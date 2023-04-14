#include <iostream>
#include <vector>
#include <cuda_runtime.h>
#include <sstream> 

#define BENCH
#include "descend.cuh"
/* General idea:
 * This file mostly implements the parallel scan presented in the NVidia guide found at
 * https://developer.nvidia.com/gpugems/gpugems3/part-vi-gpu-computing/chapter-39-parallel-prefix-sum-scan-cuda.
 * 
 * Overall, the scan algorithm has three phases:
 * 
 *  1) (on gpu) cuda_block_scans: do a parallel tree-based scan on local blocks. Also record the sum of each bloc separately
 *  2) (on host) sequentially scan the local blocks
 *  3) (on device) cuda_add: feed the scan of 2) back into the blocks.
 * 
 *  In this implementation, 2 & 3 are written by me by hand. 3) is a trivial implementation, that does not coalesce memory access
 *  This should be easy enough to do.
*/


// The size in int of each local block. This must be a power of 2 to work.
const int BLOCK_SIZE = 2048;

// Helper for checking CUDA error codes
#define gpuErrchk(ans) { gpuAssert((ans), __FILE__, __LINE__); }
inline void gpuAssert(cudaError_t code, const char *file, int line, bool abort=true)
{
   if (code != cudaSuccess) 
   {
      printf("GPUassert: %s %s %d\n", cudaGetErrorString(code), file, line);
      if (abort) exit(code);
   }
}

/**
 *  KERNELS:
 *  This section contains the various cuda kernels used in the scan program


// Implementation of local block scan.
// Precondition: g_idata contains the input of the whole scan algorithm.
// Postcondition: g_odata contains the local scans of the block, g_sums contains each block's sum.
// WARNING: This code requires a grid size of input_size/BLOCK_SIZE, and a blockDim of BLOCK_SIZE/2
*/
__global__ void cuda_block_scans(int *g_odata, int *g_sums, int *g_idata) {
    __shared__ int temp[BLOCK_SIZE];

    int thid = threadIdx.x;
    int block_offset = blockIdx.x * (2 * blockDim.x);
    int offset = 1;

    // Load input in shared memory
    temp[2 * thid] = g_idata[block_offset + 2 * thid];
    temp[2 * thid + 1] = g_idata[block_offset + 2 * thid + 1];

    // Upsweep
    for (int d = BLOCK_SIZE >> 1; d > 0; d >>= 1) {
        __syncthreads();
        if (thid < d) {
             int ai = offset*(2*thid+1)-1;     
             int bi = offset*(2*thid+2)-1;
             temp[bi] += temp[ai];
        }
        offset *= 2;
    }

    // clear the last element & record block sum
     if (thid == 0) {
         g_sums[blockIdx.x] = temp[BLOCK_SIZE-1];
         temp[BLOCK_SIZE - 1] = 0; 
    }

    // Downsweep
     for (int d = 1; d < BLOCK_SIZE; d *= 2) {
         offset >>= 1;
         __syncthreads();
         if (thid < d) {
             int ai = offset * (2 * thid + 1) - 1;
             int bi = offset * (2 * thid + 2) - 1;
             int t = temp[ai];
             temp[ai] = temp[bi];
             temp[bi] += t;
         }
     }
     __syncthreads();

     // Write out output
     g_odata[block_offset + 2 * thid] = temp[2 * thid];
     g_odata[block_offset + 2 * thid + 1] = temp[2 * thid + 1];
}

// CPU-local scan
void local_scan_inplace(std::vector<int>& data) {
    int accum = 0;
    for (auto i = 0; i < data.size(); i++) {
        int next = data[i] + accum;
        data[i] = accum;
        accum = next;
    }
}

// Feed back the block sums into each partial.
// WARNING: This is a trivial implementation. For reasonable perf, do coalescing!
__global__ void cuda_add(int* partials, int* block_sums, int block_size) {
    auto value = block_sums[blockIdx.x];
    auto chunk = partials + (block_size * blockIdx.x);

    for (auto i = 0; i < block_size; i++) {
        chunk[i] += value;
    }
}

/*** 
 *  HELPERS:
 *  This section contains a bunch of helper classes for managing the timing and checking of 
 *  gold values. This is not scan specific, just for my convenience.
 **/


class Timing {
    private:
    float block_scans_time;
    float add_time;
    float total_time;

    public:
    Timing(float block_scans_time, float add_time) {
        this->block_scans_time = block_scans_time;
        this->add_time = add_time;
        this->total_time = this->block_scans_time + this->add_time;
    }

    void printout() const {
        std::cout << "Timing Report:" << std::endl;
        std::cout << "Block Scans:\t" << block_scans_time << std::endl;
        std::cout << "Add Value:\t" << add_time << std::endl;
        std::cout << "Total:\t\t" << total_time << std::endl;
    }

    std::string csv_line(int input_size) const {
        std::stringstream ss;
        ss << "cuda," << input_size << "," << this->block_scans_time << "," << this->add_time << ","
            << this->total_time << std::endl;
        return ss.str();
    }

    static Timing average(const std::vector<Timing>& runs) {
        float block_sums_time = 0.0;
        float add_time = 0.0;
        
        for (const auto& run:runs) {
            block_sums_time += run.block_scans_time;
            add_time += run.add_time;
        }

        block_sums_time = block_sums_time / runs.size();
        add_time = add_time / runs.size();

        return Timing(block_sums_time, add_time);
    }
};

struct GoldCheck {
    private:
    bool ok;
    int err_no;
    
    public:

    GoldCheck(const std::vector<int>& output, const std::vector<int>& gold) {
        auto gold_check = true;
        int err_count = 0;
        for (int i = 0; i < output.size(); i++) {
            if (output[i] != gold[i]) {
                gold_check = gold_check && false;
                err_count++;
            }
        }
        this->ok = gold_check;
        this->err_no = err_count;
    }

    void printout() const {
        std::cout << "Gold Check:\t";
        if (this->ok) {
            std::cout << "Yes";
        } else {
            std::cout << "No.\tErrors:\t" << this->err_no;
        }
        std::cout << std::endl;
    }

    void notify_problems() const {
        if (!this->ok) {
            std::cerr << "WARNING! Gold check failed with " << this->err_no << " errors!" << std::endl;
        }
    }
};

class TestRun {
    private:
    std::vector<int> result;
    Timing timing;
    GoldCheck check;

    public:
    TestRun(std::vector<int>&& result, Timing timing, GoldCheck check): timing(timing), check(check) {
        this->result = result;    
    }

    const Timing get_timing() {
        return this->timing;
    }

    void printout() const {
        this->timing.printout();
        this->check.printout();
    }

    void notify_problems() const {
        this->check.notify_problems();
    }
};

/*
 * SCAN:
 * The runTest function implements the whole scan. 
 * 
 */

TestRun runTest(std::vector<int> input) {
    auto input_size = input.size();

    const int NUM_BLOCKS = input_size / BLOCK_SIZE;

    const int REMAINDER = input_size % BLOCK_SIZE;
    if (REMAINDER != 0) {
        std::cout << "WARNING: Input size not divisible by block size" << std::endl;
    }

    // Compute the Gold value by running a local scan
    std::vector<int> gold = input;
    local_scan_inplace(gold);

    // Load block sums to host, sequentially scan, re-upload
    std::vector<int> block_sums(NUM_BLOCKS);

    // Allocate device memory
    int* d_input;
    int *d_output;
    int *d_block_sums;
    gpuErrchk(cudaMalloc((void **)&d_input, sizeof(int) * input_size));
    gpuErrchk(cudaMalloc((void **)&d_output, sizeof(int) * input_size));
    gpuErrchk(cudaMalloc((void **)&d_block_sums, sizeof(int) * NUM_BLOCKS));

    // Load input to GPU
    gpuErrchk(cudaMemcpy(d_input, input.data(), sizeof(int) * input_size, cudaMemcpyHostToDevice));
    
    // Execute local block scans
    cudaEvent_t cuda_block_scans_start, cuda_block_scans_end;
    gpuErrchk(cudaEventCreate(&cuda_block_scans_start));
    gpuErrchk(cudaEventCreate(&cuda_block_scans_end));

    // BENCHMARK
    {
      descend::Timing timing{};
      timing.record_begin();
      cuda_block_scans<<<input_size/BLOCK_SIZE, BLOCK_SIZE/2>>>(d_output, d_block_sums, d_input);
      CHECK_CUDA_ERR( cudaDeviceSynchronize() );
      timing.record_end();
      benchmark.current_run().insert_timing(timing);
    }
    
    gpuErrchk(cudaMemcpy(block_sums.data(), d_block_sums, sizeof(int) * NUM_BLOCKS, cudaMemcpyDeviceToHost));

    local_scan_inplace(block_sums);

    gpuErrchk(cudaMemcpy(d_block_sums, block_sums.data(), sizeof(int) * NUM_BLOCKS, cudaMemcpyHostToDevice));
    // BENCHMARK
    {
      descend::Timing timing{};
      timing.record_begin();
      cuda_add<<<NUM_BLOCKS, 1>>>(d_output, d_block_sums, BLOCK_SIZE);
      CHECK_CUDA_ERR( cudaDeviceSynchronize() );
      timing.record_end();
      benchmark.current_run().insert_timing(timing);
    }

    // Copy final output to device
    gpuErrchk(cudaMemcpy(input.data(), d_output, sizeof(int) * input_size, cudaMemcpyDeviceToHost));

    // Cleanup after kernel execution
    gpuErrchk(cudaFree(d_input));
    gpuErrchk(cudaFree(d_output));
    gpuErrchk(cudaFree(d_block_sums));

    // Perform gold checking
    GoldCheck gold_check(input, gold);

    // Done!
    return TestRun(std::move(input), Timing{0.0, 0.0}, gold_check);
}

descend::Benchmark benchmark{descend::BenchConfig({"scan", "add"})};
int main() {
    static constexpr std::size_t grid_size[] = {16384, 32768, 65536};
    static constexpr std::size_t run_per_size = 100;

    // Construct input
    static_for<0, 3>([](auto i) {
      auto input_size = BLOCK_SIZE * grid_size[i];
      std::vector<int> sample_input(input_size);
      for (auto i = 0; i < input_size; i++) {
          sample_input[i] = i%32;
      }

      for (auto i = 0; i < run_per_size; i++) {
          auto run = runTest(sample_input);
          run.notify_problems();
      }

      std::size_t size_in_mib = input_size * sizeof(int)/1024/1024;
      std::size_t footprint_in_mib = size_in_mib * 2;
      float block_sum_size_in_mib = (float)(input_size/(BLOCK_SIZE)) * sizeof(descend::i32)/1024/1024;
      std::cout << "Input Size: " << size_in_mib << " MiB" << std::endl;
      std::cout << "Footprint: " << footprint_in_mib << " MiB" << std::endl;
      std::cout << "+ Block Sum size in MiB: " << block_sum_size_in_mib << " MiB" << std::endl;
      std::cout << benchmark.to_csv();
      std::cout << "--------------" << std::endl;
      
      benchmark.reset();

    });

    return 0;
}
