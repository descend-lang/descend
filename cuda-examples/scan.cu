#include <iostream>
#include <vector>
#include <cuda_runtime.h>
#include <sstream> 


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


// The size in floats of each local block. This must be a power of 2 to work.
const int BLOCK_SIZE = 64;

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
__global__ void cuda_block_scans(float *g_odata, float *g_sums, float *g_idata) {
    __shared__ float temp[BLOCK_SIZE];

    int thid = threadIdx.x;
    int block_offset = 2 * blockIdx.x * blockDim.x;
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
             float t = temp[ai];
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
void local_scan_inplace(std::vector<float>& data) {
    float accum = 0.0;
    for (auto i = 0; i < data.size(); i++) {
        float next = data[i] + accum;
        data[i] = accum;
        accum = next;
    }
}

// Feed back the block sums into each partial.
// WARNING: This is a trivial implementation. For reasonable perf, do coalescing!
__global__ void cuda_add(float* partials, float* block_sums, int block_size) {
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
        ss << "cuda," << input_size << "," << this->block_scans_time << "," << this->total_time << std::endl;
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

    GoldCheck(const std::vector<float>& output, const std::vector<float>& gold) {
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
    std::vector<float> result;
    Timing timing;
    GoldCheck check;

    public:
    TestRun(std::vector<float>&& result, Timing timing, GoldCheck check): timing(timing), check(check) {
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

TestRun runTest(std::vector<float> input) {
    auto input_size = input.size();

    const int NUM_BLOCKS = input_size / BLOCK_SIZE;

    const int REMAINDER = input_size % BLOCK_SIZE;
    if (REMAINDER != 0) {
        std::cout << "WARNING: Input size not divisible by block size" << std::endl;
    }

    // Compute the Gold value by running a local scan
    std::vector<float> gold = input;
    local_scan_inplace(gold);


    // Allocate device memory
    float* d_input;
    float *d_output;
    float *d_block_sums;
    gpuErrchk(cudaMalloc((void **)&d_input, sizeof(float) * input_size));
    gpuErrchk(cudaMalloc((void **)&d_output, sizeof(float) * input_size));
    gpuErrchk(cudaMalloc((void **)&d_block_sums, sizeof(float) * NUM_BLOCKS));

    // Load input to GPU
    gpuErrchk(cudaMemcpy(d_input, input.data(), sizeof(float) * input_size, cudaMemcpyHostToDevice));
    
    // Execute local block scans
    cudaEvent_t cuda_block_scans_start, cuda_block_scans_end;
    gpuErrchk(cudaEventCreate(&cuda_block_scans_start));
    gpuErrchk(cudaEventCreate(&cuda_block_scans_end));

    gpuErrchk(cudaEventRecord(cuda_block_scans_start));
    cuda_block_scans<<<input_size/BLOCK_SIZE, BLOCK_SIZE/2>>>(d_output, d_block_sums, d_input);
    gpuErrchk(cudaEventRecord(cuda_block_scans_end));

    gpuErrchk(cudaDeviceSynchronize());

    // Load block sums to host, sequentially scan, re-upload
    std::vector<float> block_sums(NUM_BLOCKS);
    gpuErrchk(cudaMemcpy(block_sums.data(), d_block_sums, sizeof(float) * NUM_BLOCKS, cudaMemcpyDeviceToHost));
    local_scan_inplace(block_sums);
    gpuErrchk(cudaMemcpy(d_block_sums, block_sums.data(), sizeof(float) * NUM_BLOCKS, cudaMemcpyHostToDevice));

    // Add in the block sums
    gpuErrchk(cudaDeviceSynchronize());
    cudaEvent_t cuda_add_start, cuda_add_end;
    gpuErrchk(cudaEventCreate(&cuda_add_start));
    gpuErrchk(cudaEventCreate(&cuda_add_end));

    gpuErrchk(cudaEventRecord(cuda_add_start));
    cuda_add<<<NUM_BLOCKS, 1>>>(d_output, d_block_sums, BLOCK_SIZE);
    gpuErrchk(cudaEventRecord(cuda_add_end));
    gpuErrchk(cudaDeviceSynchronize());

    // Copy final output to device
    gpuErrchk(cudaMemcpy(input.data(), d_output, sizeof(float) * input_size, cudaMemcpyDeviceToHost));

    // Cleanup after kernel execution
    gpuErrchk(cudaFree(d_input));
    gpuErrchk(cudaFree(d_output));
    gpuErrchk(cudaFree(d_block_sums));

    // Collect timing 
    float block_scans_time;
    gpuErrchk(cudaEventElapsedTime(&block_scans_time, cuda_block_scans_start, cuda_block_scans_end));
    float add_time;
    gpuErrchk(cudaEventElapsedTime(&add_time, cuda_add_start, cuda_add_end));
    Timing timing(block_scans_time, add_time);

    // Perform gold checking
    GoldCheck gold_check(input, gold);

    // Done!
    return TestRun(std::move(input), timing, gold_check);
}

int main() {
    auto base_size = 256;
    auto run_per_size = 10;
    auto num_sizes = 64;

    std::vector<std::string> output(num_sizes);

    // For each size we have...
    for (int size_n = 0; size_n < num_sizes; size_n++) {
        // Construct input
        auto input_size = (size_n + 1) * BLOCK_SIZE * base_size;
        std::vector<float> sample_input(input_size);
        for (auto i = 0; i < input_size; i++) {
            sample_input[i] = 1.0;
        }

        std::cout << "Input Size:\t" << input_size << "\tRun number:\t" << (size_n + 1) << "/" << num_sizes << std::endl;

        // Execute each run and collect its timing
        std::vector<Timing> runs;
        for (auto i = 0; i < run_per_size; i++) {
            auto run = runTest(sample_input);
            run.notify_problems();
            runs.push_back(run.get_timing());
        }
        auto average = Timing::average(runs);
        //average.printout();
        output.push_back(average.csv_line(input_size));
    }

    // Printout results as csv to stdout
    for (const auto& line:output) {
        std::cout << line;
    }

    return 0;
}