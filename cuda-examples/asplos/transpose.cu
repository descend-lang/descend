#include <iostream>
#include <numeric>

#define BENCH
#include "descend.cuh"

__global__ void gpu_transpose(const float *in_vec, float *out_vec) {
  __shared__ float tile[1024];

  int width = gridDim.x * 32;

  for (int j = 0; j < 32; j += 8)
     tile[(threadIdx.y+j)*32+threadIdx.x] =
        in_vec[(blockIdx.y*32+threadIdx.y+j)*width + blockIdx.x*32+threadIdx.x];

  __syncthreads();

  for (int j = 0; j < 32; j += 8)
     out_vec[(blockIdx.x*32+threadIdx.y+j)*width + blockIdx.y*32+threadIdx.x] =
        tile[(threadIdx.x)*32+threadIdx.y+j];
}

template <std::size_t gs, std::size_t bsx, std::size_t bsy>
void transpose(float *harray, const std::size_t width) {
  std::size_t bytes = sizeof(float) * width*width;
  float *in_vec;
  float *out_vec; 
  CHECK_CUDA_ERR(cudaMalloc(&in_vec, bytes));
  CHECK_CUDA_ERR(cudaMalloc(&out_vec, bytes));
  CHECK_CUDA_ERR(cudaMemcpy(in_vec, harray, bytes, cudaMemcpyHostToDevice));

   // BENCHMARK
  descend::Timing timing{};
  timing.record_begin();
  gpu_transpose<<<dim3(gs, gs, 1), dim3(bsx, bsy, 1)>>>(in_vec, out_vec); 
  CHECK_CUDA_ERR( cudaDeviceSynchronize() );
  timing.record_end();
  benchmark.current_run().insert_timing(timing);

  CHECK_CUDA_ERR(cudaMemcpy(harray, out_vec, bytes, cudaMemcpyDeviceToHost));
  CHECK_CUDA_ERR(cudaFree(in_vec));
  CHECK_CUDA_ERR(cudaFree(out_vec));

}

void transpose_cpu(float *in, float *out, const std::size_t width) {
  for(std::size_t k = 0; k < width*width; k++) {
    std::size_t i = k/width;
    std::size_t j = k%width;
    out[k] = in[j*width + i];
  }
}

descend::Benchmark benchmark{descend::BenchConfig({"transpose"})};
auto main() -> int {
  static constexpr std::size_t gs[] = {256, 384, 512, 768};
  static_for<0, 3>([](auto i) {
    static constexpr auto bsx = 32;
    static constexpr auto bsy = 8;
    static constexpr std::size_t width = gs[i] * bsx;

    auto gold = new float[width * width];
    auto in_cpu = new float[width * width];
    std::iota(in_cpu, in_cpu + width*width, 1.0f);
    transpose_cpu(in_cpu, gold, width);
    delete[] in_cpu;

    auto harray = new float[width*width];
    for (std::size_t iter = 0; iter < 100; iter++) {
      std::iota(harray, harray + width*width, 1.0f);

      transpose<gs[i], bsx, bsy>(harray, width);

      for (size_t i = 0; i < width*width; i++) {
          if (harray[i] != gold[i]) {
              std::cout << "At i = " << i << std::endl << "Wrong number. Found " << harray[i] << " instead of " << gold[i]<< std::endl;
              exit(EXIT_FAILURE);
          }
      }
    }
    delete[] harray;
    delete[] gold;

    std::size_t size_in_mib = width*width * sizeof(float)/1024/1024;
    std::cout << "Input Size: " << size_in_mib << " MiB" << std::endl;
    std::cout << benchmark.to_csv();
    std::cout << "--------------" << std::endl;
    
    benchmark.reset();
  });

  exit(EXIT_SUCCESS);
}
