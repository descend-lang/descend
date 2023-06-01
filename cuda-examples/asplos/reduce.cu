#include <iostream>
#include <algorithm>

#define BENCH
#include "descend.cuh"

template <std::size_t bs>
__global__ auto gpu_reduce(int *const array) -> void {
  for (std::size_t k = bs/2; k > 0; k = k / 2) {
    if (threadIdx.x < k) {
      array[blockIdx.x * bs + threadIdx.x] =
                        array[blockIdx.x * bs + threadIdx.x] +
                        array[blockIdx.x * bs + threadIdx.x + k];
    }
    __syncthreads();
  }
}

template <std::size_t gs, std::size_t bs>
auto reduce(int *ha_array) -> void {
  std::size_t bytes = sizeof(int) * gs * bs;
  int *a_array;
  CHECK_CUDA_ERR(cudaMalloc(&a_array, bytes));
  CHECK_CUDA_ERR(cudaMemcpy(a_array, ha_array, bytes, cudaMemcpyHostToDevice));

   // BENCHMARK
  descend::Timing timing{};
  timing.record_begin();
  gpu_reduce<bs><<<gs, bs>>>(a_array); 
  CHECK_CUDA_ERR( cudaPeekAtLastError() );
  CHECK_CUDA_ERR( cudaDeviceSynchronize() );
  timing.record_end();
  benchmark.current_run().insert_timing(timing);

  CHECK_CUDA_ERR(cudaMemcpy(ha_array, a_array, bytes, cudaMemcpyDeviceToHost));
  CHECK_CUDA_ERR(cudaFree(a_array));
}

descend::Benchmark benchmark{descend::BenchConfig({"tree-reduce"})};
auto main() -> int {
  static constexpr std::size_t gs[] = {65536, 131072, 262144, 524288};
  static constexpr auto bs = 1024;

  static_for<0, 4>([](auto i) {
    auto ha_array = new int[gs[i] * bs];

    for (std::size_t iter = 0; iter < 100; iter++) {
      std::fill(ha_array, ha_array + gs[i]*bs, 1);

      reduce<gs[i], bs>(ha_array);

      for (std::size_t block_num = 0; block_num < gs[i]; block_num++) {
        if (ha_array[block_num * bs] != bs) {
          std::cout << "At " << block_num * bs << ": Wrong number. Found " << ha_array[0] << " instead of " << bs << std::endl;
          exit(EXIT_FAILURE);
        }
      }
    }
    delete[] ha_array;

    std::size_t size_in_mb = gs[i] * bs * sizeof(int) / 1024 / 1024; 
    std::cout << "Input Size: " << size_in_mb << "MiB" << std::endl;
    std::cout << benchmark.to_csv();
    std::cout << "--------------" << std::endl;
    
    benchmark.reset();

  });


    exit(EXIT_SUCCESS);
}
