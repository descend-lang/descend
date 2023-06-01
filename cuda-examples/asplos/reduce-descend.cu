#include <iostream>
#include <algorithm>

#define BENCH
#include "descend.cuh"
/*
function declarations
*/
template <std::size_t gs, std::size_t bs>
__global__ auto gpu_reduce(descend::i32 *const input) -> void;
/*
function definitions
*/
template <std::size_t gs, std::size_t bs>
__host__ auto reduce(descend::i32 * ha_array) -> void {
  auto gpu = descend::gpu_device(0);
  auto a_array =
      descend::gpu_alloc_copy<descend::array<descend::i32, (gs * bs)>>(
          (&gpu), (&(*ha_array)));

   // BENCHMARK
  descend::Timing timing{};
  timing.record_begin();
  gpu_reduce<gs, bs><<<dim3(gs, 1, 1), dim3(bs, 1, 1), 0>>>((&a_array));
  CHECK_CUDA_ERR( cudaPeekAtLastError() );
  CHECK_CUDA_ERR( cudaDeviceSynchronize() );
  timing.record_end();
  benchmark.current_run().insert_timing(timing);

  descend::copy_to_host<descend::array<descend::i32, (gs * bs)>>((&a_array),
                                                                 ha_array);
}

template <std::size_t gs, std::size_t bs>
__global__ auto gpu_reduce(descend::i32 *const input) -> void {
  extern __shared__ descend::byte $buffer[];
  {
    const auto ib = (&(input[((blockIdx.x - 0) * bs)]));
    for (std::size_t k = (bs / 2); k > 0; k = k / 2) {

      if ((threadIdx.x - 0) < k) {
        {
          const auto fst_half = (&(ib[(threadIdx.x - 0)]));
          const auto snd_half = (&(ib[((threadIdx.x - 0) + k)]));
          (*fst_half) = (*fst_half) + (*snd_half);
        }
      } else {
      }

      __syncthreads();
    }
  }
}

descend::Benchmark benchmark{descend::BenchConfig({"tree-reduce"})};
auto main() -> int {
  static constexpr std::size_t gs[] = {65536, 131072, 262144, 524288};
  static constexpr auto bs = 1024;

  static_for<0, 4>([](auto i) {
    auto ha_array = new descend::i32[gs[i]*bs];

    for (std::size_t iter = 0; iter < 100; iter++) {
      std::fill(ha_array, ha_array + gs[i]*bs, 1);

      reduce<gs[i],bs>(ha_array);

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
