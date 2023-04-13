#include <algorithm>
#include <iostream>
#define BENCH
#include "descend.cuh"
/*
function declarations
*/
template <std::size_t gs, std::size_t bs>
__host__ auto inplace_vector_add(descend::i32 *const ha_array,
                                 const descend::i32 *const hb_array) -> void;
template <std::size_t gs, std::size_t bs>
__global__ auto gpu_vec_add(descend::i32 *const a_array,
                            const descend::i32 *const b_array) -> void;
/*
function definitions
*/
template <std::size_t gs, std::size_t bs>
__host__ auto inplace_vector_add(descend::i32 *const ha_array,
                                 const descend::i32 *const hb_array) -> void {
  auto gpu = descend::gpu_device(0);
  auto a_array = descend::gpu_alloc_copy<descend::array<descend::i32, gs*bs>>(
      (&gpu), (&(*ha_array)));
  const auto b_array = descend::gpu_alloc_copy<descend::array<descend::i32, gs*bs>>(
      (&gpu), (&(*hb_array)));

  // BENCHMARK
  descend::Timing timing{};
  timing.record_begin();
  gpu_vec_add<gs, bs>
      <<<dim3(gs, 1, 1), dim3(bs, 1, 1), 0>>>((&a_array), (&b_array));

  CHECK_CUDA_ERR( cudaPeekAtLastError() );
  CHECK_CUDA_ERR( cudaDeviceSynchronize() );
  timing.record_end();
  benchmark.current_run().insert_timing(timing);

  descend::copy_to_host<descend::array<descend::i32, gs*bs>>((&a_array), ha_array);
}

template <std::size_t gs, std::size_t bs>
__global__ auto gpu_vec_add(descend::i32 *const a_array,
                            const descend::i32 *const b_array) -> void {
  extern __shared__ descend::byte $buffer[];
  {
    {
      const auto a_ref =
//          (&(*a_array[(((blockIdx.x - 0) * bs) + (threadIdx.x - 0))]));
          (&(a_array[(((blockIdx.x - 0) * bs) + (threadIdx.x - 0))]));
     (*a_ref) = (*a_ref) +
//                 (*b_array[(((blockIdx.x - 0) * bs) + (threadIdx.x - 0))]);
                 (b_array[(((blockIdx.x - 0) * bs) + (threadIdx.x - 0))]);
    }
  }
}

descend::Benchmark benchmark{descend::BenchConfig({"vector-add"})};
auto main() -> int {
  static constexpr std::size_t gs[] = {1, 32, 64, 128, 256, 512, 1024, 2048};
  static_for<0, 8>([](auto i) {
    static constexpr auto bs = 1024;
    static constexpr std::size_t size = gs[i] * bs;

    auto ha_array = new descend::i32[size];
    const auto hb_array = new descend::i32[size];

    for (std::size_t iter = 0; iter < 100; iter++) {
      std::fill(ha_array, ha_array + size, 0);
      std::fill(hb_array, hb_array + size, 1);

      inplace_vector_add<gs[i], bs>(ha_array, hb_array);

      for (size_t i = 0; i < size; i++) {
          if (ha_array[i] != 1) {
              std::cout << "At i = " << i << std::endl << "Wrong number. Found " << ha_array[i] << " instead of 1.";
              exit(EXIT_FAILURE);
          }
      }
    }
    delete[] ha_array;
    delete[] hb_array;

    std::cout << "Global Size: " << gs[i] << std::endl;
    std::cout << benchmark.to_csv();
    std::cout << "--------------" << std::endl;

    benchmark.reset();
  });

  exit(EXIT_SUCCESS);
}
