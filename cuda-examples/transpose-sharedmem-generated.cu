#include <iostream>
#include <algorithm>

#define BENCH
#include "descend.cuh"
/*
function declarations
*/
template <std::size_t n>
__host__ auto transpose(descend::array<descend::f64, 2048> *const h_vec)
    -> void;
__global__ auto
par_transpose(const descend::array<descend::f64, n> *const in_vec,
              descend::array<descend::f64, 2048> *const out_vec) -> void;
/*
function definitions
*/
template <std::size_t n>
__host__ auto transpose(descend::array<descend::f64, 2048> *const h_vec)
    -> void {
  auto gpu = descend::gpu_device(0);
  const auto d_vec = descend::gpu_alloc_copy<
      descend::array<descend::array<descend::f64, 2048>, 2048>>((&gpu),
                                                                (&(*h_vec)));
  auto d_vec_out = descend::gpu_alloc_copy<
      descend::array<descend::array<descend::f64, 2048>, 2048>>((&gpu),
                                                                (&(*h_vec)));
  par_transpose<<<dim3(64, 64, 1), dim3(32, 8, 1),
                  (0 + (8 * ((1 * 32) * 32)))>>>((&d_vec), (&d_vec_out));
  descend::copy_to_host<
      descend::array<descend::array<descend::f64, 2048>, 2048>>((&d_vec_out),
                                                                h_vec);
}

__global__ auto
par_transpose(const descend::array<descend::f64, n> *const in_vec,
              descend::array<descend::f64, 2048> *const out_vec) -> void {
  extern __shared__ descend::byte $buffer[];
  descend::f64 *const tmp = (descend::f64 *)(&$buffer[0]);
  {
    {
      const auto block_tile = (&(*in_vec[((blockIdx.x - 0) * 32)]));
      const auto out_block_tile = (&(*out_vec[((blockIdx.y - 0) * 32)]));
      {
        {
          for (std::size_t i = 0; i < 4; i = i + 1) {
            const auto tmp_tile =
                (&(*tmp[((i * 8) + (threadIdx.y - 0))][(threadIdx.x - 0)]));
            (*tmp_tile) =
                (*block_tile[((i * 8) + (threadIdx.y - 0))][(threadIdx.x - 0)]);
          }

          __syncthreads();
          for (std::size_t i = 0; i < 4; i = i + 1) {
            const auto tmp_tile =
                (&(*tmp[((i * 8) + (threadIdx.y - 0))][(threadIdx.x - 0)]));
            (*out_block_tile[(((threadIdx.y - 0) * 8) + i)]
                            [(threadIdx.x - 0)]) = (*tmp_tile);
          }
        }
      }
    }
  }
}

descend::Benchmark benchmark{descend::BenchConfig({"transpose"})};
auto main() -> int {
  static constexpr std::size_t gs[] = {1, 32, 64, 128, 256, 512, 1024, 2048};
  static_for<0, 8>([](auto i) {
    static constexpr auto bs = 1024;
    static constexpr std::size_t size = gs[i] * bs;

    auto hin_vec = new descend::i32[size];
    const auto hout_vec = new descend::i32[size];

    for (std::size_t iter = 0; iter < 100; iter++) {
      std::fill(hin_vec, hin_vec + size, 1);

      transpose<gs[i], bs>(hin_vec, hout_vec);

      for (size_t i = 0; i < size; i++) {
          if (hout_vec[i] != 1) {
              std::cout << "At i = " << i << std::endl << "Wrong number. Found " << hout_vec[i] << " instead of 1.";
              exit(EXIT_FAILURE);
          }
      }
    }
    delete[] hin_vec;
    delete[] hout_vec;

    std::cout << "Global Size: " << gs[i] << std::endl;
    std::cout << benchmark.to_csv();
    std::cout << "--------------" << std::endl;
    
    benchmark.reset();
  });

  exit(EXIT_SUCCESS);
}
