#include <iostream>
#include <numeric>
#include <cstdlib>

#define BENCH
#include "../descend.cuh"
/*
function declarations
*/
template <std::size_t m, std::size_t n, std::size_t k>
__host__ auto sgemm(const descend::i32 *const a_transp_mat_h,
                    const descend::i32 *const b_mat_h,
                    const descend::i32 *const c_mat_h,
                    descend::i32 *const out_mat_h) -> void;
template <std::size_t m, std::size_t n, std::size_t k>
__global__ auto sgemm_gpu(const descend::i32 *const a_transp_mat,
                          const descend::i32 *const b_mat,
                          const descend::i32 *const c_mat,
                          descend::i32 *const out_mat, const descend::i32 alpha,
                          const descend::i32 beta) -> void;
/*
function definitions
*/

template <std::size_t m, std::size_t n, std::size_t k>
__host__ auto sgemm(const descend::i32 *const a_transp_mat_h,
                    const descend::i32 *const b_mat_h,
                    const descend::i32 *const c_mat_h,
                    descend::i32 *const out_mat_h) -> void {
    auto gpu = descend::gpu_device(0);
    // FIXME manually adjusted template param arguments to be one dimensional array types
    const auto a_transp_mat = descend::gpu_alloc_copy<
            descend::array<descend::i32, m * k>>((&gpu), (&(*a_transp_mat_h)));
    const auto b_mat = descend::gpu_alloc_copy<
            descend::array<descend::i32, n * k>>((&gpu), (&(*b_mat_h)));
    const auto c_mat = descend::gpu_alloc_copy<
            descend::array<descend::i32, n * m>>((&gpu), (&(*c_mat_h)));
    auto out_mat = descend::gpu_alloc_copy<
            descend::array<descend::i32, n * m>>((&gpu),
                                                                (&(*out_mat_h)));

    // BENCHMARK
    descend::Timing timing{};
    timing.record_begin();
    sgemm_gpu<m, n, k><<<dim3(8, 16, 1), dim3(32, 8, 1),
    ((0 + (4 * ((1 * (32 * 2)) * 8))) + (4 * ((1 * (32 * 4)) * 8)))>>>(
            (&a_transp_mat), (&b_mat), (&c_mat), (&out_mat), 1, 1);
    timing.record_end();
    benchmark.current_run().insert_timing(timing);

    descend::copy_to_host<descend::array<descend::array<descend::i32, n>, m>>(
            (&out_mat), out_mat_h);
}

template <std::size_t m, std::size_t n, std::size_t k>
__global__ auto sgemm_gpu(const descend::i32 *const a_transp_mat,
                          const descend::i32 *const b_mat,
                          const descend::i32 *const c_mat,
                          descend::i32 *const out_mat, const descend::i32 alpha,
                          const descend::i32 beta) -> void {
  extern __shared__ descend::byte $buffer[];
  descend::i32 *const a_tile = (descend::i32 *)((&$buffer[0]));
  descend::i32 *const b_tile =
      (descend::i32 *)((&a_tile[((1 * (32 * 2)) * 8)]));
  {
    {
      {
        {
          for (std::size_t wgY = 0; wgY < (m/ (64 * 16)); wgY = wgY + 1) {
            for(std::size_t wgX = 0; wgX < (n/(128 * 8)); wgX = wgX + 1) {
              auto accum = descend::create_array<32, descend::i32>(0);

              for(std::size_t tnum = 0; tnum < (k/8); tnum = tnum + 1) {
                for(std::size_t i = 0; i < 2; i = i + 1) {
                  a_tile[(((threadIdx.y - 0) * (32 * 2)) +
                          ((i * 32) + (threadIdx.x - 0)))] =
                      a_transp_mat[((((tnum * 8) + (threadIdx.y - 0)) * m) +
                                    ((((wgY * 16) + (blockIdx.y - 0)) * 64) +
                                     ((i * 32) + (threadIdx.x - 0))))];
                }

                for(std::size_t i = 0; i < 4; i = i + 1) {
                  b_tile[(((threadIdx.y - 0) * (32 * 4)) +
                          ((i * 32) + (threadIdx.x - 0)))] =
                      b_mat[((((tnum * 8) + (threadIdx.y - 0)) * n) +
                             ((((wgX * 8) + (blockIdx.x - 0)) * 128) +
                              ((i * 32) + (threadIdx.x - 0))))];
                }
                // FIXME added manually.
                //  Should be enforced in Descend but is not. Also adding it leads to weired borrowing conflict.
                __syncthreads();

                for(std::size_t i = 0; i < 8; i = i + 1) {
                  auto a_tile_regs =
                      descend::create_array<8, descend::i32>(0);
                  for(std::size_t j = 0; j < 8; j = j + 1) {
                    a_tile_regs[j] = a_tile[((i * (32 * 2)) +
                                             (((threadIdx.y - 0) * 8) + j))];
                  }

                  auto b_tile_regs =
                      descend::create_array<4, descend::i32>(0);
                  for(std::size_t j = 0; j < 4; j = j + 1) {
                    b_tile_regs[j] = b_tile[((i * (32 * 4)) +
                                             ((j * 32) + (threadIdx.x - 0)))];
                  }

                  for(std::size_t j1 = 0; j1 < 8; j1 = j1 + 1) {
                    for(std::size_t j2 = 0; j2 < 4; j2 = j2 + 1) {
                      accum[((j1 * 4) + j2)] =
                          (accum[((j1 * 4) + j2)] +
                           (a_tile_regs[j1] * b_tile_regs[j2]));
                    }
                  }
                }

                __syncthreads();
              }

              for(std::size_t i = 0; i < 8; i = i + 1) {
                for(std::size_t j = 0; j < 4; j = j + 1) {
                  out_mat[((((((wgY * 16) + (blockIdx.y - 0)) * 64) +
                             (((threadIdx.y - 0) * 8) + i)) *
                            n) +
                           ((((wgX * 8) + (blockIdx.x - 0)) * 128) +
                            ((j * 32) + (threadIdx.x - 0))))] =
                      ((accum[((i * 4) + j)] * alpha) +
                       (c_mat[((((((wgY * 16) + (blockIdx.y - 0)) * 64) +
                                 (((threadIdx.y - 0) * 8) + i)) *
                                n) +
                               ((((wgX * 8) + (blockIdx.x - 0)) * 128) +
                                ((j * 32) + (threadIdx.x - 0))))] *
                        beta));
                }
              }
            }
          }
        }
      }
    }
  }
}

template<std::size_t m, std::size_t n, std::size_t k>
auto cpu_sgemm(
        descend::i32 * const hout_mat,
        descend::i32 const * const ha_mat_transp, // [[i32; m]; k]
        descend::i32 const * const hb_mat, // [[i32; n]; k]
        descend::i32 const * const hc_mat, // [[i32; n]; m]
        descend::i32 alpha, descend::i32 beta) {
    for (int j = 0; j < k; ++j) {
        for (int i = 0; i < m; ++i)
          for (int l = 0; l < n; ++l)
              hout_mat[i * n + l] += ha_mat_transp[j * m + i] * hb_mat[j * n + l];
    }

    for (int i = 0; i < m; ++i)
      for (int l = 0; l < n; ++l)
          hout_mat[i*n + l] = alpha * hout_mat[i*n+l] + beta * hc_mat[i*n + l];
}

descend::Benchmark benchmark{descend::BenchConfig({"sgemm"})};
auto main() -> int {
    static constexpr std::size_t m[] = {8192, 8192, 16384};
    static constexpr auto n = 8192;
    static constexpr std::size_t k[] = {4096, 8192, 8192};

    static_for<0, 3>([](auto i) {
        const auto ha_mat_transp = new descend::i32[k[i]*m[i]];
        const auto hb_mat = new descend::i32[k[i]*n];
        const auto hc_mat = new descend::i32[m[i]*n];
        auto hout_mat = new descend::i32[m[i]*n];
        std::fill(ha_mat_transp, ha_mat_transp + k[i]*m[i], 1);
        std::fill(hb_mat, hb_mat + k[i]*n, 1);
        std::fill(hc_mat, hc_mat + m[i]*n, 1);

        std::cout << "Footprint: " << (k[i]*m[i] + k[i]*n + 2*m[i]*n)*sizeof(int)/1024/1024 << " MiB" << std::endl;
        auto gold = new descend::i32[m[i]*n];
        std::cout << "Compute gold..." << std::endl;
        cpu_sgemm<m[i], n, k[i]>(gold, ha_mat_transp, hb_mat, hc_mat, 1, 1);
        std::cout << "Gold computed. Starting measurement ..." << std::endl;

        for (std::size_t iter = 0; iter < 100; iter++) {
            std::fill(hout_mat, hout_mat + m[i]*n, 0);

            sgemm<m[i], n, k[i]>(ha_mat_transp, hb_mat, hc_mat, hout_mat);

            for (size_t j = 0; j < m[i]*n; j++) {
                if (gold[j] != hout_mat[j]) {
                    std::cout << "Error at " << j << ". Expected: " << gold[j] << " but found " << hout_mat[j] << "." << std::endl;
                    exit(EXIT_FAILURE);
                }
            }
        }
        delete[] gold;
        delete[] ha_mat_transp;
        delete[] hb_mat;
        delete[] hc_mat;
        delete[] hout_mat;

        std::cout << "Input sizes: m =" << m[i] << ", n = " << n << ", k = " << k[i] << std::endl;
        std::cout << benchmark.to_csv();

        benchmark.reset();
    });

    exit(EXIT_SUCCESS);
}
