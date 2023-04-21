#include <iostream>
#include <numeric>
#include <cstdlib>

#define BENCH
#include "descend.cuh"

template <std::size_t m, std::size_t n, std::size_t k>
__global__ auto gpu_matmul(const descend::i32 *const a_mat,
                           const descend::i32 *const b_mat,
                           descend::i32 *const c_mat) -> void {
  std::size_t gidy = blockIdx.y * blockDim.y + threadIdx.y;
  std::size_t gidx = blockIdx.x * blockDim.x + threadIdx.x;

  auto sum = 0;
  for (std::size_t i = 0; i < n; i++) {
    sum += a_mat[gidy*n + i] * b_mat[(i*k) + gidx];
  }
  c_mat[gidy*k + gidx] = sum;
}

template <std::size_t m, std::size_t n, std::size_t k, std::size_t bs>
auto matmul(const descend::i32 *const ha_mat,
            const descend::i32 *const hb_mat,
            descend::i32 *const hc_mat) -> void {
  int *a_mat;
  int *b_mat;
  int *c_mat;
  
  std::size_t a_bytes = sizeof(int) * m*n;
  std::size_t b_bytes = sizeof(int) * n*k;
  std::size_t c_bytes = sizeof(int) * m*k;
  CHECK_CUDA_ERR(cudaMalloc(&a_mat, a_bytes));
  CHECK_CUDA_ERR(cudaMalloc(&b_mat, b_bytes));
  CHECK_CUDA_ERR(cudaMalloc(&c_mat, c_bytes));
  CHECK_CUDA_ERR(cudaMemcpy(a_mat, ha_mat, a_bytes, cudaMemcpyHostToDevice));
  CHECK_CUDA_ERR(cudaMemcpy(b_mat, hb_mat, b_bytes, cudaMemcpyHostToDevice));

   // BENCHMARK
  descend::Timing timing{};
  timing.record_begin();
  gpu_matmul<m, n, k><<<dim3((k / bs), (m / bs), 1), dim3(bs, bs, 1)>>>(a_mat, b_mat, c_mat); 
  CHECK_CUDA_ERR( cudaDeviceSynchronize() );
  timing.record_end();
  benchmark.current_run().insert_timing(timing);

  CHECK_CUDA_ERR(cudaMemcpy(hc_mat, c_mat, c_bytes, cudaMemcpyDeviceToHost));
  CHECK_CUDA_ERR(cudaFree(c_mat));
  CHECK_CUDA_ERR(cudaFree(b_mat));
  CHECK_CUDA_ERR(cudaFree(a_mat));
}


template<std::size_t m, std::size_t n, std::size_t k>
auto cpu_matmul(descend::i32 * const hc_mat, descend::i32 const * const ha_mat, descend::i32 const * const hb_mat) {
  for (int i = 0; i < m; ++i)
    for (int j = 0; j < k; ++j)
      for (int l = 0; l < n; ++l)
          hc_mat[i*k + j] += ha_mat[i*n + l] * hb_mat[l*k + j];
}

descend::Benchmark benchmark{descend::BenchConfig({"matmul"})};
auto main() -> int {
    static constexpr auto bs = 16;
    static constexpr std::size_t m[] = {8192, 8192, 16384};
    static constexpr auto n = 8192;
    static constexpr std::size_t k[] = {4096, 8192, 8192};

    static_for<0, 1>([](auto i) {
        const auto ha_mat = new descend::i32[m[i]*n];
        const auto hb_mat = new descend::i32[n*k[i]];
        auto hc_mat = new descend::i32[m[i]*k[i]];
        std::fill(ha_mat, ha_mat + m[i]*n, 1);
        std::fill(hb_mat, hb_mat + n*k[i], 1);

        std::cout << "Footprint: " << (m[i]*n + n*k[i] + m[i]*k[i])*sizeof(int)/1024/1024 << " MiB" << std::endl;
        auto gold = new descend::i32[m[i]*k[i]];
        std::cout << "Compute gold..." << std::endl;
        cpu_matmul<m[i], n, k[i]>(gold, ha_mat, hb_mat);
        std::cout << "Gold computed. Starting measurement ..." << std::endl;

        for (std::size_t iter = 0; iter < 100; iter++) {
            std::fill(ha_mat, ha_mat + m[i]*n, 1);
            std::fill(hb_mat, hb_mat + n*k[i], 1);
            std::fill(hc_mat, hc_mat + m[i]*k[i], 0);

            matmul<m[i], n, k[i], bs>(ha_mat, hb_mat, hc_mat);

            for (size_t j = 0; j < m[i]*k[i]; j++) {
                if (gold[j] != hc_mat[j]) {
                    std::cout << "Error at " << j << ". Expected: " << gold[j] << " but found " << hc_mat[j] << "." << std::endl;
                    exit(EXIT_FAILURE);
                }
            }
        }
        delete[] gold;
        delete[] ha_mat;
        delete[] hb_mat;
        delete[] hc_mat;

        std::cout << "Input sizes: m =" << m[i] << ", n = " << n << ", k = " << k[i] << std::endl;
        std::cout << benchmark.to_csv();

        benchmark.reset();
    });

    exit(EXIT_SUCCESS);
}
