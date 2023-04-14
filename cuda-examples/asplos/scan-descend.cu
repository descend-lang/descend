#include <iostream>
#include <numeric>

#define BENCH

#include "descend.cuh"
/*
function declarations
*/
template <std::size_t m>
__host__ auto scan_inplace(descend::i32 *const data) -> void;
template <std::size_t n, std::size_t gs, std::size_t bs>
__global__ auto par_scan(const descend::i32 *const input,
                         descend::i32 *const output,
                         descend::i32 *const block_sums) -> void;
template <std::size_t n, std::size_t gs>
__global__ auto add(descend::i32 *const input,
                    const descend::i32 *const block_sums) -> void;
template <std::size_t n, std::size_t gs, std::size_t bs>
__host__ auto scan(const descend::i32 *const ha_array,
                   descend::i32 *const h_output,
                   descend::i32 *const h_block_sums) -> void;
/*
function definitions
*/
template <std::size_t m>
__host__ auto scan_inplace(descend::i32 *const data) -> void {
  auto accum = 0;
  // FIXME manually implemented because generating for-loop is broken
  for(std::size_t i = 0; i < m; i++) {
    descend::i32 next = data[i] + accum;
    data[i] = accum;
    accum = next;
  }
}

template <std::size_t n, std::size_t gs, std::size_t bs>
__global__ auto par_scan(const descend::i32 *const input,
                         descend::i32 *const output,
                         descend::i32 *const block_sums) -> void {
  extern __shared__ descend::byte $buffer[];
  descend::i32 *const tmp = (descend::i32 *)(&$buffer[0]);

  {
    const auto ib = (&(input[((blockIdx.x - 0) * (bs * 2))]));
    const auto block_out = (&(output[((blockIdx.x - 0) * (bs * 2))]));
    const auto bsum = (&(block_sums[((blockIdx.x - 0) * 1)]));
    {

      {
        (tmp[(threadIdx.x - 0)]) = (ib[(threadIdx.x - 0)]);
        (tmp[((threadIdx.x - 0) + bs)]) = (ib[((threadIdx.x - 0) + bs)]);
      }
    }

    for (std::size_t dd = bs; dd > 0; dd = dd / 2) {
      __syncthreads();

      if ((threadIdx.x - 0) < dd) {
        const auto arr = (&(tmp[((threadIdx.x - 0) * ((bs * 2) / dd))]));
        (arr[(((bs * 2) / dd) - 1)]) =
            (arr[(((bs * 2) / dd) - 1)]) + (arr[((bs / dd) - 1)]);
      } else {
      }
    }

    {
      if ((threadIdx.x - 0) < 1) {
        (bsum[(threadIdx.x - 0)]) =
            (tmp[((threadIdx.x - 0) + ((bs * 2) - 1))]);
        (tmp[((threadIdx.x - 0) + ((bs * 2) - 1))]) = 0.0f;
      } else {
      }
    }

    for (std::size_t dd = 1; dd <= bs; dd = dd * 2) {
      __syncthreads();

      if ((threadIdx.x - 0) < dd) {
        const auto arr = (&(tmp[((threadIdx.x - 0) * ((bs * 2) / dd))]));
        const auto t = (arr[((bs / dd) - 1)]);
        (arr[((bs / dd) - 1)]) = (arr[(((bs * 2) / dd) - 1)]);
        (arr[(((bs * 2) / dd) - 1)]) = (arr[(((bs * 2) / dd) - 1)]) + t;
      } else {
      }
    }

    __syncthreads();
    {

      {
        (block_out[(threadIdx.x - 0)]) = (tmp[(threadIdx.x - 0)]);
        (block_out[((threadIdx.x - 0) + bs)]) =
            (tmp[((threadIdx.x - 0) + bs)]);
      }
    }
  }
}

template <std::size_t n, std::size_t gs, std::size_t bs>
__global__ auto add(descend::i32 *const input,
                    const descend::i32 *const block_sums) -> void {
  extern __shared__ descend::byte $buffer[];
  {
    const auto value_grp = (&(block_sums[((blockIdx.x - 0) * 1)]));
    const auto chunk_grp = (&(input[((blockIdx.x - 0) * (2*bs))]));
    {
      const auto chunk = (&(chunk_grp[((threadIdx.x - 0) * (2*bs))]));
      for (std::size_t i = 0; i < 2*bs; i++) {
        const auto cc = chunk[i] + value_grp[threadIdx.x];
        chunk[i] = cc;
      }
    }
  }
}

template <std::size_t n, std::size_t gs, std::size_t bs>
__host__ auto scan(const descend::i32 *const ha_array,
                   descend::i32 *const h_output,
                   descend::i32 *const h_block_sums) -> void {
  auto gpu = descend::gpu_device(0);
  const auto a_array = descend::gpu_alloc_copy<descend::array<descend::i32, n>>(
      (&gpu), ha_array);
  auto out_array = descend::gpu_alloc_copy<descend::array<descend::i32, n>>(
      (&gpu), (&(*h_output)));
  auto block_sums =
      descend::gpu_alloc_copy<descend::array<descend::i32, (n / (bs * 2))>>(
          (&gpu), (&(*h_block_sums)));
  // BENCHMARK
  {
    descend::Timing timing{};
    timing.record_begin();
    par_scan<n, gs, bs>
        <<<dim3(gs, 1, 1), dim3(bs, 1, 1), (0 + (4 * (1 * (bs * 2))))>>>(
            (&a_array), (&out_array), (&block_sums));
    CHECK_CUDA_ERR( cudaDeviceSynchronize() );
    timing.record_end();
    benchmark.current_run().insert_timing(timing);
  }

  descend::copy_to_host<descend::array<descend::i32, (n / (bs * 2))>>(
      (&block_sums), (&(*h_block_sums)));
  scan_inplace<gs>((&(*h_block_sums)));
  descend::copy_to_gpu<descend::array<descend::i32, (n / (bs * 2))>>(
      (&block_sums), (&(*h_block_sums)));

  // BENCHMARK
  {
    descend::Timing timing{};
    timing.record_begin();
    add<n, (n / (2 * bs)), bs><<<dim3((n / (2 * bs)), 1, 1), dim3(1, 1, 1), 0>>>(
        (&out_array), (&block_sums));
    CHECK_CUDA_ERR( cudaDeviceSynchronize() );
    timing.record_end();
    benchmark.current_run().insert_timing(timing);
  }

  descend::copy_to_host<descend::array<descend::i32, n>>((&out_array),
                                                         (&(*h_output)));
}

descend::Benchmark benchmark{descend::BenchConfig({"scan", "add"})};
auto main() -> int {
  static constexpr std::size_t gs[] = {16384, 32768, 65536};//, 131072, 262144, 524288};
  static constexpr auto bs = 1024;

  static_for<0, 3>([](auto i) {
    static constexpr auto N = gs[i]*bs*2;

    auto ha_array = new descend::i32[N];
    auto h_output = new descend::i32[N];
    auto h_block_sums = new descend::i32[N/(bs*2)];
    auto gold = new descend::i32[N];
    for (size_t j =0; j< N; j++) {
        ha_array[j] = j%bs;
        gold[j] = j%bs;
    }
    scan_inplace<N>(gold);

    for (std::size_t iter = 0; iter < 100; iter++) {
      std::fill(h_output, h_output + N, 0);
      std::fill(h_block_sums, h_block_sums + (N/(bs*2)), 0);
      // Run scan
      scan<N, gs[i], bs>(ha_array, h_output, h_block_sums);
      for (int j = 0; j < N; j++) {
          if (h_output[j] != gold[j]) {
              std::cout << "Error at " << j << ": Expected `" << gold[j]
                        << "` but found `" << h_output[i] << "`" << std::endl;
              std::cout << "While input at " << j << ": " << ha_array[j] << std::endl;
              std::cout << "Next 10 lines:" << std::endl;
              for (int k = j; k < j + 10; k++)
                  std::cout << " Found: " << h_output[k] << std::endl;
              exit(EXIT_FAILURE);
          }
      }
    }

    delete[] h_block_sums;
    delete[] h_output;
    delete[] ha_array;
    delete[] gold;

    std::size_t size_in_mib = N * sizeof(descend::i32)/1024/1024;
    std::size_t footprint_in_mib = size_in_mib * 2;
    float block_sum_size_in_mib = (float)(N/(bs*2)) * sizeof(descend::i32)/1024/1024;
    std::cout << "Input Size: " << size_in_mib << " MiB" << std::endl;
    std::cout << "Footprint: " << footprint_in_mib << " MiB" << std::endl;
    std::cout << "+ Block Sum size in MiB: " << block_sum_size_in_mib << " MiB" << std::endl;
    std::cout << benchmark.to_csv();
    std::cout << "--------------" << std::endl;
    
    benchmark.reset();
  });

  exit(EXIT_SUCCESS);
};
