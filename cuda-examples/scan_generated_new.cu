#include "descend.cuh"
/*
function declarations
*/
template <std::size_t m>
__host__ auto scan_inplace(descend::i32 *const data) -> void;
template <std::size_t n>
__global__ auto par_scan(const descend::i32 *const input,
                         descend::i32 *const output,
                         descend::i32 *const block_sums) -> void;
__global__ auto par_scan2(descend::i32 *const input,
                          const descend::i32 *const block_sums) -> void;
template <std::size_t n, std::size_t gridDim>
__host__ auto scan(const descend::i32 *const ha_array,
                   descend::i32 *const h_output,
                   descend::i32 *const h_block_sums) -> void;
/*
function definitions
*/
template <std::size_t m>
__host__ auto scan_inplace(descend::i32 *const data) -> void {
  auto accum = 0;
}

template <std::size_t n>
__global__ auto par_scan(const descend::i32 *const input,
                         descend::i32 *const output,
                         descend::i32 *const block_sums) -> void {
  extern __shared__ descend::byte $buffer[];
  descend::i32 *const tmp = (descend::i32 *)(&$buffer[0]);

  {
    const auto ib = (&input[blockIdx.x - 0 * 64]);
    const auto block_out = (&output[blockIdx.x - 0 * 64]);
    const auto bsum = (&block_sums[blockIdx.x - 0 * 1]);
    {
      const auto tmp_halves = (&tmp);
      const auto input_halves = (&ib);
      {
        tmp_halves .0 [threadIdx.x - 0] = input_halves .0 [threadIdx.x - 0];
        tmp_halves .1 [threadIdx.x - 0] = input_halves .1 [threadIdx.x - 0];
      }
    }

    for (std::size_t dd = 32; dd > 0; dd = dd / 2) {
      if (threadIdx.x - 0 < dd) {
        const auto arr = (&tmp[threadIdx.x - 0 * 64 / dd]);
        arr[64 / dd - 1] = arr[64 / dd - 1] + arr[32 / dd - 1];
      } else {
      }
    }

    {
      const auto tmp_last = (&tmp);
      if (threadIdx.x - 0 < 1) {
        bsum[threadIdx.x - 0] = tmp_last[threadIdx.x - 0];
        tmp_last[threadIdx.x - 0] = 0;
      } else {
      }
    }

    for (std::size_t dd = 1; dd <= 32; dd = dd * 2) {
      if (threadIdx.x - 0 < dd) {
        const auto arr = (&tmp[threadIdx.x - 0 * 64 / dd]);
        const auto t = arr[32 / dd - 1];
        arr[32 / dd - 1] = arr[64 / dd - 1];
        arr[64 / dd - 1] = arr[64 / dd - 1] + t;
      } else {
      }
    }

    {
      const auto tmp_halves = (&tmp);
      const auto output_halves = (&block_out);
      {
        output_halves .0 [threadIdx.x - 0] = tmp_halves .0 [threadIdx.x - 0];
        output_halves .1 [threadIdx.x - 0] = tmp_halves .1 [threadIdx.x - 0];
      }
    }
  }
}

__global__ auto par_scan2(descend::i32 *const input,
                          const descend::i32 *const block_sums) -> void {
  extern __shared__ descend::byte $buffer[];

  {
    const auto block_sum = (&block_sums[blockIdx.x - 0 * 1]);
    const auto val = (&input[blockIdx.x - 0 * 64]);
    {
      const auto scanned_val = (&val[threadIdx.x - 0]);
      scanned_val = scanned_val + block_sum[threadIdx.x - 0];
    }
  }
}

template <std::size_t n, std::size_t gridDim>
__host__ auto scan(const descend::i32 *const ha_array,
                   descend::i32 *const h_output,
                   descend::i32 *const h_block_sums) -> void {
  auto gpu = descend::gpu_device(0);
  const auto a_array = descend::gpu_alloc_copy<descend::array<descend::i32, n>>(
      (&gpu), ha_array);
  auto out_array = descend::gpu_alloc_copy<descend::array<descend::i32, n>>(
      (&gpu), (&h_output));
  auto block_sums =
      descend::gpu_alloc_copy<descend::array<descend::i32, n / 64>>(
          (&gpu), (&h_block_sums));
  par_scan<n><<<dim3(gridDim, 1, 1), dim3(32, 1, 1), 0 + 4 * 1 * 64>>>(
      (&a_array), (&out_array), (&block_sums));
  descend::copy_to_host<descend::array<descend::i32, n / 64>>((&block_sums),
                                                              (&h_block_sums));
  scan_inplace<gridDim>((&h_block_sums));
  descend::copy_to_gpu<descend::array<descend::i32, n / 64>>((&block_sums),
                                                             (&h_block_sums));
  par_scan2<<<dim3(gridDim, 1, 1), dim3(64, 1, 1), 0>>>((&out_array),
                                                        (&block_sums));
  descend::copy_to_host<descend::array<descend::i32, n>>((&out_array),
                                                         (&h_output));
}
