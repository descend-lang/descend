#include "descend.cuh"
template <std::size_t m> auto scan_inplace(descend::i32 *const data) -> void {
    const auto accum = 0;
    for (std::size_t _i__0 = 0; _i__0 < m; _i__0 = _i__0 + 1) {
        const auto next = data[_i__0] + accum;
        data[_i__0] = accum;
        accum = next;
    }
}

template <std::size_t n>
auto scan(const descend::i32 *const ha_array, descend::i32 *const h_output,
          descend::i32 *const h_block_sums) -> void {
    const auto gpu = descend::gpu_device(0);
    const auto a_array =
            descend::gpu_alloc<descend::array<descend::i32, n>>(&gpu, ha_array);
    auto out_array =
            descend::gpu_alloc<descend::array<descend::i32, n>>(&gpu, &*h_output);
    const auto block_sums =
            descend::gpu_alloc<descend::array<descend::i32, n / 64>>(&gpu,
                                                                     &*h_block_sums);
    descend::exec<256, 32>(
            &gpu,
            [] __device__(descend::i32 *const p0, descend::i32 *const p1,
                          descend::i32 *const p2) -> void {
                __shared__ descend::i32 tmp[64];
                tmp[threadIdx.x] = p0[blockIdx.x * 64 + threadIdx.x];
                tmp[threadIdx.x + 32] = p0[blockIdx.x * 64 + threadIdx.x + 32];
                __syncthreads();
                for (descend::i32 d = 32; d > 0; d = d / 2) {
                    if (threadIdx.x < d) {
                        tmp[threadIdx.x * 64 / d + 64 / d - 1] =
                                tmp[threadIdx.x * 64 / d + 32 / d - 1];
                    }
                    __syncthreads();
                }
                if (threadIdx.x < 1) {
                    p2[blockIdx.x * 1 + threadIdx.x] = tmp[threadIdx.x + 63];
                    tmp[threadIdx.x + 63] = 0;
                }
                __syncthreads();
                for (descend::i32 d = 1; d <= 32; d = d * 2) {
                    if (threadIdx.x < d) {
                        const auto t = tmp[threadIdx.x * 64 / d + 32 / d - 1];
                        tmp[threadIdx.x * 64 / d + 32 / d - 1] =
                                tmp[threadIdx.x * 64 / d + 64 / d - 1];
                        tmp[threadIdx.x * 64 / d + 64 / d - 1] =
                                tmp[threadIdx.x * 64 / d + 64 / d - 1] + t;
                    }
                    __syncthreads();
                }
                p0[blockIdx.x * 64 + threadIdx.x] = tmp[threadIdx.x];
                p0[blockIdx.x * 64 + threadIdx.x + 32] = tmp[threadIdx.x + 32];
                __syncthreads();
            },
            &a_array, &out_array, &block_sums);
    descend::copy_to_host<descend::array<descend::i32, n / 64>>(&block_sums,
                                                                &*h_block_sums);
    scan_inplace<256>(h_block_sums);
    descend::exec<256, 64>(
            &gpu,
            [] __device__(descend::i32 *const p0,
                          const descend::i32 *const p1) -> void {
                p0[blockIdx.x * 64 + threadIdx.x] =
                        p0[blockIdx.x * 64 + threadIdx.x] + p1[blockIdx.x];
                __syncthreads();
            },
            &out_array, &block_sums);
    descend::copy_to_host<descend::array<descend::i32, n / 64>>(&out_array,
                                                                &*h_output);
}