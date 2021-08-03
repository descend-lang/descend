#include <iostream>
#include "descend.cuh"
template<std::size_t m>
auto scan_inplace(
        descend::i32 * const data
) -> void {
    auto accum = 0;
    for (std::size_t _i__0 = 0; _i__0 < m; _i__0 = _i__0 + 1) {
        const auto next = data[_i__0] + accum;
        data[_i__0] = accum;
        accum = next;
    }
}

template<std::size_t n>
auto scan(
        const descend::i32 * const ha_array,
        descend::i32 * const h_output,
        descend::i32 * const h_block_sums
) -> void {
    const auto gpu = descend::gpu_device(0);
    const auto a_array = descend::gpu_alloc<descend::array<descend::i32, n>>(&gpu, ha_array);
    auto out_array = descend::gpu_alloc<descend::array<descend::i32, n>>(&gpu, &*h_output);
    auto block_sums = descend::gpu_alloc<descend::array<descend::i32, n / 64>>(&gpu, &*h_block_sums);
    descend::exec<256, 32>(&gpu, [] __device__ (
            const descend::i32 * const p0,
            descend::i32 * const p1,
            descend::i32 * const p2) -> void {
        __shared__ descend::i32 tmp[64];
        tmp[threadIdx.x] = p0[blockIdx.x * 64 + threadIdx.x];
        tmp[threadIdx.x + 32] = p0[blockIdx.x * 64 + threadIdx.x + 32];
        __syncthreads();
        for (descend::i32 d = 32; d > 0; d = d / 2) {
            if (threadIdx.x < d)
            {
                tmp[threadIdx.x * 64 / d + 64 / d - 1] = tmp[threadIdx.x * 64 / d + 64 / d - 1] + tmp[threadIdx.x * 64 / d + 32 / d - 1];
            }
            __syncthreads();
        }
        if (threadIdx.x < 1)
        {
            p2[blockIdx.x * 1 + threadIdx.x] = tmp[threadIdx.x + 63];
            tmp[threadIdx.x + 63] = 0;
        }
        __syncthreads();
        for (descend::i32 d = 1; d <= 32; d = d * 2) {
            if (threadIdx.x < d)
            {
                const auto t = tmp[threadIdx.x * 64 / d + 32 / d - 1];
                tmp[threadIdx.x * 64 / d + 32 / d - 1] = tmp[threadIdx.x * 64 / d + 64 / d - 1];
                tmp[threadIdx.x * 64 / d + 64 / d - 1] = tmp[threadIdx.x * 64 / d + 64 / d - 1] + t;
            }
            __syncthreads();
        }
        p1[blockIdx.x * 64 + threadIdx.x] = tmp[threadIdx.x];
        p1[blockIdx.x * 64 + threadIdx.x + 32] = tmp[threadIdx.x + 32];
        __syncthreads();

    }, &a_array, &out_array, &block_sums);
    descend::copy_to_host<descend::array<descend::i32, n / 64>>(&block_sums, &*h_block_sums);
    scan_inplace<256>(&*h_block_sums);
    descend::copy_to_gpu<descend::array<descend::i32, n / 64>>(&block_sums, &*h_block_sums);
    descend::exec<256, 64>(&gpu, [] __device__ (
            descend::i32 * const p0,
            const descend::i32 * const p1) -> void {
        p0[blockIdx.x * 64 + threadIdx.x] = p0[blockIdx.x * 64 + threadIdx.x] + p1[blockIdx.x];
        __syncthreads();

    }, &out_array, &block_sums);
    descend::copy_to_host<descend::array<descend::i32, n>>(&out_array, &*h_output);
}

auto main() -> int {
    #define N 256*32*2
    const auto ha_array = descend::HeapBuffer<descend::array<descend::i32, N>>(3);
    auto h_output = descend::HeapBuffer<descend::array<descend::i32, N>>(0);
    auto h_block_sums = descend::HeapBuffer<descend::array<descend::i32, N/64>>(0);
    scan<N>(&ha_array, &h_output, &h_block_sums);

    // Check results
    auto gold = descend::HeapBuffer<descend::array<descend::i32, N>>(3);
    scan_inplace<N>(&gold);
    for (int i = 0; i < N; i++) {
        if (h_output[i] != gold[i]) {
            std::cout << "Error at " << i << ": Expected `" << gold[i]
                << "` but found `" << h_output[i] << "`" << std::endl;
            std::cout << "Next 10 lines:" << std::endl;
            for (int j = i; j < i+10; j++)
                std::cout << "Expected: " << gold[j] << " Found: " << h_output[i] << std::endl;
            exit(EXIT_FAILURE);
        }
    }
};