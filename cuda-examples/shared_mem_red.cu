#include "descend.cuh"

template<std::size_t n>
auto reduce_shared_mem(
        const descend::i32 * const ha_array,
        descend::i32 * const h_output
) -> void {
    const auto gpu = descend::gpu_device(0);
    const auto a_array = descend::gpu_alloc<descend::array<descend::i32, n>>(&gpu, ha_array);
    auto out_array = descend::gpu_alloc<descend::array<descend::i32, 64>>(&gpu, &*h_output);
    descend::exec<64, 1024>(&gpu, [] __device__ (
            const descend::i32 * const p0,
            descend::i32 * const p1) -> void {
        __shared__ descend::i32 tmp[1024];
        tmp[threadIdx.x] = p0[blockIdx.x * 1024 + threadIdx.x];
        __syncthreads();
        for (descend::i32 k = 512; k > 0; k = k / 2) {
            if (threadIdx.x < k)
            {
                tmp[threadIdx.x] = tmp[threadIdx.x] + tmp[threadIdx.x + k];
            }

            __syncthreads();
        }

        if (threadIdx.x < 1)
        {
            p1[blockIdx.x * 1 + threadIdx.x] = tmp[threadIdx.x];
        }

        __syncthreads();
        ;
    }, &a_array, &out_array);
    descend::copy_to_host<descend::array<descend::i32, 64>>(&out_array, h_output);
}

auto main() -> int {
    const auto ha_array = descend::HeapBuffer<descend::array<descend::i32, 64*1024>>(1);
    auto h_output = descend::HeapBuffer<descend::array<descend::i32, 64>>(0);
    reduce_shared_mem<64*1024>(&ha_array, &h_output);

    for (size_t i = 0; i < 64; i++) {
        if (h_output[i] != 1024) {
            std::cout << "At i = " << i << "Wrong number. Found " << h_output[i] << " instead of 1024.";
            exit(EXIT_FAILURE);
        }
    }
    exit(EXIT_SUCCESS);
}
