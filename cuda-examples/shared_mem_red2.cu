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
            const GpuBuffer<descend::array<descend::i32, n>> p0,
            descend::i32 * const p1) -> void {
        __shared__ descend::i32 tmp[1024];
        tmp[threadIdx.x] = &views.0[blockIdx.x * 1024 + threadIdx.x];
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
    }, a_array, &out_array);
    descend::copy_to_host<descend::array<descend::i32, 64>>(&out_array, h_output);
}