#include "descend.cuh"
auto hist(const descend::u8 *const h_in, descend::u32 *const h_out) -> void {
    {
        descend::Gpu gpu = descend::gpu_device(0);
        const const GpuBuffer<descend::array<descend::u8, (64 * 1024)>> d_in =
        descend::gpu_alloc_copy<descend::array<descend::u8, (64 * 1024)>>(
                (&gpu), (&(*h_in)));
        GpuBuffer<descend::array<descend::u32, 256>> d_out =
                                                       descend::gpu_alloc_copy<descend::array<descend::u32, 256>>((&gpu),
                (&(*h_out)));
        descend::exec<64, 1024>(
                (&gpu),
                [] __device__(const descend::u8 *const p0,
                              descend::u32 *const p1) -> void {
                    {

                        const descend::u32 *const d_out_atomic =
                                descend::to_atomic_array<256>(p1);

                        __shared__ descend::u32 sm_out[256];
                        {

                            if ((threadIdx.x < 256)) {

                                {
                                    descend::atomic_store(descend::atomic_ref<descend::u32>(
                                                                  sm_out[(threadIdx.x - 0)]),
                                                          0u);
                                }
                            } else {
                            }
                            __syncthreads();

                            {
                                const const descend::u8 tmp =
                                        p0[((blockIdx.x * 1024) + threadIdx.x)];
                                descend::atomic_fetch_add(
                                        descend::atomic_ref<descend::u32>((*sm_out)[tmp]), 1u);
                            }

                            __syncthreads(); // manually inserted!

                            if ((threadIdx.x < 256)) {

                                {
                                    descend::atomic_fetch_add(
                                            descend::atomic_ref<descend::u32>(
                                                    d_out_atomic[threadIdx.x]),
                                            descend::atomic_load(descend::atomic_ref<descend::u32>(
                                                    sm_out[threadIdx.x])));
                                }
                            } else {
                            }
                            __syncthreads();
                        }
                    }
                },
                (&d_in), (&d_out));
        descend::copy_to_host<descend::array<descend::u32, 256>>((&d_out), h_out);
    }
}