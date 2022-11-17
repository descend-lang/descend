// Generated from ../examples/infer/huffman/vlc_encode.desc

#include "descend.cuh"
auto vlc_encode(const descend::array<descend::u8, 4> *const h_source_data,
                const descend::u32 *const h_codewords,
                const descend::u32 *const h_codewordlens,
                descend::u32 *const h_out_data, descend::u32 *const h_out_idx)
-> void {
    {
        descend::Gpu gpu = descend::gpu_device(0);
        const const GpuBuffer<
                descend::array<descend::array<descend::u8, 4>, (4 * 256)>>
                source_data = descend::gpu_alloc_copy<
                descend::array<descend::array<descend::u8, 4>, (4 * 256)>>(
                (&gpu), (&(*h_source_data)));
        const const GpuBuffer<descend::array<descend::u32, 256>> codewords =
                descend::gpu_alloc_copy<descend::array<descend::u32, 256>>(
                        (&gpu), (&(*h_codewords)));
        const const GpuBuffer<descend::array<descend::u32, 256>> codewordlens =
                descend::gpu_alloc_copy<descend::array<descend::u32, 256>>(
                        (&gpu), (&(*h_codewordlens)));
        GpuBuffer<descend::array<descend::u32, (4 * 256)>> out_data =
                descend::gpu_alloc_copy<descend::array<descend::u32, (4 * 256)>>(
                        (&gpu), (&(*h_out_data)));
        GpuBuffer<descend::array<descend::u32, 4>> out_idx =
                descend::gpu_alloc_copy<descend::array<descend::u32, 4>>(
                        (&gpu), (&(*h_out_idx)));
        descend::exec<4, 256>(
                (&gpu),
                [] __device__(const descend::array<descend::u8, 4> *const p0,
                              const descend::u32 *const p1,
                              const descend::u32 *const p2, descend::u32 *const p3,
                              descend::u32 *const p4, std::size_t tmp_d_item_i,
                              std::size_t d) -> void {
                    {

                        __shared__ descend::u32 sm_cw[256];
                        __shared__ descend::u32 sm_cwl[256];
                        __shared__ descend::u32 sm_as[256];
                        __shared__ descend::u32 sm_kcmax[1];
                        {

                            descend::u64 codeword;
                            descend::u32 codewordlen;
                            descend::u32 kc;
                            descend::u32 startbit;

                            {
                                sm_cw[threadIdx.x] = p1[threadIdx.x];
                                sm_cwl[threadIdx.x] = p2[threadIdx.x];
                            }
                            {
                                const descend::u32 *const foo = sm_as;

                                {
                                    codeword = 0;
                                    codewordlen = 0;
                                    const const descend::array<descend::u8, 4> tmp_d_item =
                                            p0[((blockIdx.x * 256) + threadIdx.x)];
                                    descend::u8 tmp_d_item_i = tmp_d_item[0];
                                    descend::u32 tmpcw = sm_cw[tmp_d_item_i];
                                    descend::u32 tmpcwl = sm_cwl[tmp_d_item_i];
                                    codeword = ((codeword << tmpcwl) | (descend::u64)(tmpcw));
                                    codewordlen = (codewordlen + tmpcwl);
                                    tmp_d_item_i = tmp_d_item[1];
                                    tmpcw = sm_cw[tmp_d_item_i];
                                    tmpcwl = sm_cwl[tmp_d_item_i];
                                    codeword = ((codeword << tmpcwl) | (descend::u64)(tmpcw));
                                    codewordlen = (codewordlen + tmpcwl);
                                    tmp_d_item_i = tmp_d_item[2];
                                    tmpcw = sm_cw[tmp_d_item_i];
                                    tmpcwl = sm_cwl[tmp_d_item_i];
                                    codeword = ((codeword << tmpcwl) | (descend::u64)(tmpcw));
                                    codewordlen = (codewordlen + tmpcwl);
                                    tmp_d_item_i = tmp_d_item[3];
                                    tmpcw = sm_cw[tmp_d_item_i];
                                    tmpcwl = sm_cwl[tmp_d_item_i];
                                    codeword = ((codeword << tmpcwl) | (descend::u64)(tmpcw));
                                    codewordlen = (codewordlen + tmpcwl);
                                    (&(*foo))[threadIdx.x] = codewordlen;
                                }
                            }
                            {
                                const descend::u32 *const foo = sm_as;
                                for (std::size_t d = 128; (d > 0); d = (d / 2)) {

                                    if ((threadIdx.x < d)) {
                                        (&(*foo))[(((threadIdx.x - 0) * (256 / d)) +
                                                   ((256 / d) - 1))] =
                                                ((&(*foo))[(((threadIdx.x - 0) * (256 / d)) +
                                                            ((256 / d) - 1))] +
                                                 (&(*foo))[(((threadIdx.x - 0) * (256 / d)) +
                                                            ((128 / d) - 1))]);
                                    } else {
                                    }
                                    __syncthreads();
                                }
                            }

                            if ((threadIdx.x < 1)) {
                                sm_as[((threadIdx.x - 0) + (256 - 1))] = 0;
                            } else {
                            }
                            __syncthreads();
                            {
                                const descend::u32 *const foo = sm_as;
                                for (std::size_t d = 1; (d <= 128); d = (d * 2)) {

                                    if ((threadIdx.x < d)) {
                                        const const descend::u32 t = (&(*foo))[(
                                                ((threadIdx.x - 0) * (256 / d)) + ((128 / d) - 1))];
                                        (&(*foo))[(((threadIdx.x - 0) * (256 / d)) +
                                                   ((128 / d) - 1))] =
                                                (&(*foo))[(((threadIdx.x - 0) * (256 / d)) +
                                                           ((256 / d) - 1))];
                                        (&(*foo))[(((threadIdx.x - 0) * (256 / d)) +
                                                   ((256 / d) - 1))] =
                                                ((&(*foo))[(((threadIdx.x - 0) * (256 / d)) +
                                                            ((256 / d) - 1))] +
                                                 t);
                                    } else {
                                    }
                                    __syncthreads();
                                }
                            }
                            if ((threadIdx.x < 255)) {

                            } else {

                                {
                                    p4[((blockIdx.x * 1) + (threadIdx.x - 255))] =
                                            (sm_as[255] + codewordlen);
                                    sm_kcmax[(threadIdx.x - 255)] =
                                            ((sm_as[255] + codewordlen) / 32);
                                }
                            }
                            __syncthreads();
                            {
                                const descend::u32 *const foo = sm_as;

                                {
                                    kc = ((&(*foo))[threadIdx.x] / 32);
                                    startbit = ((&(*foo))[threadIdx.x] % 32);
                                    (&(*foo))[threadIdx.x] = 0;
                                }
                            }

                            {
                                descend::u32 wrbits;
                                if ((codewordlen > (32 - startbit))) {
                                    wrbits = (32 - startbit);
                                } else {
                                    wrbits = codewordlen;
                                }
                                descend::u32 tmpcw =
                                        (descend::u32)((codeword >> (codewordlen - wrbits)));
                                codewordlen = (codewordlen - wrbits);
                                if ((codewordlen > 0)) {
                                    if ((codewordlen > 32)) {
                                        wrbits = 32;
                                    } else {
                                        wrbits = codewordlen;
                                    }
                                    codewordlen = (codewordlen - wrbits);
                                    tmpcw = ((descend::u32)((codeword >> codewordlen)) &
                                             ((1 << wrbits) - 1));
                                }
                                if ((codewordlen > 0)) {
                                    tmpcw = (descend::u32)((codeword & ((1 << codewordlen) - 1)));
                                }
                            }

                            { p3[((blockIdx.x * 256) + threadIdx.x)] = sm_as[threadIdx.x]; }
                        }
                    }
                },
                (&source_data), (&codewords), (&codewordlens), (&out_data), (&out_idx),
                tmp_d_item_i, d);
        descend::copy_to_host<descend::array<descend::u32, (4 * 256)>>((&out_data),
                                                                       h_out_data);
        descend::copy_to_host<descend::array<descend::u32, 4>>((&out_idx),
                                                               h_out_idx);
    }
}