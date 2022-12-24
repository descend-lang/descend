// code generated from ../examples/infer/huffman/vlc_encode.desc
// 3 __syncthreads operations have been inserted manually
// to_atomic_array call has been removed manually

#include "descend.cuh"
auto vlc_encode(const descend::u32 *const h_source_data,
                const descend::u32 *const h_codewords,
                const descend::u32 *const h_codewordlens,
                descend::u32 *const h_out_data, descend::u32 *const h_out_idx)
-> void {
    {
        descend::Gpu gpu = descend::gpu_device(0);
        const const GpuBuffer<descend::array<descend::u32, (64 * 256)>>
                source_data =
        descend::gpu_alloc_copy<descend::array<descend::u32, (64 * 256)>>(
                (&gpu), (&(*h_source_data)));
        const const GpuBuffer<descend::array<descend::u32, 256>> codewords =
        descend::gpu_alloc_copy<descend::array<descend::u32, 256>>(
                (&gpu), (&(*h_codewords)));
        const const GpuBuffer<descend::array<descend::u32, 256>> codewordlens =
        descend::gpu_alloc_copy<descend::array<descend::u32, 256>>(
                (&gpu), (&(*h_codewordlens)));
        GpuBuffer<descend::array<descend::u32, (64 * 256)>> out_data =
                                                       descend::gpu_alloc_copy<descend::array<descend::u32, (64 * 256)>>(
                (&gpu), (&(*h_out_data)));
        GpuBuffer<descend::array<descend::u32, 64>> out_idx =
                                                       descend::gpu_alloc_copy<descend::array<descend::u32, 64>>(
                (&gpu), (&(*h_out_idx)));
        descend::exec<64, 256>((&gpu), [
        ] __device__ (
                const descend::u32 * const p0,
                const descend::u32 * const p1,
                const descend::u32 * const p2,
                descend::u32 * const p3,
                descend::u32 * const p4) -> void {
            {

                __shared__ descend::u32 sm_cw[256];
                __shared__ descend::u32 sm_cwl[256];
                __shared__ descend::u32 sm_scan_and_result[256];
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
                        descend::u32 *foo = sm_scan_and_result;

                        {
                            codeword = ((descend::u64)0);
                            codewordlen = 0u;
                            const const descend::u32 tmp_d_item =
                                    p0[((blockIdx.x * 256) + threadIdx.x)];
                            descend::u8 tmp_d_item_i = (descend::u8)((tmp_d_item >> 24));
                            descend::u32 tmpcw = sm_cw[tmp_d_item_i];
                            descend::u32 tmpcwl = sm_cwl[tmp_d_item_i];
                            codeword = ((codeword << tmpcwl) | (descend::u64)(tmpcw));
                            codewordlen = (codewordlen + tmpcwl);
                            tmp_d_item_i = (descend::u8)((tmp_d_item >> 16));
                            tmpcw = sm_cw[tmp_d_item_i];
                            tmpcwl = sm_cwl[tmp_d_item_i];
                            codeword = ((codeword << tmpcwl) | (descend::u64)(tmpcw));
                            codewordlen = (codewordlen + tmpcwl);
                            tmp_d_item_i = (descend::u8)((tmp_d_item >> 8));
                            tmpcw = sm_cw[tmp_d_item_i];
                            tmpcwl = sm_cwl[tmp_d_item_i];
                            codeword = ((codeword << tmpcwl) | (descend::u64)(tmpcw));
                            codewordlen = (codewordlen + tmpcwl);
                            tmp_d_item_i = (descend::u8)(tmp_d_item);
                            tmpcw = sm_cw[tmp_d_item_i];
                            tmpcwl = sm_cwl[tmp_d_item_i];
                            codeword = ((codeword << tmpcwl) | (descend::u64)(tmpcw));
                            codewordlen = (codewordlen + tmpcwl);
                            (&(*foo))[threadIdx.x] = codewordlen;
                        }
                    }
                    __syncthreads(); //manually inserted
                    {
                        descend::u32 *foo = sm_scan_and_result;
                        for (std::size_t d = 128; (d > 0u); d = (d / 2u)) {

                            if ((threadIdx.x < d)) {
                                (&(*foo))[(((threadIdx.x - 0) * (256 / d)) + ((256 / d) - 1))] =
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
                        sm_scan_and_result[((threadIdx.x - 0) + (256 - 1))] = 0u;
                    } else {
                    }
                    __syncthreads();
                    {
                        descend::u32 *foo = sm_scan_and_result;
                        for (std::size_t d = 1; (d <= 128); d = (d * 2u)) {

                            if ((threadIdx.x < d)) {
                                const const descend::u32 t = (&(
                                        *foo))[(((threadIdx.x - 0) * (256 / d)) + ((128 / d) - 1))];
                                (&(*foo))[(((threadIdx.x - 0) * (256 / d)) + ((128 / d) - 1))] =
                                        (&(*foo))[(((threadIdx.x - 0) * (256 / d)) +
                                                   ((256 / d) - 1))];
                                (&(*foo))[(((threadIdx.x - 0) * (256 / d)) + ((256 / d) - 1))] =
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
                                    (sm_scan_and_result[255] + codewordlen);
                            sm_kcmax[(threadIdx.x - 255)] =
                                    ((sm_scan_and_result[255] + codewordlen) / 32u);
                        }
                    }
                    __syncthreads();
                    {

                        {kc = (sm_scan_and_result[threadIdx.x] / 32u);
                            startbit = (sm_scan_and_result[threadIdx.x] % 32u);
                            sm_scan_and_result[threadIdx.x] = 0u;
                        }
                    }
                    __syncthreads(); //manually inserted
                    {
                        descend::u32 *sm_result = descend::to_atomic_array<256>(sm_scan_and_result);

                        {
                            descend::u32 wrbits;
                            if ((codewordlen > (32u - startbit))) {
                                wrbits = (32u - startbit);
                            } else {
                                wrbits = codewordlen;
                            }
                            descend::u32 tmpcw =
                                    (descend::u32)((codeword >> (codewordlen - wrbits)));
                            descend::atomic_fetch_or(
                                    descend::atomic_ref<descend::u32>(sm_result[kc]),
                                    (tmpcw << ((32u - startbit) - wrbits)));
                            codewordlen = (codewordlen - wrbits);
                            if ((codewordlen > 0u)) {
                                if ((codewordlen > 32u)) {
                                    wrbits = 32u;
                                } else {
                                    wrbits = codewordlen;
                                }
                                codewordlen = (codewordlen - wrbits);
                                tmpcw = ((descend::u32)((codeword >> codewordlen)) &
                                         ((1u << wrbits) - 1u));
                                descend::atomic_fetch_or(
                                        descend::atomic_ref<descend::u32>(sm_result[(kc + 1)]),
                                        (tmpcw << (32u - wrbits)));
                            }
                            if ((codewordlen > 0u)) {
                                tmpcw =
                                        (descend::u32)((codeword & ((((descend::u64)1) << codewordlen) -
                                                                    ((descend::u64)1))));
                                descend::atomic_fetch_or(
                                        descend::atomic_ref<descend::u32>(sm_result[(kc + 2)]),
                                        (tmpcw << (32u - codewordlen)));
                            }
                        }
                    }

                    __syncthreads(); //manually inserted

                    {

                        if ((descend::thread_id_x() <= sm_kcmax[0])) {
                            p3[((blockIdx.x * 256) + threadIdx.x)] =
                                    sm_scan_and_result[threadIdx.x];
                        }
                    }
                }
            }
        }, (&source_data), (&codewords), (&codewordlens), (&out_data), (&out_idx));
        descend::copy_to_host<descend::array<descend::u32, (64 * 256)>>((&out_data),
                h_out_data);
        descend::copy_to_host<descend::array<descend::u32, 64>>((&out_idx), h_out_idx);
    }
}