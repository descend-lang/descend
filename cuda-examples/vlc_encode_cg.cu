// code generated from ../examples/infer/huffman/vlc_encode.desc with a hand written shfl scan
// 2 __syncthreads operations have been inserted manually

#include "descend.cuh"
// todo include cooperative groups in descend.cuh
#include <cooperative_groups.h>
namespace cg = cooperative_groups;

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
        descend::exec<64, 256>(
                (&gpu),
                [] __device__(const descend::u32 *const p0,
                              const descend::u32 *const p1,
                              const descend::u32 *const p2, descend::u32 *const p3,
                              descend::u32 *const p4) -> void {
                    {

                        __shared__ descend::u32 sm_cw[256];
                        __shared__ descend::u32 sm_cwl[256];
                        __shared__ descend::u32 sm_scan_arr[7];
                        __shared__ descend::u32 sm_block_enc[256];
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
                            __syncthreads(); // manually inserted!
                            {
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
                                }
                            }



                            // begin hand written cg shfl scan

                            descend::u32 scan_codewordlen;
                            descend::u32 tmp_shfl_res;
                            auto warp = cg::tiled_partition<32>(cg::this_thread_block());

                            {
                                scan_codewordlen = codewordlen;
                                for (std::size_t k = 1; (k <= 16); k = (k * 2)) {
                                    tmp_shfl_res = warp.shfl_up(scan_codewordlen, k);
                                    if (warp.thread_rank() < k) {
                                    }
                                    else {
                                        scan_codewordlen = scan_codewordlen + tmp_shfl_res;
                                    }
                                }
                            }

                            if (warp.meta_group_rank() < 7) {
                                if (warp.thread_rank() < 31) {
                                }
                                else {
                                    sm_scan_arr[warp.meta_group_rank()] = scan_codewordlen;
                                }
                            }
                            else {
                            }


                            __syncthreads();

                            if (warp.meta_group_rank() < 1) {
                                descend::u32 scan_block;
                                if (warp.thread_rank() < 7) {
                                    scan_block = sm_scan_arr[warp.thread_rank()];
                                }
                                else {
                                    scan_block = 0;
                                }
                                for (std::size_t k = 1; (k <= 4); k = (k * 2)) {
                                    tmp_shfl_res = warp.shfl_up(scan_block, k);
                                    if (warp.thread_rank() < k) {
                                    }
                                    else {
                                        scan_block = scan_block + tmp_shfl_res;
                                    }
                                }
                                if (warp.thread_rank() < 7) {
                                    sm_scan_arr[warp.thread_rank()] = scan_block;
                                }
                                else {
                                }
                            }
                            else {
                            }

                            __syncthreads();

                            if (warp.meta_group_rank() < 1) {
                            }
                            else {
                                scan_codewordlen = scan_codewordlen + sm_scan_arr[warp.meta_group_rank() - 1];
                            }

                            {
                                scan_codewordlen = scan_codewordlen - codewordlen;
                            }

                            // end hand written cg shfl scan



                            if ((threadIdx.x < 255)) {

                            } else {

                                {
                                    p4[((blockIdx.x * 1) + (threadIdx.x - 255))] =
                                            (scan_codewordlen + codewordlen);
                                    sm_kcmax[(threadIdx.x - 255)] =
                                            (scan_codewordlen + codewordlen) / 32u;
                                }
                            }
                            __syncthreads();
                            {
                                kc = (scan_codewordlen / 32);
                                startbit = (scan_codewordlen % 32);
                                descend::atomic_store(descend::atomic_ref<descend::u32>(
                                                              sm_block_enc[threadIdx.x]),
                                                      0u);
                            }
                            __syncthreads(); // manually inserted
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
                                        descend::atomic_ref<descend::u32>((*(&sm_block_enc[kc]))),
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
                                    descend::atomic_fetch_or(descend::atomic_ref<descend::u32>(
                                                                     (*(&sm_block_enc[(kc + 1)]))),
                                                             (tmpcw << (32u - wrbits)));
                                }
                                if ((codewordlen > 0u)) {
                                    tmpcw = (descend::u32)(
                                            (codeword & ((((descend::u64)1) << codewordlen) -
                                                         ((descend::u64)1))));
                                    descend::atomic_fetch_or(descend::atomic_ref<descend::u32>(
                                                                     (*(&sm_block_enc[(kc + 2)]))),
                                                             (tmpcw << (32u - codewordlen)));
                                }

                                if ((descend::thread_id_x() <= sm_kcmax[0])) {
                                    p3[((blockIdx.x * 256) + threadIdx.x)] =
                                            descend::atomic_load(descend::atomic_ref<descend::u32>(
                                                    sm_block_enc[threadIdx.x]));
                                }
                            }
                        }
                    }
                },
                (&source_data), (&codewords), (&codewordlens), (&out_data), (&out_idx));
        descend::copy_to_host<descend::array<descend::u32, (64 * 256)>>((&out_data),
                                                                        h_out_data);
        descend::copy_to_host<descend::array<descend::u32, 64>>((&out_idx),
                                                                h_out_idx);
    }
}