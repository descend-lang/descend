// code generated from ../examples/infer/huffman/vlc_encode.desc
// 3 __syncthreads operations have been inserted manually
// 3 deref operators in front of arrays have been removed manually

#include "descend.cuh"
auto vlc_encode(const descend::u32 *const h_source_data,
                const descend::u32 *const h_codewords,
                const descend::u32 *const h_codewordlens,
                descend::u32 *const h_out, descend::u32 *const h_out_idx)
-> void {
    {
        descend::Gpu gpu = descend::gpu_device(0);
        const const GpuBuffer<descend::array<descend::u32, (64 * 256)>>
                g_source_data =
        descend::gpu_alloc_copy<descend::array<descend::u32, (64 * 256)>>(
                (&gpu), (&(*h_source_data)));
        const const GpuBuffer<descend::array<descend::u32, 256>> g_codewords =
        descend::gpu_alloc_copy<descend::array<descend::u32, 256>>(
                (&gpu), (&(*h_codewords)));
        const const GpuBuffer<descend::array<descend::u32, 256>> g_codewordlens =
        descend::gpu_alloc_copy<descend::array<descend::u32, 256>>(
                (&gpu), (&(*h_codewordlens)));
        GpuBuffer<descend::array<descend::u32, (64 * 256)>> g_out =
                                                       descend::gpu_alloc_copy<descend::array<descend::u32, (64 * 256)>>(
                (&gpu), (&(*h_out)));
        GpuBuffer<descend::array<descend::u32, 64>> g_out_idx =
                                                       descend::gpu_alloc_copy<descend::array<descend::u32, 64>>(
                (&gpu), (&(*h_out_idx)));
        descend::exec<64, 256>(
                (&gpu),
                [] __device__(const descend::u32 *const p0,
                              const descend::u32 *const p1,
                              const descend::u32 *const p2, descend::u32 *const p3,
                              descend::u32 *const p4) -> void {
                    {

                        __shared__ descend::u32 s_codewords[256];
                        __shared__ descend::u32 s_codewordlens[256];
                        __shared__ descend::u32 s_result_locations[256];
                        __shared__ descend::u32 s_block_out[256];
                        __shared__ descend::u32 s_last_index_to_copy[1];
                        {

                            descend::u64 l_thread_out;
                            descend::u32 l_thread_out_len;
                            descend::u32 l_thread_start_value;
                            descend::u32 l_thread_start_bit;

                            {
                                s_codewords[threadIdx.x] = p1[threadIdx.x];
                                s_codewordlens[threadIdx.x] = p2[threadIdx.x];
                            }
                            __syncthreads(); //manually inserted
                            {
                                descend::u32 *s_result_locations_ref = s_result_locations;

                                {
                                    l_thread_out = ((descend::u64)0);
                                    l_thread_out_len = 0u;
                                    const const descend::u32 tmp_source_data_item =
                                            p0[((blockIdx.x * 256) + threadIdx.x)];
                                    descend::u8 tmp_source_data_item_i;
                                    descend::u32 tmp_cw;
                                    descend::u32 tmp_cwl;
                                    tmp_source_data_item_i =
                                            (descend::u8)((tmp_source_data_item >> 24));
                                    tmp_cw = s_codewords[tmp_source_data_item_i];
                                    tmp_cwl = s_codewordlens[tmp_source_data_item_i];
                                    l_thread_out =
                                            ((l_thread_out << tmp_cwl) | (descend::u64)(tmp_cw));
                                    l_thread_out_len = (l_thread_out_len + tmp_cwl);
                                    tmp_source_data_item_i =
                                            (descend::u8)((tmp_source_data_item >> 16));
                                    tmp_cw = s_codewords[tmp_source_data_item_i];
                                    tmp_cwl = s_codewordlens[tmp_source_data_item_i];
                                    l_thread_out =
                                            ((l_thread_out << tmp_cwl) | (descend::u64)(tmp_cw));
                                    l_thread_out_len = (l_thread_out_len + tmp_cwl);
                                    tmp_source_data_item_i =
                                            (descend::u8)((tmp_source_data_item >> 8));
                                    tmp_cw = s_codewords[tmp_source_data_item_i];
                                    tmp_cwl = s_codewordlens[tmp_source_data_item_i];
                                    l_thread_out =
                                            ((l_thread_out << tmp_cwl) | (descend::u64)(tmp_cw));
                                    l_thread_out_len = (l_thread_out_len + tmp_cwl);
                                    tmp_source_data_item_i = (descend::u8)(tmp_source_data_item);
                                    tmp_cw = s_codewords[tmp_source_data_item_i];
                                    tmp_cwl = s_codewordlens[tmp_source_data_item_i];
                                    l_thread_out =
                                            ((l_thread_out << tmp_cwl) | (descend::u64)(tmp_cw));
                                    l_thread_out_len = (l_thread_out_len + tmp_cwl);
                                    (&(*s_result_locations_ref))[threadIdx.x] = l_thread_out_len;
                                }
                            }
                            __syncthreads(); //manually inserted
                            {
                                descend::u32 *s_result_locations_ref = s_result_locations;
                                for (std::size_t d = 128; (d > 0u); d = (d / 2u)) {

                                    if ((threadIdx.x < d)) {
                                        (&(*s_result_locations_ref))[(
                                                ((threadIdx.x - 0) * (256 / d)) + ((256 / d) - 1))] =
                                                ((&(*s_result_locations_ref))[(
                                                        ((threadIdx.x - 0) * (256 / d)) +
                                                        ((256 / d) - 1))] +
                                                 (&(*s_result_locations_ref))[(
                                                         ((threadIdx.x - 0) * (256 / d)) +
                                                         ((128 / d) - 1))]);
                                    } else {
                                    }
                                    __syncthreads();
                                }
                            }

                            if ((threadIdx.x < 1)) {
                                s_result_locations[((threadIdx.x - 0) + (256 - 1))] = 0u;
                            } else {
                            }
                            __syncthreads();
                            {
                                descend::u32 *s_result_locations_ref = s_result_locations;
                                for (std::size_t d = 1; (d <= 128); d = (d * 2u)) {

                                    if ((threadIdx.x < d)) {
                                        const const descend::u32 t = (&(*s_result_locations_ref))[(
                                                ((threadIdx.x - 0) * (256 / d)) + ((128 / d) - 1))];
                                        (&(*s_result_locations_ref))[(
                                                ((threadIdx.x - 0) * (256 / d)) + ((128 / d) - 1))] =
                                                (&(*s_result_locations_ref))[(
                                                        ((threadIdx.x - 0) * (256 / d)) + ((256 / d) - 1))];
                                        (&(*s_result_locations_ref))[(
                                                ((threadIdx.x - 0) * (256 / d)) + ((256 / d) - 1))] =
                                                ((&(*s_result_locations_ref))[(
                                                        ((threadIdx.x - 0) * (256 / d)) +
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
                                            (s_result_locations[255] + l_thread_out_len);
                                    s_last_index_to_copy[(threadIdx.x - 255)] =
                                            ((s_result_locations[255] + l_thread_out_len) / 32u);
                                }
                            }
                            __syncthreads();

                            {
                                l_thread_start_value = (s_result_locations[threadIdx.x] / 32u);
                                l_thread_start_bit = (s_result_locations[threadIdx.x] % 32u);
                                descend::atomic_store(
                                        descend::atomic_ref<descend::u32>(s_block_out[threadIdx.x]),
                                        0u);
                            }
                            __syncthreads(); //manually inserted

                            {
                                descend::u32 wrbits;
                                if ((l_thread_out_len > (32u - l_thread_start_bit))) {
                                    wrbits = (32u - l_thread_start_bit);
                                } else {
                                    wrbits = l_thread_out_len;
                                }
                                descend::u32 tmpcw = (descend::u32)(
                                        (l_thread_out >> (l_thread_out_len - wrbits)));
                                descend::atomic_fetch_or(
                                        descend::atomic_ref<descend::u32>(
                                                (s_block_out)[l_thread_start_value]),
                                        (tmpcw << ((32u - l_thread_start_bit) - wrbits)));
                                l_thread_out_len = (l_thread_out_len - wrbits);
                                if ((l_thread_out_len > 0u)) {
                                    if ((l_thread_out_len > 32u)) {
                                        wrbits = 32u;
                                    } else {
                                        wrbits = l_thread_out_len;
                                    }
                                    l_thread_out_len = (l_thread_out_len - wrbits);
                                    tmpcw = ((descend::u32)((l_thread_out >> l_thread_out_len)) &
                                             ((1u << wrbits) - 1u));
                                    descend::atomic_fetch_or(
                                            descend::atomic_ref<descend::u32>(
                                                    (s_block_out)[(l_thread_start_value + 1)]),
                                            (tmpcw << (32u - wrbits)));
                                }
                                if ((l_thread_out_len > 0u)) {
                                    tmpcw = (descend::u32)(
                                            (l_thread_out & ((((descend::u64)1) << l_thread_out_len) -
                                                             ((descend::u64)1))));
                                    descend::atomic_fetch_or(
                                            descend::atomic_ref<descend::u32>(
                                                    (s_block_out)[(l_thread_start_value + 2)]),
                                            (tmpcw << (32u - l_thread_out_len)));
                                }

                                if ((descend::thread_id_x() <= s_last_index_to_copy[0])) {
                                    p3[((blockIdx.x * 256) + threadIdx.x)] =
                                            descend::atomic_load(descend::atomic_ref<descend::u32>(
                                                    s_block_out[threadIdx.x]));
                                }
                            }
                        }
                    }
                },
                (&g_source_data), (&g_codewords), (&g_codewordlens), (&g_out),
                (&g_out_idx));
        descend::copy_to_host<descend::array<descend::u32, (64 * 256)>>((&g_out),
                h_out);
        descend::copy_to_host<descend::array<descend::u32, 64>>((&g_out_idx),
                h_out_idx);
    }
}