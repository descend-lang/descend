// =====================================================================================================================
//   code generated from ../examples/infer/huffman/vlc_encode_reuse.desc
// =====================================================================================================================

#include "descend.cuh"
/*
function declarations
*/
template <std::size_t gs>
__host__ auto vlc_encode(const descend::u32 *const h_source_data,
                         const descend::u32 *const h_codewords,
                         const descend::u32 *const h_codewordlens,
                         descend::u32 *const h_out,
                         descend::u32 *const h_out_idx) -> void;
template <std::size_t gs>
__global__ auto gpu_vlc_encode(const descend::u32 *const g_source_data,
                               const descend::u32 *const g_codewords,
                               const descend::u32 *const g_codewordlens,
                               descend::u32 *const g_out,
                               descend::u32 *const g_out_idx) -> void;
/*
function definitions
*/
template <std::size_t gs>
__host__ auto vlc_encode(const descend::u32 *const h_source_data,
                         const descend::u32 *const h_codewords,
                         const descend::u32 *const h_codewordlens,
                         descend::u32 *const h_out,
                         descend::u32 *const h_out_idx) -> void {
    auto gpu = descend::gpu_device(0);
    const auto g_source_data =
    descend::gpu_alloc_copy<descend::array<descend::u32, (gs * 256)>>(
            (&gpu), (&(*h_source_data)));
    const auto g_codewords =
    descend::gpu_alloc_copy<descend::array<descend::u32, 256>>(
            (&gpu), (&(*h_codewords)));
    const auto g_codewordlens =
    descend::gpu_alloc_copy<descend::array<descend::u32, 256>>(
            (&gpu), (&(*h_codewordlens)));
    auto g_out =
    descend::gpu_alloc_copy<descend::array<descend::u32, (gs * 256)>>(
            (&gpu), (&(*h_out)));
    auto g_out_idx = descend::gpu_alloc_copy<descend::array<descend::u32, gs>>(
            (&gpu), (&(*h_out_idx)));
    gpu_vlc_encode<gs>
    <<<dim3(gs, 1, 1), dim3(256, 1, 1),
    ((((0 + (4 * (1 * 256))) + (4 * (1 * 256))) + (4 * (1 * 256))) +
     (4 * (1 * 1)))>>>((&g_source_data), (&g_codewords), (&g_codewordlens),
                       (&g_out), (&g_out_idx));
    descend::copy_to_host<descend::array<descend::u32, (gs * 256)>>((&g_out),
            h_out);
    descend::copy_to_host<descend::array<descend::u32, gs>>((&g_out_idx),
            h_out_idx);
}

template <std::size_t gs>
__global__ auto gpu_vlc_encode(const descend::u32 *const g_source_data,
                               const descend::u32 *const g_codewords,
                               const descend::u32 *const g_codewordlens,
                               descend::u32 *const g_out,
                               descend::u32 *const g_out_idx) -> void {
    extern __shared__ descend::byte $buffer[];
    descend::u32 *const s_codewords = (descend::u32 *)((&$buffer[0]));
    descend::u32 *const s_codewordlens =
            (descend::u32 *)((&s_codewords[(1 * 256)]));
    descend::u32 *const s_scan_and_block_out =
            (descend::u32 *)((&s_codewordlens[(1 * 256)]));
    descend::u32 *const s_last_index_to_copy =
            (descend::u32 *)((&s_scan_and_block_out[(1 * 256)]));

    {

        auto l_thread_out = 0ull;
        auto l_thread_out_len = 0u;
        auto l_thread_start_value = 0u;
        auto l_thread_start_bit = 0u;
        {

            {
                const auto g_codeword_item = (&g_codewords[(threadIdx.x - 0)]);
                const auto g_codewordlen_item = (&g_codewordlens[(threadIdx.x - 0)]);
                const auto s_codeword_item = (&(&(*s_codewords))[(threadIdx.x - 0)]);
                const auto s_codewordlen_item =
                        (&(&(*s_codewordlens))[(threadIdx.x - 0)]);
                (*s_codeword_item) = (*g_codeword_item);
                (*s_codewordlen_item) = (*g_codewordlen_item);
            }
        }

        __syncthreads();
        {
            auto s_scan_ref = (&(*s_scan_and_block_out));

            {
                const auto g_source_data_item =
                        (&g_source_data[(((blockIdx.x - 0) * 256) + (threadIdx.x - 0))]);
                const auto s_scan_item = (&(&(*s_scan_ref))[(threadIdx.x - 0)]);
                const auto tmp_source_data_item = (*g_source_data_item);
                auto tmp_source_data_item_i = ((descend::u8)0);
                auto tmp_cw = 0u;
                auto tmp_cwl = 0u;
                for (std::size_t i = 0; (i < 4); i = (i + 1u)) {
                    tmp_source_data_item_i = (descend::u8)(
                            (tmp_source_data_item >> (8 * (3 - (descend::i32)(i)))));
                    tmp_cw = s_codewords[tmp_source_data_item_i];
                    tmp_cwl = s_codewordlens[tmp_source_data_item_i];
                    l_thread_out = ((l_thread_out << tmp_cwl) | (descend::u64)(tmp_cw));
                    l_thread_out_len = (l_thread_out_len + tmp_cwl);
                }

                (*s_scan_item) = l_thread_out_len;
            }
        }

        {
            auto s_scan_ref = (&(*s_scan_and_block_out));
            for (std::size_t d = 128; (d > 0u); d = (d >> 1)) {
                __syncthreads();
                if (((threadIdx.x - 0) < d)) {
                    {
                        (&(*s_scan_ref))[(((threadIdx.x - 0) * (256 / d)) +
                                          ((256 / d) - 1))] =
                                ((&(*s_scan_ref))[(((threadIdx.x - 0) * (256 / d)) +
                                                   ((256 / d) - 1))] +
                                 (&(*s_scan_ref))[(((threadIdx.x - 0) * (256 / d)) +
                                                   ((128 / d) - 1))]);
                    }
                } else {
                }
            }
        }

        {

            if (((threadIdx.x - 0) < 1)) {
                {
                    const auto last =
                            (&(&(*s_scan_and_block_out))[((threadIdx.x - 0) + (256 - 1))]);
                    (*last) = 0u;
                }
            } else {
            }
        }

        {
            auto s_scan_ref = (&(*s_scan_and_block_out));
            for (std::size_t d = 1; (d <= 128); d = (d * 2u)) {
                __syncthreads();
                if (((threadIdx.x - 0) < d)) {
                    {
                        const auto t = (&(*s_scan_ref))[(((threadIdx.x - 0) * (256 / d)) +
                                                         ((128 / d) - 1))];
                        (&(*s_scan_ref))[(((threadIdx.x - 0) * (256 / d)) +
                                          ((128 / d) - 1))] =
                                (&(*s_scan_ref))[(((threadIdx.x - 0) * (256 / d)) +
                                                  ((256 / d) - 1))];
                        (&(*s_scan_ref))[(((threadIdx.x - 0) * (256 / d)) +
                                          ((256 / d) - 1))] =
                                ((&(*s_scan_ref))[(((threadIdx.x - 0) * (256 / d)) +
                                                   ((256 / d) - 1))] +
                                 t);
                    }
                } else {
                }
            }
        }

        __syncthreads();
        {

            if (((threadIdx.x - 0) < 255)) {
            } else {
                {
                    const auto g_out_idx_block_item =
                            (&g_out_idx[(((blockIdx.x - 0) * 1) + (threadIdx.x - 255))]);
                    const auto s_last_index_to_copy_item =
                            (&(&(*s_last_index_to_copy))[(threadIdx.x - 255)]);
                    (*g_out_idx_block_item) =
                            (s_scan_and_block_out[255] + l_thread_out_len);
                    (*s_last_index_to_copy_item) =
                            ((s_scan_and_block_out[255] + l_thread_out_len) / 32u);
                }
            }
        }

        {
            {
                const auto s_scan_and_block_out_item =
                        (&(&(*s_scan_and_block_out))[(threadIdx.x - 0)]);
                l_thread_start_value = ((*s_scan_and_block_out_item) / 32u);
                l_thread_start_bit = ((*s_scan_and_block_out_item) % 32u);
                (*s_scan_and_block_out_item) = 0u;
            }
        }

        __syncthreads();
        {
            auto s_block_out = (&(*s_scan_and_block_out));
            {
                descend::u32 wrbits;
                if ((l_thread_out_len > (32u - l_thread_start_bit))) {
                    wrbits = (32u - l_thread_start_bit);
                } else {
                    wrbits = l_thread_out_len;
                }

                auto tmpcw =
                        (descend::u32)((l_thread_out >> (l_thread_out_len - wrbits)));
                descend::atomic_fetch_or(
                        descend::atomic_ref<descend::u32>(
                                s_block_out[l_thread_start_value]),
                        (tmpcw << ((32u - l_thread_start_bit) - wrbits)));
                l_thread_out_len = (l_thread_out_len - wrbits);
                if ((l_thread_out_len > 0u)) {
                    if ((l_thread_out_len > 32u)) {
                        wrbits = 32u;
                    } else {
                        wrbits = l_thread_out_len;
                    }

                    tmpcw =
                            ((descend::u32)((l_thread_out >> (l_thread_out_len - wrbits))) &
                             ((1u << wrbits) - 1u));
                    descend::atomic_fetch_or(descend::atomic_ref<descend::u32>(
                                                     s_block_out[(l_thread_start_value + 1)]),
                                             (tmpcw << (32u - wrbits)));
                    l_thread_out_len = (l_thread_out_len - wrbits);
                }

                if ((l_thread_out_len > 0u)) {
                    tmpcw = (descend::u32)(
                            (l_thread_out & ((1ull << l_thread_out_len) - 1ull)));
                    descend::atomic_fetch_or(descend::atomic_ref<descend::u32>(
                                                     s_block_out[(l_thread_start_value + 2)]),
                                             (tmpcw << (32u - l_thread_out_len)));
                }
            }
        }

        __syncthreads();
        {
            {
                const auto g_out_item =
                        (&g_out[(((blockIdx.x - 0) * 256) + (threadIdx.x - 0))]);
                const auto s_block_out_item =
                        (&(&(*s_scan_and_block_out))[(threadIdx.x - 0)]);
                if ((threadIdx.x <= s_last_index_to_copy[0])) {
                    (*g_out_item) = (*s_block_out_item);
                }
            }
        }
    }
}