// =====================================================================================================================
//   code generated from ../examples/infer/huffman/histogram.desc
// =====================================================================================================================

#include "descend.cuh"
/*
function declarations
*/
template <std::size_t gs, std::size_t ts>
__host__ auto hist(const descend::u8 *const h_in, descend::u32 *const h_out)
-> void;
template <std::size_t gs, std::size_t ts>
__global__ auto gpu_hist(const descend::u8 *const d_in,
                         descend::u32 *const d_out) -> void;
/*
function definitions
*/
template <std::size_t gs, std::size_t ts>
__host__ auto hist(const descend::u8 *const h_in, descend::u32 *const h_out)
-> void {
    auto gpu = descend::gpu_device(0);
    const auto d_in =
    descend::gpu_alloc_copy<descend::array<descend::u8, ((gs * 256) * ts)>>(
            (&gpu), (&(*h_in)));
    auto d_out = descend::gpu_alloc_copy<descend::array<descend::u32, 256>>(
            (&gpu), (&(*h_out)));
    gpu_hist<gs, ts><<<dim3(gs, 1, 1), dim3(256, 1, 1), (0 + (4 * (1 * 256)))>>>(
            (&d_in), (&d_out));
    descend::copy_to_host<descend::array<descend::u32, 256>>((&d_out), h_out);
}

template <std::size_t gs, std::size_t ts>
__global__ auto gpu_hist(const descend::u8 *const d_in,
                         descend::u32 *const d_out) -> void {
    extern __shared__ descend::byte $buffer[];
    descend::u32 *const s_block_out = (descend::u32 *)((&$buffer[0]));

    const auto d_out_atomic = d_out;

    {
        {
            const auto s_block_out_item = (&(&(*s_block_out))[(threadIdx.x - 0)]);

            const auto d_out_atomic_item = (&(&(*d_out_atomic))[(threadIdx.x - 0)]);
            descend::atomic_store(
                    descend::atomic_ref<descend::u32>((*s_block_out_item)), 0u);
            __syncthreads();
            for (std::size_t i = 0; (i < ts); i = (i + 1u)) {
                const auto tmp = d_in[((i * (gs * 256)) +
                                       (((blockIdx.x - 0) * 256) + (threadIdx.x - 0)))];
                descend::atomic_fetch_add(
                        descend::atomic_ref<descend::u32>(s_block_out[tmp]), 1u);
            }

            __syncthreads();
            descend::atomic_fetch_add(
                    descend::atomic_ref<descend::u32>((*d_out_atomic_item)),
                    descend::atomic_load(
                            descend::atomic_ref<descend::u32>((*s_block_out_item))));
        }
    }
}