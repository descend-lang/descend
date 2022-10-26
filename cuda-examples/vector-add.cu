    #include "descend.cuh"

template<std::size_t n>
auto inplace_vector_add(
        descend::i32 * const ha_array,
        const descend::i32 * const hb_array
) -> void {
    const auto gpu = descend::gpu_device(0);
    auto a_array = descend::gpu_alloc<descend::array<descend::i32, n>>(&gpu, &*ha_array);
    const auto b_array = descend::gpu_alloc<descend::array<descend::i32, n>>(&gpu, &*hb_array);
    descend::exec<64, 1024>(&gpu, [] __device__ (descend::i32 * const p0, const descend::i32 * const p1) -> void {
        p0[blockIdx.x * 1024 + threadIdx.x] = p0[blockIdx.x * 1024 + threadIdx.x] + p1[blockIdx.x * 1024 + threadIdx.x];
        __syncthreads();
    }, &a_array, &b_array);
    descend::copy_to_host<descend::array<descend::i32, n>>(&a_array, ha_array);
}


auto main() -> int {
    auto ha_array = descend::HeapBuffer<descend::array<descend::i32, 1*1024>>(descend::create_array<1024, descend::i32>(0));
    const auto hb_array = descend::HeapBuffer<descend::array<descend::i32, 1*1024>>(descend::create_array<1024, descend::i32>(1));
    inplace_vector_add<1*1024>(&ha_array, &hb_array);

    for (size_t i = 0; i < 1*1024; i++) {
        if (ha_array[i] != 1) {
            std::cout << "At i = " << i << "Wrong number. Found " << ha_array[i] << " instead of 1.";
            exit(EXIT_FAILURE);
        }
    }
    exit(EXIT_SUCCESS);
}
