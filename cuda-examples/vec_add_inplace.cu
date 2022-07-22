#include "descend.cuh"
template <std::size_t n>
auto vec_add_inplace(descend::f64 *const h_vec_a,
                     const descend::f64 *const h_vec_b) -> void {
    {
        auto gpu = descend::gpu_device(0);
        auto a_array = descend::gpu_alloc_copy<descend::array<descend::f64, n>>(
                (&gpu), (&(*h_vec_a)));
        const auto b_array =
                descend::gpu_alloc_copy<descend::array<descend::f64, n>>((&gpu),
                                                                         (&(*h_vec_b)));
        descend::exec<64, 1024>(
                (&gpu),
                [] __device__(descend::f64 *const p0, const descend::f64 *const p1,
                              std::size_t n) -> void {
                    {

                        {

                            {
                                p0[((blockIdx.x * 1024) + threadIdx.x)] =
                                        p0[((blockIdx.x * 1024) + threadIdx.x)] +
                                        p1[((blockIdx.x * 1024) + threadIdx.x)];
                            }
                        }
                    }
                },
                (&a_array), (&b_array), n);
        descend::copy_to_host<descend::array<descend::f64, n>>((&a_array), h_vec_a);
    }
};

auto main() -> int {
    auto ha_array = descend::HeapBuffer<descend::array<descend::f64, 64*1024>>(descend::create_array<64*1024, descend::f64>(0));
    const auto hb_array = descend::HeapBuffer<descend::array<descend::f64, 64*1024>>(descend::create_array<64*1024, descend::f64>(1));
    vec_add_inplace<64*1024>(&ha_array, &hb_array);

    for (size_t i = 0; i < 64*1024; i++) {
        if (ha_array[i] != 1) {
            std::cout << "At i = " << i << "Wrong number. Found " << ha_array[i] << " instead of 1.";
            exit(EXIT_FAILURE);
        }
    }
    exit(EXIT_SUCCESS);
}