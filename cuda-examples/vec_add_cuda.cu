#include "descend.cuh"

template <std::size_t n>
auto vec_add(descend::i32 *const vec_1, const descend::i32 *const vec_2) -> void {
  {
    auto gpu = descend::gpu_device(0);
    auto vec_1_arr = descend::gpu_alloc_copy<descend::array<descend::i32, n>>((&gpu), (&(*vec_1)));
    const auto vec_2_arr = descend::gpu_alloc_copy<descend::array<descend::i32, n>>((&gpu),(&(*vec_2)));
    descend::exec<32, 32>((&gpu), [] __device__(descend::i32 *const p0, const descend::i32 *const p1, std::size_t n) -> void {
                            {
                              {
                                {
                                  p0[((blockIdx.x * 32) + threadIdx.x)] = p0[((blockIdx.x * 32) + threadIdx.x)] + p1[((blockIdx.x * 32) + threadIdx.x)];
                                }
                              }
                            }
                          }, (&vec_1_arr), (&vec_2_arr), n);
    descend::copy_to_host<descend::array<descend::i32, n>>((&vec_1_arr), vec_1);
  }
}


auto main() -> int {
    auto ha_array = descend::HeapBuffer<descend::array<descend::i32, 32>>(descend::create_array<32, descend::i32>(1));
    const auto hb_array = descend::HeapBuffer<descend::array<descend::i32, 32>>(descend::create_array<32, descend::i32>(1));
//    int res [] = {4, 6, 8, 10, 12, 14};

//   '' printf("1. Summand: %i\n", a);
//    printf("2. Summand: %i\n", b);
//    printf("Erwartetes Ergebnis: %i\n", res);
//
    vec_add<32>(&ha_array, &hb_array);
//
//    printf("Echtes ergebnis: %i\n", a);''
    for (size_t i = 0; i < 32; i++) {
        if (ha_array[i] != 2) {
            std::cout << "At i = " << i << "Wrong number. Found " << ha_array[i] << " instead of 2.\n";
            exit(EXIT_FAILURE);
        }
    }
    std::cout << "Vector addition was successful!\n";
    exit(EXIT_SUCCESS);
}
