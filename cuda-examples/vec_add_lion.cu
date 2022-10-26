#include <cuda.h>
#include <stdio.h>
#include "descend.cuh"

extern void vec_add(descend::f64 *const vec_1, const descend::f64 *const vec_2);

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