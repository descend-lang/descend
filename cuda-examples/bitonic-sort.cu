#include "descend.cuh"
#include <time.h>
#include <stdlib.h>
#include <algorithm>
template <std::size_t n>
auto bitonicsort(descend::i32 *const ha_array) -> void {
    {
        auto gpu = descend::gpu_device(0);
        auto a_array = descend::gpu_alloc_copy<descend::array<descend::i32, n>>(
                (&gpu), (&(*ha_array)));
        for (std::size_t k = 2; k <= (n / 2); k = k * 2) {
            for (std::size_t j = (k / 2); j > 0; j = j / 2) {

                descend::exec<(n / (2 * 512)), 512>(
                        (&gpu),
                        [] __device__(descend::i32 *const p0, std::size_t j, std::size_t k,
                                      std::size_t n) -> void {
                            {

                                if (blockIdx.x < (n / (4 * 512))) {

                                    {

                                        if (p0[((((((((((blockIdx.x * 512) + threadIdx.x) %
                                                       ((((n / j) * j) / 2) / (k / j))) *
                                                      (k / j)) +
                                                     (((blockIdx.x * 512) + threadIdx.x) /
                                                      ((((n / j) * j) / 2) / (k / j)))) *
                                                    2) +
                                                   0) %
                                                  (n / j)) *
                                                 j) +
                                                ((((((((blockIdx.x * 512) + threadIdx.x) %
                                                      ((((n / j) * j) / 2) / (k / j))) *
                                                     (k / j)) +
                                                    (((blockIdx.x * 512) + threadIdx.x) /
                                                     ((((n / j) * j) / 2) / (k / j)))) *
                                                   2) +
                                                  0) /
                                                 (n / j)))] >
                                            p0[((((((((((blockIdx.x * 512) + threadIdx.x) %
                                                       ((((n / j) * j) / 2) / (k / j))) *
                                                      (k / j)) +
                                                     (((blockIdx.x * 512) + threadIdx.x) /
                                                      ((((n / j) * j) / 2) / (k / j)))) *
                                                    2) +
                                                   1) %
                                                  (n / j)) *
                                                 j) +
                                                ((((((((blockIdx.x * 512) + threadIdx.x) %
                                                      ((((n / j) * j) / 2) / (k / j))) *
                                                     (k / j)) +
                                                    (((blockIdx.x * 512) + threadIdx.x) /
                                                     ((((n / j) * j) / 2) / (k / j)))) *
                                                   2) +
                                                  1) /
                                                 (n / j)))]) {
                                            const auto temp =
                                                    p0[((((((((((blockIdx.x * 512) + threadIdx.x) %
                                                               ((((n / j) * j) / 2) / (k / j))) *
                                                              (k / j)) +
                                                             (((blockIdx.x * 512) + threadIdx.x) /
                                                              ((((n / j) * j) / 2) / (k / j)))) *
                                                            2) +
                                                           0) %
                                                          (n / j)) *
                                                         j) +
                                                        ((((((((blockIdx.x * 512) + threadIdx.x) %
                                                              ((((n / j) * j) / 2) / (k / j))) *
                                                             (k / j)) +
                                                            (((blockIdx.x * 512) + threadIdx.x) /
                                                             ((((n / j) * j) / 2) / (k / j)))) *
                                                           2) +
                                                          0) /
                                                         (n / j)))];
                                            p0[((((((((((blockIdx.x * 512) + threadIdx.x) %
                                                       ((((n / j) * j) / 2) / (k / j))) *
                                                      (k / j)) +
                                                     (((blockIdx.x * 512) + threadIdx.x) /
                                                      ((((n / j) * j) / 2) / (k / j)))) *
                                                    2) +
                                                   0) %
                                                  (n / j)) *
                                                 j) +
                                                ((((((((blockIdx.x * 512) + threadIdx.x) %
                                                      ((((n / j) * j) / 2) / (k / j))) *
                                                     (k / j)) +
                                                    (((blockIdx.x * 512) + threadIdx.x) /
                                                     ((((n / j) * j) / 2) / (k / j)))) *
                                                   2) +
                                                  0) /
                                                 (n / j)))] =
                                                    p0[((((((((((blockIdx.x * 512) + threadIdx.x) %
                                                               ((((n / j) * j) / 2) / (k / j))) *
                                                              (k / j)) +
                                                             (((blockIdx.x * 512) + threadIdx.x) /
                                                              ((((n / j) * j) / 2) / (k / j)))) *
                                                            2) +
                                                           1) %
                                                          (n / j)) *
                                                         j) +
                                                        ((((((((blockIdx.x * 512) + threadIdx.x) %
                                                              ((((n / j) * j) / 2) / (k / j))) *
                                                             (k / j)) +
                                                            (((blockIdx.x * 512) + threadIdx.x) /
                                                             ((((n / j) * j) / 2) / (k / j)))) *
                                                           2) +
                                                          1) /
                                                         (n / j)))];
                                            p0[((((((((((blockIdx.x * 512) + threadIdx.x) %
                                                       ((((n / j) * j) / 2) / (k / j))) *
                                                      (k / j)) +
                                                     (((blockIdx.x * 512) + threadIdx.x) /
                                                      ((((n / j) * j) / 2) / (k / j)))) *
                                                    2) +
                                                   1) %
                                                  (n / j)) *
                                                 j) +
                                                ((((((((blockIdx.x * 512) + threadIdx.x) %
                                                      ((((n / j) * j) / 2) / (k / j))) *
                                                     (k / j)) +
                                                    (((blockIdx.x * 512) + threadIdx.x) /
                                                     ((((n / j) * j) / 2) / (k / j)))) *
                                                   2) +
                                                  1) /
                                                 (n / j)))] = temp;
                                        }
                                    }
                                    __syncthreads();
                                }

                                if ((n / (4 * 512)) <= blockIdx.x) {

                                    {

                                        if (p0[((((((((((blockIdx.x * 512) + threadIdx.x) %
                                                       ((((n / j) * j) / 2) / (k / j))) *
                                                      (k / j)) +
                                                     (((blockIdx.x * 512) + threadIdx.x) /
                                                      ((((n / j) * j) / 2) / (k / j)))) *
                                                    2) +
                                                   0) %
                                                  (n / j)) *
                                                 j) +
                                                ((((((((blockIdx.x * 512) + threadIdx.x) %
                                                      ((((n / j) * j) / 2) / (k / j))) *
                                                     (k / j)) +
                                                    (((blockIdx.x * 512) + threadIdx.x) /
                                                     ((((n / j) * j) / 2) / (k / j)))) *
                                                   2) +
                                                  0) /
                                                 (n / j)))] <
                                            p0[((((((((((blockIdx.x * 512) + threadIdx.x) %
                                                       ((((n / j) * j) / 2) / (k / j))) *
                                                      (k / j)) +
                                                     (((blockIdx.x * 512) + threadIdx.x) /
                                                      ((((n / j) * j) / 2) / (k / j)))) *
                                                    2) +
                                                   1) %
                                                  (n / j)) *
                                                 j) +
                                                ((((((((blockIdx.x * 512) + threadIdx.x) %
                                                      ((((n / j) * j) / 2) / (k / j))) *
                                                     (k / j)) +
                                                    (((blockIdx.x * 512) + threadIdx.x) /
                                                     ((((n / j) * j) / 2) / (k / j)))) *
                                                   2) +
                                                  1) /
                                                 (n / j)))]) {
                                            const auto temp =
                                                    p0[((((((((((blockIdx.x * 512) + threadIdx.x) %
                                                               ((((n / j) * j) / 2) / (k / j))) *
                                                              (k / j)) +
                                                             (((blockIdx.x * 512) + threadIdx.x) /
                                                              ((((n / j) * j) / 2) / (k / j)))) *
                                                            2) +
                                                           0) %
                                                          (n / j)) *
                                                         j) +
                                                        ((((((((blockIdx.x * 512) + threadIdx.x) %
                                                              ((((n / j) * j) / 2) / (k / j))) *
                                                             (k / j)) +
                                                            (((blockIdx.x * 512) + threadIdx.x) /
                                                             ((((n / j) * j) / 2) / (k / j)))) *
                                                           2) +
                                                          0) /
                                                         (n / j)))];
                                            p0[((((((((((blockIdx.x * 512) + threadIdx.x) %
                                                       ((((n / j) * j) / 2) / (k / j))) *
                                                      (k / j)) +
                                                     (((blockIdx.x * 512) + threadIdx.x) /
                                                      ((((n / j) * j) / 2) / (k / j)))) *
                                                    2) +
                                                   0) %
                                                  (n / j)) *
                                                 j) +
                                                ((((((((blockIdx.x * 512) + threadIdx.x) %
                                                      ((((n / j) * j) / 2) / (k / j))) *
                                                     (k / j)) +
                                                    (((blockIdx.x * 512) + threadIdx.x) /
                                                     ((((n / j) * j) / 2) / (k / j)))) *
                                                   2) +
                                                  0) /
                                                 (n / j)))] =
                                                    p0[((((((((((blockIdx.x * 512) + threadIdx.x) %
                                                               ((((n / j) * j) / 2) / (k / j))) *
                                                              (k / j)) +
                                                             (((blockIdx.x * 512) + threadIdx.x) /
                                                              ((((n / j) * j) / 2) / (k / j)))) *
                                                            2) +
                                                           1) %
                                                          (n / j)) *
                                                         j) +
                                                        ((((((((blockIdx.x * 512) + threadIdx.x) %
                                                              ((((n / j) * j) / 2) / (k / j))) *
                                                             (k / j)) +
                                                            (((blockIdx.x * 512) + threadIdx.x) /
                                                             ((((n / j) * j) / 2) / (k / j)))) *
                                                           2) +
                                                          1) /
                                                         (n / j)))];
                                            p0[((((((((((blockIdx.x * 512) + threadIdx.x) %
                                                       ((((n / j) * j) / 2) / (k / j))) *
                                                      (k / j)) +
                                                     (((blockIdx.x * 512) + threadIdx.x) /
                                                      ((((n / j) * j) / 2) / (k / j)))) *
                                                    2) +
                                                   1) %
                                                  (n / j)) *
                                                 j) +
                                                ((((((((blockIdx.x * 512) + threadIdx.x) %
                                                      ((((n / j) * j) / 2) / (k / j))) *
                                                     (k / j)) +
                                                    (((blockIdx.x * 512) + threadIdx.x) /
                                                     ((((n / j) * j) / 2) / (k / j)))) *
                                                   2) +
                                                  1) /
                                                 (n / j)))] = temp;
                                        }
                                    }
                                    __syncthreads();
                                }
                            }
                        },
                        (&a_array), j, k, n);
            }
        }
        for (std::size_t j = (n / 2); j > 0; j = j / 2) {

            descend::exec<(n / (2 * 512)), 512>(
                    (&gpu),
                    [] __device__(descend::i32 *const p0, std::size_t n,
                                  std::size_t j) -> void {
                        {

                            {

                                {

                                    if (p0[(((((((blockIdx.x * 512) + threadIdx.x) * 2) + 0) %
                                              (n / j)) *
                                             j) +
                                            (((((blockIdx.x * 512) + threadIdx.x) * 2) + 0) /
                                             (n / j)))] >
                                        p0[(((((((blockIdx.x * 512) + threadIdx.x) * 2) + 1) %
                                              (n / j)) *
                                             j) +
                                            (((((blockIdx.x * 512) + threadIdx.x) * 2) + 1) /
                                             (n / j)))]) {
                                        const auto temp =
                                                p0[(((((((blockIdx.x * 512) + threadIdx.x) * 2) + 0) %
                                                      (n / j)) *
                                                     j) +
                                                    (((((blockIdx.x * 512) + threadIdx.x) * 2) + 0) /
                                                     (n / j)))];
                                        p0[(((((((blockIdx.x * 512) + threadIdx.x) * 2) + 0) %
                                              (n / j)) *
                                             j) +
                                            (((((blockIdx.x * 512) + threadIdx.x) * 2) + 0) /
                                             (n / j)))] =
                                                p0[(((((((blockIdx.x * 512) + threadIdx.x) * 2) + 1) %
                                                      (n / j)) *
                                                     j) +
                                                    (((((blockIdx.x * 512) + threadIdx.x) * 2) + 1) /
                                                     (n / j)))];
                                        p0[(((((((blockIdx.x * 512) + threadIdx.x) * 2) + 1) %
                                              (n / j)) *
                                             j) +
                                            (((((blockIdx.x * 512) + threadIdx.x) * 2) + 1) /
                                             (n / j)))] = temp;
                                    }
                                }
                                __syncthreads();
                            }
                        }
                    },
                    (&a_array), n, j);
        }
        descend::copy_to_host<descend::array<descend::i32, n>>((&a_array),
                                                               ha_array);
    }
}





auto main() -> int {
    const int NUM_RUNS = 10;
    const int NUM_VALS = 4096;
    srand(time(NULL));

    std::cout << "begin computation" << std::endl;
    int* gold = (int*)malloc(NUM_VALS*sizeof(int));
    for (int run = 0; run < NUM_RUNS; run++){
        auto ha_array = descend::HeapBuffer<descend::array<descend::i32, NUM_VALS>>(1);
        for ( int i = 0; i < NUM_VALS; i ++){
            int r = rand();
            ha_array[i] = r;
        }
       for (int i = 0; i < NUM_VALS; i++){
            gold[i] = ha_array[i];
        }
        std::sort(gold, gold+NUM_VALS);
        bitonicsort<NUM_VALS>(&ha_array);
        for (int i = 0; i < NUM_VALS; i++){
            if (ha_array[i] != gold[i]){
                std::cout << "Error at " << i << ": Expected `" << gold[i]
                          << "` but found `" << ha_array[i] << "`" << std::endl;
                std::cout << "Next 10 lines:" << std::endl;
                for (int j = i; j < i + 10; j++)
                    std::cout << "Expected: " << gold[j] << " Found: " << ha_array[j] << std::endl;
                exit(EXIT_FAILURE);
            }
            //std::cout << "@" << i << ": " << ha_array[i]  << std::endl;
        }
    }
    free(gold);
    std::cout << "success" << std::endl;
}


