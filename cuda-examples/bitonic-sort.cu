#define BENCH
#include "descend.cuh"
#include <time.h>
#include <stdlib.h>
#include <algorithm>
const int NUM_VALS = 4096; // Number elements to sort
const int NUM_KERNEL = 78; // Number Kernels to start

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
                        [] __device__(descend::i32 *const p0, std::size_t k, std::size_t j,
                                      std::size_t n) -> void {
                            {

                                if (blockIdx.x < (n / (4 * 512))) {

                                    {

                                        if (p0[((((((((((blockIdx.x - 0) * 512) + threadIdx.x) %
                                                      ((n / 2) / (k / j))) *
                                                     (k / j)) +
                                                    ((((blockIdx.x - 0) * 512) + threadIdx.x) /
                                                     ((n / 2) / (k / j)))) *
                                                   2) %
                                                  (n / j)) *
                                                 j) +
                                                ((((((((blockIdx.x - 0) * 512) + threadIdx.x) %
                                                     ((n / 2) / (k / j))) *
                                                    (k / j)) +
                                                   ((((blockIdx.x - 0) * 512) + threadIdx.x) /
                                                    ((n / 2) / (k / j)))) *
                                                  2) /
                                                 (n / j)))] >
                                            p0[(((((((((((blockIdx.x - 0) * 512) + threadIdx.x) %
                                                       ((n / 2) / (k / j))) *
                                                      (k / j)) +
                                                     ((((blockIdx.x - 0) * 512) + threadIdx.x) /
                                                      ((n / 2) / (k / j)))) *
                                                    2) +
                                                   1) %
                                                  (n / j)) *
                                                 j) +
                                                (((((((((blockIdx.x - 0) * 512) + threadIdx.x) %
                                                      ((n / 2) / (k / j))) *
                                                     (k / j)) +
                                                    ((((blockIdx.x - 0) * 512) + threadIdx.x) /
                                                     ((n / 2) / (k / j)))) *
                                                   2) +
                                                  1) /
                                                 (n / j)))]) {
                                            const auto temp =
                                                    p0[((((((((((blockIdx.x - 0) * 512) + threadIdx.x) %
                                                              ((n / 2) / (k / j))) *
                                                             (k / j)) +
                                                            ((((blockIdx.x - 0) * 512) + threadIdx.x) /
                                                             ((n / 2) / (k / j)))) *
                                                           2) %
                                                          (n / j)) *
                                                         j) +
                                                        ((((((((blockIdx.x - 0) * 512) + threadIdx.x) %
                                                             ((n / 2) / (k / j))) *
                                                            (k / j)) +
                                                           ((((blockIdx.x - 0) * 512) + threadIdx.x) /
                                                            ((n / 2) / (k / j)))) *
                                                          2) /
                                                         (n / j)))];
                                            p0[((((((((((blockIdx.x - 0) * 512) + threadIdx.x) %
                                                      ((n / 2) / (k / j))) *
                                                     (k / j)) +
                                                    ((((blockIdx.x - 0) * 512) + threadIdx.x) /
                                                     ((n / 2) / (k / j)))) *
                                                   2) %
                                                  (n / j)) *
                                                 j) +
                                                ((((((((blockIdx.x - 0) * 512) + threadIdx.x) %
                                                     ((n / 2) / (k / j))) *
                                                    (k / j)) +
                                                   ((((blockIdx.x - 0) * 512) + threadIdx.x) /
                                                    ((n / 2) / (k / j)))) *
                                                  2) /
                                                 (n / j)))] =
                                                    p0[(((((((((((blockIdx.x - 0) * 512) + threadIdx.x) %
                                                               ((n / 2) / (k / j))) *
                                                              (k / j)) +
                                                             ((((blockIdx.x - 0) * 512) + threadIdx.x) /
                                                              ((n / 2) / (k / j)))) *
                                                            2) +
                                                           1) %
                                                          (n / j)) *
                                                         j) +
                                                        (((((((((blockIdx.x - 0) * 512) + threadIdx.x) %
                                                              ((n / 2) / (k / j))) *
                                                             (k / j)) +
                                                            ((((blockIdx.x - 0) * 512) + threadIdx.x) /
                                                             ((n / 2) / (k / j)))) *
                                                           2) +
                                                          1) /
                                                         (n / j)))];
                                            p0[(((((((((((blockIdx.x - 0) * 512) + threadIdx.x) %
                                                       ((n / 2) / (k / j))) *
                                                      (k / j)) +
                                                     ((((blockIdx.x - 0) * 512) + threadIdx.x) /
                                                      ((n / 2) / (k / j)))) *
                                                    2) +
                                                   1) %
                                                  (n / j)) *
                                                 j) +
                                                (((((((((blockIdx.x - 0) * 512) + threadIdx.x) %
                                                      ((n / 2) / (k / j))) *
                                                     (k / j)) +
                                                    ((((blockIdx.x - 0) * 512) + threadIdx.x) /
                                                     ((n / 2) / (k / j)))) *
                                                   2) +
                                                  1) /
                                                 (n / j)))] = temp;
                                        }
                                    }
                                    __syncthreads();
                                }

                                if (blockIdx.x >= (n / (4 * 512))) {

                                    {

                                        if (p0[((((((((((blockIdx.x - (n / (4 * 512))) * 512) +
                                                       threadIdx.x) %
                                                      ((n / 2) / (k / j))) *
                                                     (k / j)) +
                                                    (((((blockIdx.x - (n / (4 * 512))) * 512) +
                                                       threadIdx.x) /
                                                      ((n / 2) / (k / j))) +
                                                     (k / (2 * j)))) *
                                                   2) %
                                                  (n / j)) *
                                                 j) +
                                                ((((((((blockIdx.x - (n / (4 * 512))) * 512) +
                                                      threadIdx.x) %
                                                     ((n / 2) / (k / j))) *
                                                    (k / j)) +
                                                   (((((blockIdx.x - (n / (4 * 512))) * 512) +
                                                      threadIdx.x) /
                                                     ((n / 2) / (k / j))) +
                                                    (k / (2 * j)))) *
                                                  2) /
                                                 (n / j)))] <
                                            p0[(((((((((((blockIdx.x - (n / (4 * 512))) * 512) +
                                                        threadIdx.x) %
                                                       ((n / 2) / (k / j))) *
                                                      (k / j)) +
                                                     (((((blockIdx.x - (n / (4 * 512))) * 512) +
                                                        threadIdx.x) /
                                                       ((n / 2) / (k / j))) +
                                                      (k / (2 * j)))) *
                                                    2) +
                                                   1) %
                                                  (n / j)) *
                                                 j) +
                                                (((((((((blockIdx.x - (n / (4 * 512))) * 512) +
                                                       threadIdx.x) %
                                                      ((n / 2) / (k / j))) *
                                                     (k / j)) +
                                                    (((((blockIdx.x - (n / (4 * 512))) * 512) +
                                                       threadIdx.x) /
                                                      ((n / 2) / (k / j))) +
                                                     (k / (2 * j)))) *
                                                   2) +
                                                  1) /
                                                 (n / j)))]) {
                                            const auto temp =
                                                    p0[((((((((((blockIdx.x - (n / (4 * 512))) * 512) +
                                                               threadIdx.x) %
                                                              ((n / 2) / (k / j))) *
                                                             (k / j)) +
                                                            (((((blockIdx.x - (n / (4 * 512))) * 512) +
                                                               threadIdx.x) /
                                                              ((n / 2) / (k / j))) +
                                                             (k / (2 * j)))) *
                                                           2) %
                                                          (n / j)) *
                                                         j) +
                                                        ((((((((blockIdx.x - (n / (4 * 512))) * 512) +
                                                              threadIdx.x) %
                                                             ((n / 2) / (k / j))) *
                                                            (k / j)) +
                                                           (((((blockIdx.x - (n / (4 * 512))) * 512) +
                                                              threadIdx.x) /
                                                             ((n / 2) / (k / j))) +
                                                            (k / (2 * j)))) *
                                                          2) /
                                                         (n / j)))];
                                            p0[((((((((((blockIdx.x - (n / (4 * 512))) * 512) +
                                                       threadIdx.x) %
                                                      ((n / 2) / (k / j))) *
                                                     (k / j)) +
                                                    (((((blockIdx.x - (n / (4 * 512))) * 512) +
                                                       threadIdx.x) /
                                                      ((n / 2) / (k / j))) +
                                                     (k / (2 * j)))) *
                                                   2) %
                                                  (n / j)) *
                                                 j) +
                                                ((((((((blockIdx.x - (n / (4 * 512))) * 512) +
                                                      threadIdx.x) %
                                                     ((n / 2) / (k / j))) *
                                                    (k / j)) +
                                                   (((((blockIdx.x - (n / (4 * 512))) * 512) +
                                                      threadIdx.x) /
                                                     ((n / 2) / (k / j))) +
                                                    (k / (2 * j)))) *
                                                  2) /
                                                 (n / j)))] =
                                                    p0[(((((((((((blockIdx.x - (n / (4 * 512))) * 512) +
                                                                threadIdx.x) %
                                                               ((n / 2) / (k / j))) *
                                                              (k / j)) +
                                                             (((((blockIdx.x - (n / (4 * 512))) * 512) +
                                                                threadIdx.x) /
                                                               ((n / 2) / (k / j))) +
                                                              (k / (2 * j)))) *
                                                            2) +
                                                           1) %
                                                          (n / j)) *
                                                         j) +
                                                        (((((((((blockIdx.x - (n / (4 * 512))) * 512) +
                                                               threadIdx.x) %
                                                              ((n / 2) / (k / j))) *
                                                             (k / j)) +
                                                            (((((blockIdx.x - (n / (4 * 512))) * 512) +
                                                               threadIdx.x) /
                                                              ((n / 2) / (k / j))) +
                                                             (k / (2 * j)))) *
                                                           2) +
                                                          1) /
                                                         (n / j)))];
                                            p0[(((((((((((blockIdx.x - (n / (4 * 512))) * 512) +
                                                        threadIdx.x) %
                                                       ((n / 2) / (k / j))) *
                                                      (k / j)) +
                                                     (((((blockIdx.x - (n / (4 * 512))) * 512) +
                                                        threadIdx.x) /
                                                       ((n / 2) / (k / j))) +
                                                      (k / (2 * j)))) *
                                                    2) +
                                                   1) %
                                                  (n / j)) *
                                                 j) +
                                                (((((((((blockIdx.x - (n / (4 * 512))) * 512) +
                                                       threadIdx.x) %
                                                      ((n / 2) / (k / j))) *
                                                     (k / j)) +
                                                    (((((blockIdx.x - (n / (4 * 512))) * 512) +
                                                       threadIdx.x) /
                                                      ((n / 2) / (k / j))) +
                                                     (k / (2 * j)))) *
                                                   2) +
                                                  1) /
                                                 (n / j)))] = temp;
                                        }
                                    }
                                    __syncthreads();
                                }
                            }
                        },
                        (&a_array), k, j, n);
            }
        }
        for (std::size_t j = (n / 2); j > 0; j = j / 2) {

            descend::exec<(n / (2 * 512)), 512>(
                    (&gpu),
                    [] __device__(descend::i32 *const p0, std::size_t j,
                                  std::size_t n) -> void {
                        {

                            {

                                {

                                    if (p0[((((((blockIdx.x * 512) + threadIdx.x) * 2) %
                                              (n / j)) *
                                             j) +
                                            ((((blockIdx.x * 512) + threadIdx.x) * 2) /
                                             (n / j)))] >
                                        p0[(((((((blockIdx.x * 512) + threadIdx.x) * 2) + 1) %
                                              (n / j)) *
                                             j) +
                                            (((((blockIdx.x * 512) + threadIdx.x) * 2) + 1) /
                                             (n / j)))]) {
                                        const auto temp = p0[(
                                                (((((blockIdx.x * 512) + threadIdx.x) * 2) % (n / j)) *
                                                 j) +
                                                ((((blockIdx.x * 512) + threadIdx.x) * 2) / (n / j)))];
                                        p0[((((((blockIdx.x * 512) + threadIdx.x) * 2) % (n / j)) *
                                             j) +
                                            ((((blockIdx.x * 512) + threadIdx.x) * 2) / (n / j)))] =
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
                    (&a_array), j, n);
        }
        descend::copy_to_host<descend::array<descend::i32, n>>((&a_array),
                                                               ha_array);
    }
}






descend::Benchmark benchmark{descend::BenchConfig(NUM_KERNEL)};
auto main() -> int {
    const int NUM_RUNS = 10;

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
    std::cout << benchmark.avg_to_csv();
}


