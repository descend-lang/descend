#include "descend.cuh"
template <std::size_t n>
auto bitonicsort(descend::i32 *const ha_array) -> void {
    {
        auto gpu = descend::gpu_device(0);
        auto a_array = descend::gpu_alloc_copy<descend::array<descend::i32, n>>(
                (&gpu), (&(*ha_array)));
        for (descend::i32 k = 1; k <= 2; k = k * 2) {
            for (descend::i32 j = (k / 2); j > 0; j = j / 2) {

                descend::exec<(n / (2 * 512)), 512>(
                        (&gpu),
                        [] __device__(descend::i32 *const p0) -> void {
                            {

                                if (blockIdx.x < k) {

                                    {

                                        if (p0[((((((((((blockIdx.x * s) + threadIdx.x) %
                                                       ((((n / j) * j) / 2) / (k / j))) *
                                                      s) +
                                                     (((blockIdx.x * s) + threadIdx.x) /
                                                      ((((n / j) * j) / 2) / (k / j)))) *
                                                    s) +
                                                   0) %
                                                  (n / j)) *
                                                 s) +
                                                ((((((((blockIdx.x * s) + threadIdx.x) %
                                                      ((((n / j) * j) / 2) / (k / j))) *
                                                     s) +
                                                    (((blockIdx.x * s) + threadIdx.x) /
                                                     ((((n / j) * j) / 2) / (k / j)))) *
                                                   s) +
                                                  0) /
                                                 (n / j)))] >
                                            p0[((((((((((blockIdx.x * s) + threadIdx.x) %
                                                       ((((n / j) * j) / 2) / (k / j))) *
                                                      s) +
                                                     (((blockIdx.x * s) + threadIdx.x) /
                                                      ((((n / j) * j) / 2) / (k / j)))) *
                                                    s) +
                                                   1) %
                                                  (n / j)) *
                                                 s) +
                                                ((((((((blockIdx.x * s) + threadIdx.x) %
                                                      ((((n / j) * j) / 2) / (k / j))) *
                                                     s) +
                                                    (((blockIdx.x * s) + threadIdx.x) /
                                                     ((((n / j) * j) / 2) / (k / j)))) *
                                                   s) +
                                                  1) /
                                                 (n / j)))]) {
                                            const auto temp =
                                                    p0[((((((((((blockIdx.x * s) + threadIdx.x) %
                                                               ((((n / j) * j) / 2) / (k / j))) *
                                                              s) +
                                                             (((blockIdx.x * s) + threadIdx.x) /
                                                              ((((n / j) * j) / 2) / (k / j)))) *
                                                            s) +
                                                           0) %
                                                          (n / j)) *
                                                         s) +
                                                        ((((((((blockIdx.x * s) + threadIdx.x) %
                                                              ((((n / j) * j) / 2) / (k / j))) *
                                                             s) +
                                                            (((blockIdx.x * s) + threadIdx.x) /
                                                             ((((n / j) * j) / 2) / (k / j)))) *
                                                           s) +
                                                          0) /
                                                         (n / j)))];
                                            p0[((((((((((blockIdx.x * s) + threadIdx.x) %
                                                       ((((n / j) * j) / 2) / (k / j))) *
                                                      s) +
                                                     (((blockIdx.x * s) + threadIdx.x) /
                                                      ((((n / j) * j) / 2) / (k / j)))) *
                                                    s) +
                                                   0) %
                                                  (n / j)) *
                                                 s) +
                                                ((((((((blockIdx.x * s) + threadIdx.x) %
                                                      ((((n / j) * j) / 2) / (k / j))) *
                                                     s) +
                                                    (((blockIdx.x * s) + threadIdx.x) /
                                                     ((((n / j) * j) / 2) / (k / j)))) *
                                                   s) +
                                                  0) /
                                                 (n / j)))] =
                                                    p0[((((((((((blockIdx.x * s) + threadIdx.x) %
                                                               ((((n / j) * j) / 2) / (k / j))) *
                                                              s) +
                                                             (((blockIdx.x * s) + threadIdx.x) /
                                                              ((((n / j) * j) / 2) / (k / j)))) *
                                                            s) +
                                                           1) %
                                                          (n / j)) *
                                                         s) +
                                                        ((((((((blockIdx.x * s) + threadIdx.x) %
                                                              ((((n / j) * j) / 2) / (k / j))) *
                                                             s) +
                                                            (((blockIdx.x * s) + threadIdx.x) /
                                                             ((((n / j) * j) / 2) / (k / j)))) *
                                                           s) +
                                                          1) /
                                                         (n / j)))];
                                            p0[((((((((((blockIdx.x * s) + threadIdx.x) %
                                                       ((((n / j) * j) / 2) / (k / j))) *
                                                      s) +
                                                     (((blockIdx.x * s) + threadIdx.x) /
                                                      ((((n / j) * j) / 2) / (k / j)))) *
                                                    s) +
                                                   1) %
                                                  (n / j)) *
                                                 s) +
                                                ((((((((blockIdx.x * s) + threadIdx.x) %
                                                      ((((n / j) * j) / 2) / (k / j))) *
                                                     s) +
                                                    (((blockIdx.x * s) + threadIdx.x) /
                                                     ((((n / j) * j) / 2) / (k / j)))) *
                                                   s) +
                                                  1) /
                                                 (n / j)))] = temp;
                                        }
                                    }
                                    __syncthreads();
                                }

                                if (k >= blockIdx.x) {

                                    {

                                        if (p0[((((((((((blockIdx.x * s) + threadIdx.x) %
                                                       ((((n / j) * j) / 2) / (k / j))) *
                                                      s) +
                                                     ((((blockIdx.x * s) + threadIdx.x) /
                                                       ((((n / j) * j) / 2) / (k / j))) +
                                                      (k / (2 * j)))) *
                                                    s) +
                                                   0) %
                                                  (n / j)) *
                                                 s) +
                                                ((((((((blockIdx.x * s) + threadIdx.x) %
                                                      ((((n / j) * j) / 2) / (k / j))) *
                                                     s) +
                                                    ((((blockIdx.x * s) + threadIdx.x) /
                                                      ((((n / j) * j) / 2) / (k / j))) +
                                                     (k / (2 * j)))) *
                                                   s) +
                                                  0) /
                                                 (n / j)))] <
                                            p0[((((((((((blockIdx.x * s) + threadIdx.x) %
                                                       ((((n / j) * j) / 2) / (k / j))) *
                                                      s) +
                                                     ((((blockIdx.x * s) + threadIdx.x) /
                                                       ((((n / j) * j) / 2) / (k / j))) +
                                                      (k / (2 * j)))) *
                                                    s) +
                                                   1) %
                                                  (n / j)) *
                                                 s) +
                                                ((((((((blockIdx.x * s) + threadIdx.x) %
                                                      ((((n / j) * j) / 2) / (k / j))) *
                                                     s) +
                                                    ((((blockIdx.x * s) + threadIdx.x) /
                                                      ((((n / j) * j) / 2) / (k / j))) +
                                                     (k / (2 * j)))) *
                                                   s) +
                                                  1) /
                                                 (n / j)))]) {
                                            const auto temp =
                                                    p0[((((((((((blockIdx.x * s) + threadIdx.x) %
                                                               ((((n / j) * j) / 2) / (k / j))) *
                                                              s) +
                                                             ((((blockIdx.x * s) + threadIdx.x) /
                                                               ((((n / j) * j) / 2) / (k / j))) +
                                                              (k / (2 * j)))) *
                                                            s) +
                                                           0) %
                                                          (n / j)) *
                                                         s) +
                                                        ((((((((blockIdx.x * s) + threadIdx.x) %
                                                              ((((n / j) * j) / 2) / (k / j))) *
                                                             s) +
                                                            ((((blockIdx.x * s) + threadIdx.x) /
                                                              ((((n / j) * j) / 2) / (k / j))) +
                                                             (k / (2 * j)))) *
                                                           s) +
                                                          0) /
                                                         (n / j)))];
                                            p0[((((((((((blockIdx.x * s) + threadIdx.x) %
                                                       ((((n / j) * j) / 2) / (k / j))) *
                                                      s) +
                                                     ((((blockIdx.x * s) + threadIdx.x) /
                                                       ((((n / j) * j) / 2) / (k / j))) +
                                                      (k / (2 * j)))) *
                                                    s) +
                                                   0) %
                                                  (n / j)) *
                                                 s) +
                                                ((((((((blockIdx.x * s) + threadIdx.x) %
                                                      ((((n / j) * j) / 2) / (k / j))) *
                                                     s) +
                                                    ((((blockIdx.x * s) + threadIdx.x) /
                                                      ((((n / j) * j) / 2) / (k / j))) +
                                                     (k / (2 * j)))) *
                                                   s) +
                                                  0) /
                                                 (n / j)))] =
                                                    p0[((((((((((blockIdx.x * s) + threadIdx.x) %
                                                               ((((n / j) * j) / 2) / (k / j))) *
                                                              s) +
                                                             ((((blockIdx.x * s) + threadIdx.x) /
                                                               ((((n / j) * j) / 2) / (k / j))) +
                                                              (k / (2 * j)))) *
                                                            s) +
                                                           1) %
                                                          (n / j)) *
                                                         s) +
                                                        ((((((((blockIdx.x * s) + threadIdx.x) %
                                                              ((((n / j) * j) / 2) / (k / j))) *
                                                             s) +
                                                            ((((blockIdx.x * s) + threadIdx.x) /
                                                              ((((n / j) * j) / 2) / (k / j))) +
                                                             (k / (2 * j)))) *
                                                           s) +
                                                          1) /
                                                         (n / j)))];
                                            p0[((((((((((blockIdx.x * s) + threadIdx.x) %
                                                       ((((n / j) * j) / 2) / (k / j))) *
                                                      s) +
                                                     ((((blockIdx.x * s) + threadIdx.x) /
                                                       ((((n / j) * j) / 2) / (k / j))) +
                                                      (k / (2 * j)))) *
                                                    s) +
                                                   1) %
                                                  (n / j)) *
                                                 s) +
                                                ((((((((blockIdx.x * s) + threadIdx.x) %
                                                      ((((n / j) * j) / 2) / (k / j))) *
                                                     s) +
                                                    ((((blockIdx.x * s) + threadIdx.x) /
                                                      ((((n / j) * j) / 2) / (k / j))) +
                                                     (k / (2 * j)))) *
                                                   s) +
                                                  1) /
                                                 (n / j)))] = temp;
                                        }
                                    }
                                    __syncthreads();
                                }
                            }
                        },
                        (&a_array));
            }
        }
        for (descend::i32 j = (n / 2); j > 0; j = j / 2) {

            descend::exec<(n / (2 * 512)), 512>(
                    (&gpu),
                    [] __device__(descend::i32 *const p0) -> void {
                        {

                            {

                                {

                                    if (p0[(((((((blockIdx.x * s) + threadIdx.x) * s) + 0) %
                                              (n / j)) *
                                             s) +
                                            (((((blockIdx.x * s) + threadIdx.x) * s) + 0) /
                                             (n / j)))] >
                                        p0[(((((((blockIdx.x * s) + threadIdx.x) * s) + 1) %
                                              (n / j)) *
                                             s) +
                                            (((((blockIdx.x * s) + threadIdx.x) * s) + 1) /
                                             (n / j)))]) {
                                        const auto temp =
                                                p0[(((((((blockIdx.x * s) + threadIdx.x) * s) + 0) %
                                                      (n / j)) *
                                                     s) +
                                                    (((((blockIdx.x * s) + threadIdx.x) * s) + 0) /
                                                     (n / j)))];
                                        p0[(((((((blockIdx.x * s) + threadIdx.x) * s) + 0) %
                                              (n / j)) *
                                             s) +
                                            (((((blockIdx.x * s) + threadIdx.x) * s) + 0) /
                                             (n / j)))] =
                                                p0[(((((((blockIdx.x * s) + threadIdx.x) * s) + 1) %
                                                      (n / j)) *
                                                     s) +
                                                    (((((blockIdx.x * s) + threadIdx.x) * s) + 1) /
                                                     (n / j)))];
                                        p0[(((((((blockIdx.x * s) + threadIdx.x) * s) + 1) %
                                              (n / j)) *
                                             s) +
                                            (((((blockIdx.x * s) + threadIdx.x) * s) + 1) /
                                             (n / j)))] = temp;
                                    }
                                }
                                __syncthreads();
                            }
                        }
                    },
                    (&a_array));
        }
        descend::copy_to_host<descend::array<descend::i32, n>>((&a_array),
                                                               ha_array);
    }
}


auto main() -> int {
    const auto NUM_RUNS = 10;
    const auto NUM_VALS = 65536;

    auto gold = descend::HeapBuffer<descend::array<descend::i32, NUM_VALS>>(1);
    for (int i = 0; i < NUM_VALS; i++){
        gold[i] = i;
    }

    for (int run = 0; run < NUM_RUNS; run++){
        auto ha_array = descend::HeapBuffer<descend::array<descend::i32, NUM_VALS>>(1);
        for (int i = 0; i < NUM_VALS; i ++){
            ha_array[i] = i ^ run;
        }
        bitonicsort<>(&ha_array);
        for (int i = 0; i < NUM_VALS; i++){
            if (ha_array[i] != gold[i]){
                std::cout << "Error at " << i << ": Expected `" << gold[i]
                          << "` but found `" << ha_array[i] << "`" << std::endl;
                std::cout << "Next 10 lines:" << std::endl;
                for (int j = i; j < i + 10; j++)
                    std::cout << "Expected: " << gold[j] << " Found: " << ha_array[i] << std::endl;
                exit(EXIT_FAILURE);
            }
        }
    }
}


