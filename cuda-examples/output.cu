#include "descend.cuh"
template <std::size_t g_size, std::size_t b_size, std::size_t t_size>
auto prefix_scan(descend::i32 *const cpu_i_array,
                 descend::i32 *const cpu_flag_array,
                 descend::i32 *const cpu_agg_array,
                 descend::i32 *const cpu_prefix_array) -> void {
  {
    auto gpu = descend::gpu_device(0);
    auto g_i = descend::gpu_alloc_copy<
        descend::array<descend::i32, ((g_size * b_size) * t_size)>>(
        (&gpu), (&(*cpu_i_array)));
    auto g_flags =
        descend::gpu_alloc_copy<descend::array<descend::i32, g_size>>(
            (&gpu), (&(*cpu_flag_array)));
    auto g_aggs = descend::gpu_alloc_copy<descend::array<descend::i32, g_size>>(
        (&gpu), (&(*cpu_agg_array)));
    auto g_prefixs =
        descend::gpu_alloc_copy<descend::array<descend::i32, g_size>>(
            (&gpu), (&(*cpu_prefix_array)));
    descend::exec<g_size, b_size>(
        (&gpu),
        [] __device__(descend::i32 *const p0, descend::i32 *const p1,
                      descend::i32 *const p2, descend::i32 *const p3) -> void {
          {
            const auto gi_i = p0;
            const auto gi_flags = p1;
            const auto gi_aggs = p2;
            const auto gi_prefixs = p3;

            __shared__ descend::i32 shared_input[(b_size * t_size)];
            __shared__ descend::i32 shared_input_bkp[(b_size * t_size)];
            __shared__ descend::i32 result_reduction[b_size];
            __shared__ descend::i32 exclusive_prefix[1];
            __shared__ descend::i32 last_value[1];
            {

              {
                for (std::size_t k = 0; k < t_size; k = k + 1) {
                  shared_input[((threadIdx.x * t_size) + k)] =
                      gi_i[((blockIdx.x * (b_size * t_size)) +
                            ((threadIdx.x * t_size) + k))];
                }
                for (std::size_t k = 0; k < t_size; k = k + 1) {
                  shared_input_bkp[((threadIdx.x * t_size) + k)] =
                      gi_i[((blockIdx.x * (b_size * t_size)) +
                            ((threadIdx.x * t_size) + k))];
                }
              }
              __syncthreads();

              {
                result_reduction[threadIdx.x] = 0;
                for (std::size_t k = 0; k < t_size; k = k + 1) {
                  result_reduction[threadIdx.x] =
                      result_reduction[threadIdx.x] +
                      shared_input[((threadIdx.x * t_size) + k)];
                }
              }
              __syncthreads();
              for (std::size_t k = (b_size / 2); k > 0; k = k / 2) {

                if (threadIdx.x < k) {
                  result_reduction[(threadIdx.x - 0)] =
                      result_reduction[(threadIdx.x - 0)] +
                      result_reduction[((threadIdx.x - 0) + k)];
                }
                __syncthreads();
              }

              if (threadIdx.x < 1) {
                gi_aggs[((blockIdx.x * 1) + (threadIdx.x - 0))] =
                    result_reduction[(threadIdx.x - 0)];
              }
              __syncthreads();

              if (threadIdx.x < 1) {
                gi_flags[((blockIdx.x * 1) + (threadIdx.x - 0))] = 1;
              }
              __syncthreads();
              const auto curr_block_id_x = descend::block_id_x();

              if (threadIdx.x < 1) {
                if (curr_block_id_x > 0) {
                  auto not_done = true;
                  auto endIndex = curr_block_id_x - 5;
                  if (endIndex < 0) {
                    endIndex = 0;
                  }
                  while (not_done) {
                    exclusive_prefix[(threadIdx.x - 0)] = 0;
                    auto i = 1;
                    auto flag = 0;
                    auto agg = 0;
                    auto prefix = 0;
                    auto not_break_loop = true;
                    while (i <= 5 && curr_block_id_x - i >= 0 &&
                           not_break_loop) {
                      const auto raw_ptr_flag =
                          descend::to_raw_ptr<descend::i32>((&gi_flags[(
                              (blockIdx.x * 1) + (threadIdx.x - 0))]));
                      const auto raw_ptr_flag_offset =
                          descend::offset_raw_ptr<descend::i32>(raw_ptr_flag,
                                                                0 - i);
                      const auto raw_ptr_agg =
                          descend::to_raw_ptr<descend::i32>((&gi_aggs[(
                              (blockIdx.x * 1) + (threadIdx.x - 0))]));
                      const auto raw_ptr_agg_offset =
                          descend::offset_raw_ptr<descend::i32>(raw_ptr_agg,
                                                                0 - i);
                      const auto raw_ptr_prefix =
                          descend::to_raw_ptr<descend::i32>((&gi_prefixs[(
                              (blockIdx.x * 1) + (threadIdx.x - 0))]));
                      const auto raw_ptr_prefix_offset =
                          descend::offset_raw_ptr<descend::i32>(raw_ptr_prefix,
                                                                0 - i);
                      // unsafe
                      {
                        flag = (*raw_ptr_flag_offset);
                        agg = (*raw_ptr_agg_offset);
                        prefix = (*raw_ptr_prefix_offset);
                      }
                      if (flag == 0) {
                        not_break_loop = false;
                      }
                      if (flag == 1) {
                        exclusive_prefix[(threadIdx.x - 0)] =
                            exclusive_prefix[(threadIdx.x - 0)] + agg;
                      }
                      if (flag == 2) {
                        exclusive_prefix[(threadIdx.x - 0)] =
                            exclusive_prefix[(threadIdx.x - 0)] + prefix;
                        not_break_loop = false;
                        not_done = false;
                      }
                      i = i - 1;
                    }
                  }
                }
              }
              __syncthreads();

              if (threadIdx.x < 1) {
                gi_prefixs[((blockIdx.x * 1) + (threadIdx.x - 0))] =
                    exclusive_prefix[(threadIdx.x - 0)] +
                    result_reduction[(threadIdx.x - 0)];
              }
              __syncthreads();

              if (threadIdx.x < 1) {
                gi_flags[((blockIdx.x * 1) + (threadIdx.x - 0))] = 2;
              }
              __syncthreads();
              {
                const auto foo = shared_input;
                for (std::size_t d = b_size; d > 0; d = d / 2) {

                  if (threadIdx.x < d) {
                    (&(*foo))[(((threadIdx.x - 0) * ((b_size * t_size) / d)) +
                               (((b_size * t_size) / d) - 1))] =
                        (&(*foo))[(
                            ((threadIdx.x - 0) * ((b_size * t_size) / d)) +
                            (((b_size * t_size) / d) - 1))] +
                        (&(*foo))[(
                            ((threadIdx.x - 0) * ((b_size * t_size) / d)) +
                            ((b_size / d) - 1))];
                  }
                  __syncthreads();
                }
              }

              if (threadIdx.x < 1) {
                shared_input[((threadIdx.x - 0) + ((b_size * t_size) - 1))] = 0;
              }
              __syncthreads();
              {
                const auto foo = shared_input;
                for (std::size_t d = 1; d <= b_size; d = d * 2) {

                  if (threadIdx.x < d) {
                    const auto t = (&(
                        *foo))[(((threadIdx.x - 0) * ((b_size * t_size) / d)) +
                                ((b_size / d) - 1))];
                    (&(*foo))[(((threadIdx.x - 0) * ((b_size * t_size) / d)) +
                               ((b_size / d) - 1))] =
                        (&(*foo))[(
                            ((threadIdx.x - 0) * ((b_size * t_size) / d)) +
                            (((b_size * t_size) / d) - 1))];
                    (&(*foo))[(((threadIdx.x - 0) * ((b_size * t_size) / d)) +
                               (((b_size * t_size) / d) - 1))] =
                        (&(*foo))[(
                            ((threadIdx.x - 0) * ((b_size * t_size) / d)) +
                            (((b_size * t_size) / d) - 1))] +
                        t;
                  }
                  __syncthreads();
                }
              }

              {
                for (std::size_t k = 0; k < t_size; k = k + 1) {
                  gi_i[((blockIdx.x * (b_size * t_size)) +
                        ((threadIdx.x * t_size) + k))] =
                      shared_input[((threadIdx.x * t_size) + k)] +
                      exclusive_prefix[0] +
                      shared_input_bkp[((threadIdx.x * t_size) + k)];
                }
              }
              __syncthreads();
            }
          }
        },
        (&g_i), (&g_flags), (&g_aggs), (&g_prefixs));
    descend::copy_to_host<
        descend::array<descend::i32, ((g_size * b_size) * t_size)>>(
        (&g_i), cpu_i_array);
    descend::copy_to_host<descend::array<descend::i32, g_size>>((&g_flags),
                                                                cpu_flag_array);
    descend::copy_to_host<descend::array<descend::i32, g_size>>((&g_aggs),
                                                                cpu_agg_array);
    descend::copy_to_host<descend::array<descend::i32, g_size>>(
        (&g_prefixs), cpu_prefix_array);
  }
}
