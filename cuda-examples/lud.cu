#include "descend.cuh"
/*
function declarations
*/
template <std::size_t tile_size, std::size_t matrix_dim>
__host__ auto lud_descend(descend::f32 *const m5) -> void;
template <std::size_t it, std::size_t tile_size, std::size_t matrix_dim>
__global__ auto lud_diagonal(descend::f32 *const m) -> void;
template <std::size_t it, std::size_t tile_size, std::size_t matrix_dim>
__global__ auto lud_perimeter(descend::f32 *const m2) -> void;
template <std::size_t it, std::size_t tile_size, std::size_t matrix_dim>
__global__ auto lud_internal(descend::f32 *const m3) -> void;
/*
function definitions
*/
template <std::size_t tile_size, std::size_t matrix_dim>
__host__ auto lud_descend(descend::f32 *const m5) -> void {
  auto gpu = descend::gpu_device(0);
  auto m_gpu = descend::gpu_alloc_copy<
      descend::array<descend::f32, (matrix_dim * matrix_dim)>>((&gpu),
                                                               (&(*m5)));
  static_for<0, ((matrix_dim / tile_size) - 1)>([&](auto it) -> void {
    lud_diagonal<it, tile_size, matrix_dim>
        <<<dim3(1, 1, 1), dim3(tile_size, 1, 1),
           (0 + (4 * (1 * (tile_size * tile_size))))>>>((&m_gpu));
    lud_perimeter<it, tile_size, matrix_dim>
        <<<dim3((((matrix_dim / tile_size) - it) - 1), 1, 1),
           dim3((tile_size * 2), 1, 1),
           (((0 + (4 * (1 * (tile_size * tile_size)))) +
             (4 * (1 * (tile_size * tile_size)))) +
            (4 * (1 * (tile_size * tile_size))))>>>((&m_gpu));
    lud_internal<it, tile_size, matrix_dim>
        <<<dim3((((matrix_dim / tile_size) - it) - 1),
                (((matrix_dim / tile_size) - it) - 1), 1),
           dim3(tile_size, tile_size, 1),
           ((0 + (4 * (1 * (tile_size * tile_size)))) +
            (4 * (1 * (tile_size * tile_size))))>>>((&m_gpu));
  });
  lud_diagonal<((matrix_dim / tile_size) - 1), tile_size, matrix_dim>
      <<<dim3(1, 1, 1), dim3(tile_size, 1, 1),
         (0 + (4 * (1 * (tile_size * tile_size))))>>>((&m_gpu));
  descend::copy_to_host<
      descend::array<descend::f32, (matrix_dim * matrix_dim)>>((&m_gpu), m5);
}

template <std::size_t it, std::size_t tile_size, std::size_t matrix_dim>
__global__ auto lud_diagonal(descend::f32 *const m) -> void {
  extern __shared__ descend::byte $buffer[];
  descend::f32 *const local_tile = (descend::f32 *)(&$buffer[0]);

  {
    {

      static_for<0, tile_size>([&](auto i) -> void {
        local_tile[((i * tile_size) + (threadIdx.x - 0))] =
            m[((((it * tile_size) + i) * matrix_dim) +
               ((((blockIdx.x - 0) + it) * tile_size) + (threadIdx.x - 0)))];
      });
    }

    __syncthreads();
    static_for<0, (tile_size - 1)>([&](auto i) -> void {
      {

        if ((threadIdx.x - 0) < (i + 1)) {
        } else {
          {
            const auto elem = (&local_tile[(
                (((threadIdx.x - (0 + (i + 1))) + (i + 1)) * tile_size) +
                (0 + i))]);

            static_for<0, i>([&](auto j) -> void {
              (*elem) = (*elem) -
                        local_tile[((((threadIdx.x - (0 + (i + 1))) + (i + 1)) *
                                     tile_size) +
                                    j)] *
                            local_tile[((j * tile_size) + i)];
            });
            (*elem) = (*elem) / local_tile[((i * tile_size) + i)];
          }
        }

        __syncthreads();
      }

      if ((threadIdx.x - 0) < (i + 1)) {
      } else {
        {
          const auto elem =
              (&local_tile[(((0 + (i + 1)) * tile_size) +
                            ((threadIdx.x - (0 + (i + 1))) + (i + 1)))]);

          static_for<0, (i + 1)>([&](auto j) -> void {
            (*elem) =
                (*elem) -
                local_tile[(((0 + (i + 1)) * tile_size) + j)] *
                    local_tile[((j * tile_size) +
                                ((threadIdx.x - (0 + (i + 1))) + (i + 1)))];
          });
        }
      }

      __syncthreads();
    });
    {

      static_for<1, tile_size>([&](auto i) -> void {
        m[((((it * tile_size) + i) * matrix_dim) +
           ((((blockIdx.x - 0) + it) * tile_size) + (threadIdx.x - 0)))] =
            local_tile[((i * tile_size) + (threadIdx.x - 0))];
      });
    }
  }
}

template <std::size_t it, std::size_t tile_size, std::size_t matrix_dim>
__global__ auto lud_perimeter(descend::f32 *const m2) -> void {
  extern __shared__ descend::byte $buffer[];
  descend::f32 *const peri_row = (descend::f32 *)(&$buffer[0]);
  descend::f32 *const peri_col =
      (descend::f32 *)(&peri_row[(1 * (tile_size * tile_size))]);
  descend::f32 *const dia =
      (descend::f32 *)(&peri_col[(1 * (tile_size * tile_size))]);

  {

    if ((threadIdx.x - 0) < tile_size) {
      {

        static_for<0, (tile_size / 2)>([&](auto i) -> void {
          dia[((i * tile_size) + (threadIdx.x - 0))] =
              m2[(((((0 + it) * tile_size) + i) * matrix_dim) +
                  (((0 + it) * tile_size) + (threadIdx.x - 0)))];
        });
        static_for<0, tile_size>([&](auto i) -> void {
          peri_row[((i * tile_size) + (threadIdx.x - 0))] =
              m2[(((((0 + it) * tile_size) + i) * matrix_dim) +
                  (((((blockIdx.x - 0) + 1) + it) * tile_size) +
                   (threadIdx.x - 0)))];
        });
      }
    } else {
      {

        static_for<0, (tile_size - (tile_size / 2))>([&](auto i) -> void {
          dia[(((i + (tile_size / 2)) * tile_size) +
               (threadIdx.x - (0 + tile_size)))] =
              m2[(((((0 + it) * tile_size) + (i + (tile_size / 2))) *
                   matrix_dim) +
                  (((0 + it) * tile_size) + (threadIdx.x - (0 + tile_size))))];
        });
        static_for<0, tile_size>([&](auto i) -> void {
          peri_col[((i * tile_size) + (threadIdx.x - (0 + tile_size)))] = m2[(
              ((((((blockIdx.x - 0) + 1) + it) * tile_size) + i) * matrix_dim) +
              (((0 + it) * tile_size) + (threadIdx.x - (0 + tile_size))))];
        });
      }
    }

    __syncthreads();

    if ((threadIdx.x - 0) < tile_size) {
      {
        static_for<1, tile_size>([&](auto i) -> void {
          static_for<0, i>([&](auto j) -> void {
            peri_row[((i * tile_size) + (threadIdx.x - 0))] =
                peri_row[((i * tile_size) + (threadIdx.x - 0))] -
                dia[((i * tile_size) + j)] *
                    peri_row[((j * tile_size) + (threadIdx.x - 0))];
          });
        });
      }
    } else {
      {
        static_for<0, tile_size>([&](auto i) -> void {
          static_for<0, i>([&](auto j) -> void {
            peri_col[(((threadIdx.x - (0 + tile_size)) * tile_size) + i)] =
                peri_col[(((threadIdx.x - (0 + tile_size)) * tile_size) + i)] -
                dia[((j * tile_size) + i)] *
                    peri_col[(((threadIdx.x - (0 + tile_size)) * tile_size) +
                              j)];
          });
          peri_col[(((threadIdx.x - (0 + tile_size)) * tile_size) + i)] =
              peri_col[(((threadIdx.x - (0 + tile_size)) * tile_size) + i)] /
              dia[((i * tile_size) + i)];
        });
      }
    }

    __syncthreads();
    if ((threadIdx.x - 0) < tile_size) {
      {

        static_for<1, tile_size>([&](auto i) -> void {
          m2[(((((0 + it) * tile_size) + i) * matrix_dim) +
              (((((blockIdx.x - 0) + 1) + it) * tile_size) +
               (threadIdx.x - 0)))] =
              peri_row[((i * tile_size) + (threadIdx.x - 0))];
        });
      }
    } else {
      {

        static_for<0, tile_size>([&](auto i) -> void {
          m2[(((((((blockIdx.x - 0) + 1) + it) * tile_size) + i) * matrix_dim) +
              (((0 + it) * tile_size) + (threadIdx.x - (0 + tile_size))))] =
              peri_col[((i * tile_size) + (threadIdx.x - (0 + tile_size)))];
        });
      }
    }
  }
}

template <std::size_t it, std::size_t tile_size, std::size_t matrix_dim>
__global__ auto lud_internal(descend::f32 *const m3) -> void {
  extern __shared__ descend::byte $buffer[];
  descend::f32 *const peri_row = (descend::f32 *)(&$buffer[0]);
  descend::f32 *const peri_col =
      (descend::f32 *)(&peri_row[(1 * (tile_size * tile_size))]);

  {{{{const auto peri_row_shared_block =
          (&peri_row[(((threadIdx.y - 0) * tile_size) + (threadIdx.x - 0))]);
  const auto peri_col_shared_block =
      (&peri_col[(((threadIdx.y - 0) * tile_size) + (threadIdx.x - 0))]);
  const auto peri_row_global_block = (&m3[(
      ((((0 + it) * tile_size) + (threadIdx.y - 0)) * matrix_dim) +
      (((((blockIdx.x - 0) + 1) + it) * tile_size) + (threadIdx.x - 0)))]);
  const auto peri_col_global_block =
      (&m3[(((((((blockIdx.y - 0) + 1) + it) * tile_size) + (threadIdx.y - 0)) *
             matrix_dim) +
            (((0 + it) * tile_size) + (threadIdx.x - 0)))]);
  (*peri_row_shared_block) = (*peri_row_global_block);
  (*peri_col_shared_block) = (*peri_col_global_block);
}
}

__syncthreads();
}
}

{
  {
    {
      {
        const auto thread_element = (&m3[(
            ((((((blockIdx.y - 0) + 1) + it) * tile_size) + (threadIdx.y - 0)) *
             matrix_dim) +
            (((((blockIdx.x - 0) + 1) + it) * tile_size) +
             (threadIdx.x - 0)))]);
        auto sum = 0.0f;
        static_for<0, tile_size>([&](auto i) -> void {
          sum = sum + peri_col[(((threadIdx.y - 0) * tile_size) + i)] *
                          peri_row[((i * tile_size) + (threadIdx.x - 0))];
        });
        (*thread_element) = (*thread_element) - sum;
      }
    }
  }
}
}
