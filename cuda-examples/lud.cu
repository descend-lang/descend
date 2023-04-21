#include "descend.cuh"
/*
function declarations
*/
template <std::size_t tile_size, std::size_t matrix_dim>
__host__ auto lud_descend(descend::array<descend::f32, matrix_dim> *const m5)
    -> void;
template <std::size_t it, std::size_t tile_size, std::size_t matrix_dim>
__global__ auto lud_diagonal(descend::array<descend::f32, matrix_dim> *const m)
    -> void;
template <std::size_t it, std::size_t tile_size, std::size_t matrix_dim>
__global__ auto
lud_perimeter(descend::array<descend::f32, matrix_dim> *const m2) -> void;
template <std::size_t it, std::size_t tile_size, std::size_t matrix_dim>
__global__ auto lud_internal(descend::array<descend::f32, matrix_dim> *const m3)
    -> void;
/*
function definitions
*/
template <std::size_t tile_size, std::size_t matrix_dim>
__host__ auto lud_descend(descend::array<descend::f32, matrix_dim> *const m5)
    -> void {
  auto gpu = descend::gpu_device(0);
  auto m_gpu = descend::gpu_alloc_copy<
      descend::array<descend::array<descend::f32, matrix_dim>, matrix_dim>>(
      (&gpu), (&(*m5)));
  static_for<0, ((matrix_dim / tile_size) - 1)>([&](auto it) -> void {
    lud_diagonal<it, tile_size, matrix_dim>
        <<<dim3(1, 1, 1), dim3(tile_size, 1, 1),
           (0 + (4 * (((1 * tile_size) * tile_size) * 1)))>>>((&m_gpu));
    lud_perimeter<it, tile_size, matrix_dim>
        <<<dim3((((matrix_dim / tile_size) - it) - 1), 1, 1),
           dim3((tile_size * 2), 1, 1),
           (((0 + (4 * (((1 * tile_size) * tile_size) *
                        (((matrix_dim / tile_size) - it) - 1)))) +
             (4 * (((1 * tile_size) * tile_size) *
                   (((matrix_dim / tile_size) - it) - 1)))) +
            (4 * (((1 * tile_size) * tile_size) *
                  (((matrix_dim / tile_size) - it) - 1))))>>>((&m_gpu));
    lud_internal<it, tile_size, matrix_dim>
        <<<dim3((((matrix_dim / tile_size) - it) - 1),
                (((matrix_dim / tile_size) - it) - 1), 1),
           dim3(tile_size, tile_size, 1),
           ((0 + (4 * ((((1 * tile_size) * tile_size) *
                        (((matrix_dim / tile_size) - it) - 1)) *
                       (((matrix_dim / tile_size) - it) - 1)))) +
            (4 * ((((1 * tile_size) * tile_size) *
                   (((matrix_dim / tile_size) - it) - 1)) *
                  (((matrix_dim / tile_size) - it) - 1))))>>>((&m_gpu));
  });
  lud_diagonal<((matrix_dim / tile_size) - 1), tile_size, matrix_dim>
      <<<dim3(1, 1, 1), dim3(tile_size, 1, 1),
         (0 + (4 * (((1 * tile_size) * tile_size) * 1)))>>>((&m_gpu));
  descend::copy_to_host<
      descend::array<descend::array<descend::f32, matrix_dim>, matrix_dim>>(
      (&m_gpu), m5);
}

template <std::size_t it, std::size_t tile_size, std::size_t matrix_dim>
__global__ auto lud_diagonal(descend::array<descend::f32, matrix_dim> *const m)
    -> void {
  extern __shared__ descend::byte $buffer[];
  descend::f32 *const local_tile = (descend::f32 *)(&$buffer[0]);

  {
    const auto tile = (&(*m[(((blockIdx.x - 0) + it) * tile_size)]));
    const auto local_tile_in_block = (&(*local_tile[(blockIdx.x - 0)]));
    {
      const auto global_thread_tile = (&(*tile[(threadIdx.x - 0)]));
      const auto local_thread_tile =
          (&(*local_tile_in_block[(threadIdx.x - 0)]));
      static_for<0, tile_size>([&](auto i) -> void {
        (*local_thread_tile[i]) = (*global_thread_tile[i]);
      });
    }

    __syncthreads();
    static_for<0, (tile_size - 1)>([&](auto i) -> void {
      {

        if ((threadIdx.x - 0) < (tile_size - (i + 1))) {
        } else {
          {
            const auto elem = (&(*local_tile_in_block[(
                (threadIdx.x - (0 + (tile_size - (i + 1)))) + (i + 1))]
                                                     [(0 + i)]));

            const auto row_i = (&(*local_tile_in_block[i]));

            static_for<0, i>([&](auto j) -> void {
              (*elem) =
                  (*elem) - (*local_tile_in_block[(
                                (threadIdx.x - (0 + (tile_size - (i + 1)))) +
                                (i + 1))][j]) *
                                (*row_i[j]);
            });
            (*elem) = (*elem) / (*row_i[i]);
          }
        }

        __syncthreads();
      }

      const auto row_i1 = (&(*local_tile_in_block[(0 + (i + 1))]));

      if ((threadIdx.x - 0) < (i + 1)) {
      } else {
        {
          const auto elem =
              (&(*row_i1[((threadIdx.x - (0 + (i + 1))) + (i + 1))]));

          static_for<0, (i + 1)>([&](auto j) -> void {
            (*elem) =
                (*elem) -
                (*row_i1[j]) * (*local_tile_in_block[j][(
                                   (threadIdx.x - (0 + (i + 1))) + (i + 1))]);
          });
        }
      }

      __syncthreads();
    });
    {
      const auto global_thread_tile = (&(*tile[(threadIdx.x - 0)]));
      const auto local_thread_tile =
          (&(*local_tile_in_block[(threadIdx.x - 0)]));
      static_for<0, tile_size>([&](auto i) -> void {
        (*global_thread_tile[i]) = (*local_thread_tile[i]);
      });
    }
  }
}

template <std::size_t it, std::size_t tile_size, std::size_t matrix_dim>
__global__ auto
lud_perimeter(descend::array<descend::f32, matrix_dim> *const m2) -> void {
  extern __shared__ descend::byte $buffer[];
  descend::f32 *const peri_row = (descend::f32 *)(&$buffer[0]);
  descend::f32 *const peri_col = (descend::f32 *)(&peri_row[(
      ((1 * tile_size) * tile_size) * (((matrix_dim / tile_size) - it) - 1))]);
  descend::f32 *const dia = (descend::f32 *)(&peri_col[(
      ((1 * tile_size) * tile_size) * (((matrix_dim / tile_size) - it) - 1))]);

  const auto dia_global = (&(*m2[((0 + it) * tile_size)]));

  {
    const auto peri_row_global_tile =
        (&(*m2[((((blockIdx.x - 0) + 1) + it) * tile_size)]));
    const auto peri_col_global_tile = (&(*m2[((0 + it) * tile_size)]));
    const auto peri_row_shared_tile = (&(*peri_row[(blockIdx.x - 0)]));
    const auto peri_col_shared_tile = (&(*peri_col[(blockIdx.x - 0)]));
    const auto dia_tile = (&(*dia[(blockIdx.x - 0)]));

    if ((threadIdx.x - 0) < tile_size) {
      {
        const auto peri_row_global_tile_thread =
            (&(*peri_row_global_tile[(threadIdx.x - 0)]));
        const auto peri_row_shared_tile_thread =
            (&(*peri_row_shared_tile[(threadIdx.x - 0)]));

        static_for<0, (tile_size / 2)>([&](auto i) -> void {
          (*dia_tile[i][(threadIdx.x - 0)]) =
              (*dia_global[i][(threadIdx.x - 0)]);
        });
        static_for<0, tile_size>([&](auto i) -> void {
          (*peri_row_shared_tile_thread[i]) = (*peri_row_global_tile_thread[i]);
        });
      }
    } else {
      {
        const auto peri_col_global_tile_thread =
            (&(*peri_col_global_tile[(threadIdx.x - (0 + tile_size))]));
        const auto peri_col_shared_tile_thread =
            (&(*peri_col_shared_tile[(threadIdx.x - (0 + tile_size))]));

        static_for<0, (tile_size - (tile_size / 2))>([&](auto i) -> void {
          (*dia_tile[(i + (tile_size / 2))][(threadIdx.x - (0 + tile_size))]) =
              (*dia_global[(i + (tile_size / 2))]
                          [(threadIdx.x - (0 + tile_size))]);
        });
        static_for<0, tile_size>([&](auto i) -> void {
          (*peri_col_shared_tile_thread[i]) = (*peri_col_global_tile_thread[i]);
        });
      }
    }

    __syncthreads();
    const auto peri_row_transp = (&(*peri_row_shared_tile));
    if ((threadIdx.x - 0) < tile_size) {
      {
        const auto peri_row_column = (&(*peri_row_transp[(threadIdx.x - 0)]));
        static_for<1, tile_size>([&](auto i) -> void {
          static_for<0, i>([&](auto j) -> void {
            (*peri_row_column[i]) = (*peri_row_column[i]) -
                                    (*dia_tile[i][j]) * (*peri_row_column[j]);
          });
        });
      }
    } else {
      {
        const auto peri_col_row =
            (&(*peri_col_shared_tile[(threadIdx.x - (0 + tile_size))]));
        static_for<1, tile_size>([&](auto i) -> void {
          static_for<0, i>([&](auto j) -> void {
            (*peri_col_row[i]) =
                (*peri_col_row[i]) - (*dia_tile[i][j]) * (*peri_col_row[j]);
          });
          (*peri_col_row[i]) = (*peri_col_row[i]) / (*dia_tile[i][i]);
        });
      }
    }

    __syncthreads();
    if ((threadIdx.x - 0) < tile_size) {
      {
        const auto peri_row_global_tile_thread =
            (&(*peri_row_global_tile[(threadIdx.x - 0)]));
        const auto peri_row_shared_tile_thread =
            (&(*peri_row_shared_tile[(threadIdx.x - 0)]));
        static_for<0, tile_size>([&](auto i) -> void {
          (*peri_row_global_tile_thread[i]) = (*peri_row_shared_tile_thread[i]);
        });
      }
    } else {
      {
        const auto peri_col_global_tile_thread =
            (&(*peri_col_global_tile[(threadIdx.x - (0 + tile_size))]));
        const auto peri_col_shared_tile_thread =
            (&(*peri_col_shared_tile[(threadIdx.x - (0 + tile_size))]));
        static_for<0, tile_size>([&](auto i) -> void {
          (*peri_col_global_tile_thread[i]) = (*peri_col_shared_tile_thread[i]);
        });
      }
    }
  }
}

template <std::size_t it, std::size_t tile_size, std::size_t matrix_dim>
__global__ auto lud_internal(descend::array<descend::f32, matrix_dim> *const m3)
    -> void {
  extern __shared__ descend::byte $buffer[];
  descend::f32 *const peri_row = (descend::f32 *)(&$buffer[0]);
  descend::f32 *const peri_col = (descend::f32 *)(&peri_row[(
      (((1 * tile_size) * tile_size) * (((matrix_dim / tile_size) - it) - 1)) *
      (((matrix_dim / tile_size) - it) - 1))]);

  {
    const auto peri_col_global_block_y = (&(*m3[((0 + it) * tile_size)]));
    {
      {
        {
          const auto peri_row_shared_block =
              (&(*peri_row[(blockIdx.y - 0)][(blockIdx.x - 0)]
                          [(threadIdx.y - 0)][(threadIdx.x - 0)]));
          const auto peri_col_shared_block =
              (&(*peri_col[(blockIdx.y - 0)][(blockIdx.x - 0)]
                          [(threadIdx.y - 0)][(threadIdx.x - 0)]));
          const auto peri_row_global_block =
              (&(*m3[(((((blockIdx.x - 0) + 1) + it) * tile_size) +
                      (threadIdx.y - 0))]
                    [(((0 + it) * tile_size) + (threadIdx.x - 0))]));
          const auto peri_col_global_block = (&(
              *peri_col_global_block_y[(threadIdx.y - 0)][(threadIdx.x - 0)]));
          (*peri_row_shared_block) = (*peri_row_global_block);
          (*peri_col_shared_block) = (*peri_col_global_block);
        }
      }
    }
  }

  {
    {
      const auto peri_row_block =
          (&(*peri_row[(blockIdx.y - 0)][(blockIdx.x - 0)]));
      {
        const auto peri_col_t = (&(
            *peri_col[(blockIdx.y - 0)][(blockIdx.x - 0)][(threadIdx.y - 0)]));
        {
          const auto peri_row_t = (&(*peri_row_block[(threadIdx.x - 0)]));
          const auto thread_element =
              (&(*m3[(((((blockIdx.x - 0) + 1) + it) * tile_size) +
                      (threadIdx.y - 0))]
                    [(((((blockIdx.y - 0) + 1) + it) * tile_size) +
                      (threadIdx.x - 0))]));
          auto sum = (*peri_col_t[0]) * (*peri_row_t[0]);
          static_for<1, tile_size>([&](auto i) -> void {
            sum = sum + (*peri_col_t[i]) * (*peri_row_t[i]);
          });
          (*thread_element) = (*thread_element) - sum;
        }
      }
    }
  }
}
