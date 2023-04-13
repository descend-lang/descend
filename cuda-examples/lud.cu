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
  static_for<0, matrix_dim / tile_size - 1>([&] __device__ __host__(
                                                auto it) -> void {
    lud_diagonal<it, tile_size, matrix_dim>
        <<<dim3(1, 1, 1), dim3(tile_size, 1, 1),
           0 + 4 * 1 * tile_size * tile_size * 1>>>((&m_gpu));
    lud_perimeter<it, tile_size, matrix_dim><<<
        dim3(matrix_dim / tile_size - it - 1, 1, 1), dim3(tile_size * 2, 1, 1),
        0 + 4 * 1 * tile_size * tile_size * matrix_dim / tile_size - it - 1 +
            4 * 1 * tile_size * tile_size * matrix_dim / tile_size - it - 1 +
            4 * 1 * tile_size * tile_size * matrix_dim / tile_size - it - 1>>>(
        (&m_gpu));
    lud_internal<it, tile_size, matrix_dim>
        <<<dim3(matrix_dim / tile_size - it - 1,
                matrix_dim / tile_size - it - 1, 1),
           dim3(tile_size, tile_size, 1),
           0 + 4 * 1 * tile_size * tile_size * matrix_dim / tile_size - it -
               1 * matrix_dim / tile_size - it - 1 +
               4 * 1 * tile_size * tile_size * matrix_dim / tile_size - it -
               1 * matrix_dim / tile_size - it - 1>>>((&m_gpu));
  });
  lud_diagonal<matrix_dim / tile_size - 1, tile_size, matrix_dim>
      <<<dim3(1, 1, 1), dim3(tile_size, 1, 1),
         0 + 4 * 1 * tile_size * tile_size * 1>>>((&m_gpu));
  descend::copy_to_host<
      descend::array<descend::array<descend::f32, matrix_dim>, matrix_dim>>(
      (&m_gpu), m5);
}

template <std::size_t it, std::size_t tile_size, std::size_t matrix_dim>
__global__ auto lud_diagonal(descend::array<descend::f32, matrix_dim> *const m)
    -> void {
  extern __shared__ descend::byte $buffer[];
  descend::f32 *const local_tile = (descend::f32 *)(&$buffer[0]);

  const auto row_of_tiles = (*(*m[it * tile_size]));
  const auto position_of_tile = (*row_of_tiles);

  {
    const auto tile = (*position_of_tile[blockIdx.x - 0]);
    const auto local_tile_in_block = (*(*local_tile[blockIdx.x - 0]));
    diagonal_copy_to_local_mem<tile_size>((&(*tile)),
                                          (&(*local_tile_in_block)));
    diagonal_block<tile_size>((&(*local_tile_in_block)));
    diagonal_copy_to_global_mem<tile_size>(tile, local_tile_in_block);
  }
}

template <std::size_t it, std::size_t tile_size, std::size_t matrix_dim>
__global__ auto
lud_perimeter(descend::array<descend::f32, matrix_dim> *const m2) -> void {
  extern __shared__ descend::byte $buffer[];
  descend::f32 *const peri_row = (descend::f32 *)(&$buffer[0]);
  descend::f32 *const peri_col =
      (descend::f32
           *)(&peri_row[1 * tile_size * tile_size * matrix_dim / tile_size -
                        it - 1]);
  descend::f32 *const dia =
      (descend::f32
           *)(&peri_col[1 * tile_size * tile_size * matrix_dim / tile_size -
                        it - 1]);

  const auto position_of_tile = (*(*(*m2[0 + it * tile_size])));
  const auto dia_global = (*position_of_tile .0 [0]);
  const auto peri_row_global = (*position_of_tile .1);

  const auto peri_row_global_reborrow = (*peri_row_global);
}

template <std::size_t it, std::size_t tile_size, std::size_t matrix_dim>
__global__ auto lud_internal(descend::array<descend::f32, matrix_dim> *const m3)
    -> void {
  extern __shared__ descend::byte $buffer[];
  descend::f32 *const peri_row = (descend::f32 *)(&$buffer[0]);
  descend::f32 *const peri_col =
      (descend::f32
           *)(&peri_row[1 * tile_size * tile_size * matrix_dim / tile_size -
                        it - 1 * matrix_dim / tile_size - it - 1]);

  const auto position_of_tile = (*(*(*m3[0 + it * tile_size])));
  const auto peri_row_global = (*position_of_tile .1);
}