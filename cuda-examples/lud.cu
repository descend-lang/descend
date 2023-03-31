#include "descend.cuh"
/*
function declarations
*/
template <std::size_t tile_size, std::size_t matrix_dim>
__host__ auto lud_descend(descend::array<descend::f64, matrix_dim> *const m5)
    -> void;
template <std::size_t it, std::size_t tile_size, std::size_t matrix_dim>
__host__ auto lud_perimeter(descend::array<descend::f64, matrix_dim> *const m2)
    -> void;
template <std::size_t it, std::size_t tile_size, std::size_t matrix_dim>
__host__ auto lud_internal(descend::array<descend::f64, matrix_dim> *const m3)
    -> void;
/*
function definitions
*/
template <std::size_t tile_size, std::size_t matrix_dim>
__host__ auto lud_descend(descend::array<descend::f64, matrix_dim> *const m5)
    -> void {
  auto gpu = descend::gpu_device(0);
  auto m_gpu = descend::gpu_alloc_copy<
      descend::array<descend::array<descend::f64, matrix_dim>, matrix_dim>>(
      (&gpu), (&(*m5)));
  static_for<0, matrix_dim / tile_size - 1>([](auto it) -> void {
    lud_perimeter<it, tile_size, matrix_dim>((&m_gpu));
    lud_internal<it, tile_size, matrix_dim>((&m_gpu));
  });
  descend::copy_to_host<
      descend::array<descend::array<descend::f64, matrix_dim>, matrix_dim>>(
      (&m_gpu), m5);
}

template <std::size_t it, std::size_t tile_size, std::size_t matrix_dim>
__host__ auto lud_perimeter(descend::array<descend::f64, matrix_dim> *const m2)
    -> void {
  const auto a = 1;
}

template <std::size_t it, std::size_t tile_size, std::size_t matrix_dim>
__host__ auto lud_internal(descend::array<descend::f64, matrix_dim> *const m3)
    -> void {
  const auto a = 1;
}
