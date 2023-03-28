#include "descend.cuh"
/*
function declarations
*/
template <std::size_t i>
__device__ auto
diagonal_below_HDDx_Dx_IT_P0S_T_P1S_IP0S_P1S_I$M_96____P0S_IP0S_IP0S_P1S_I$M_97____(
        descend::f64 *const a,
        const descend::array<descend::f64, i> *const shrd_row,
        const descend::array<descend::f64, (i + 1)> *const shrd_column) -> void;
template <std::size_t tile_size>
__device__ auto diagonal_blockDx_IP0S_P1S_I$M_95___(
        descend::array<descend::array<descend::f64, tile_size>, tile_size>
        *const m4) -> void;
template <std::size_t i>
__device__ auto
diagonal_above_HDDx_Dx_IP1S_T_P0S_IP0S_P1S_I$M_98____P0S_IP1S_IP0S_P1S_I$M_99____(
        descend::f64 *const a,
        const descend::array<descend::f64, (i + 1)> *const shrd_column,
        const descend::array<descend::f64, (i + 1)> *const shrd_row) -> void;
template <std::size_t tile_size, std::size_t matrix_dim>
__host__ auto lud_descend(descend::array<descend::f64, matrix_dim> *const m5)
-> void;
template <std::size_t it, std::size_t tile_size, std::size_t matrix_dim>
__global__ auto lud_diagonal(descend::array<descend::f64, matrix_dim> *const m)
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
template <std::size_t i>
__device__ auto
diagonal_below_HDDx_Dx_IT_P0S_T_P1S_IP0S_P1S_I$M_96____P0S_IP0S_IP0S_P1S_I$M_97____(
        descend::f64 *const a,
        const descend::array<descend::f64, i> *const shrd_row,
        const descend::array<descend::f64, (i + 1)> *const shrd_column) -> void {
    for (std::size_t j = 0; j < (i - 1); j = j + 1) {
        (*a) = (*a) -
               descend::group_mut<tile_size, matrix_dim,
                       descend::array<descend::f64, matrix_dim>>(m)[it][(
                       threadIdx.x + (i + 1))][(((blockIdx.x + it) * tile_size) + j)] *
               descend::group_mut<tile_size, matrix_dim,
                       descend::array<descend::f64, matrix_dim>>(
                       m)[it][i][(((blockIdx.x + it) * tile_size) + j)];
    }

    (*a) = (*a) / descend::group_mut<tile_size, matrix_dim,
            descend::array<descend::f64, matrix_dim>>(
            m)[it][i][(((blockIdx.x + it) * tile_size) + i)];
}

template <std::size_t tile_size>
__device__ auto diagonal_blockDx_IP0S_P1S_I$M_95___(
        descend::array<descend::array<descend::f64, tile_size>, tile_size>
        *const m4) -> void {
    for (std::size_t i = 0; i < (tile_size - 1); i = i + 1) {

        {

            {
                const auto elem =
                        (&descend::group_mut<tile_size, matrix_dim,
                                descend::array<descend::f64, matrix_dim>>(
                                m)[it][(threadIdx.x + (i + 1))]
                        [(((blockIdx.x + it) * tile_size) + i)]);

                diagonal_below_HDDx_Dx_IT_P0S_T_P1S_IP0S_P1S_I$M_96____P0S_IP0S_IP0S_P1S_I$M_97____<
                        i>(elem, m, m);
            }

            __syncthreads();
        }

        {
            const auto elem =
                    (&descend::group_mut<tile_size, matrix_dim,
                            descend::array<descend::f64, matrix_dim>>(m)[it][(0 + (i + 1))]
                    [(((blockIdx.x + it) * tile_size) + (threadIdx.x + (i + 1)))]);

            diagonal_above_HD<i>(elem, m, m);
        }

        __syncthreads();
    }
}

template <std::size_t i>
__device__ auto
diagonal_above_HDDx_Dx_IP1S_T_P0S_IP0S_P1S_I$M_98____P0S_IP1S_IP0S_P1S_I$M_99____(
        descend::f64 *const a,
        const descend::array<descend::f64, (i + 1)> *const shrd_column,
        const descend::array<descend::f64, (i + 1)> *const shrd_row) -> void {
    for (std::size_t j = 0; j < i; j = j + 1) {
        (*a) =
                (*a) -
                descend::group_mut<tile_size, matrix_dim,
                        descend::array<descend::f64, matrix_dim>>(m)[it][(0 + (i + 1))][(((blockIdx.x + it) * tile_size) + j)] *
                descend::group_mut<tile_size, matrix_dim,
                        descend::array<descend::f64, matrix_dim>>(m)[it][j]
                [(((blockIdx.x + it) * tile_size) + (threadIdx.x + (i + 1)))];
    }
}

template <std::size_t tile_size, std::size_t matrix_dim>
__host__ auto lud_descend(descend::array<descend::f64, matrix_dim> *const m5)
-> void {
    auto gpu = descend::gpu_device(0);
    auto m_gpu = descend::gpu_alloc_copy<
            descend::array<descend::array<descend::f64, matrix_dim>, matrix_dim>>(
            (&gpu), (&(*m5)));
    for (std::size_t it = 0; it < ((matrix_dim / tile_size) - 1); it = it + 1) {
        lud_diagonal<it, tile_size, matrix_dim>
        <<<dim3(1, 1, 1), dim3(tile_size, 1, 1), 0>>>((&m_gpu));
        lud_perimeter<it, tile_size, matrix_dim>((&m_gpu));
        lud_internal<it, tile_size, matrix_dim>((&m_gpu));
    }

    lud_diagonal<(matrix_dim / tile_size), tile_size, matrix_dim>
    <<<dim3(1, 1, 1), dim3(tile_size, 1, 1), 0>>>((&m_gpu));
    descend::copy_to_host<descend::array<descend::array<descend::f64, matrix_dim>, matrix_dim>>(
            (&m_gpu), m5);
}

template <std::size_t it, std::size_t tile_size, std::size_t matrix_dim>
__global__ auto lud_diagonal(descend::array<descend::f64, matrix_dim> *const m)
-> void {
    extern __shared__ descend::byte $buffer[];

    {
        diagonal_block<tile_size>(m);
    }
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

