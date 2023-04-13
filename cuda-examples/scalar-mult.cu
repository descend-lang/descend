#include "descend.cuh"
/*
function declarations
*/
template <std::size_t n>
__host__ auto inplace_vector_add(descend::i32 *const ha_array,
                                 const descend::i32 *const hb_array) -> void;
template <std::size_t n>
__global__ auto gpu_vec_add(descend::i32 *const a_array,
                            const descend::i32 *const b_array) -> void;
/*
function definitions
*/
template <std::size_t n>
__host__ auto inplace_vector_add(descend::i32 *const ha_array,
                                 const descend::i32 *const hb_array) -> void {
  auto gpu = descend::gpu_device(0);
  auto a_array = descend::gpu_alloc_copy<descend::array<descend::i32, n>>(
      (&gpu), (&(*ha_array)));
  const auto b_array = descend::gpu_alloc_copy<descend::array<descend::i32, n>>(
      (&gpu), (&(*hb_array)));
  gpu_vec_add<n>
      <<<dim3(64, 1, 1), dim3(1024, 1, 1), 0>>>((&a_array), (&b_array));
  descend::copy_to_host<descend::array<descend::i32, n>>((&a_array), ha_array);
}

template <std::size_t n>
__global__ auto gpu_vec_add(descend::i32 *const a_array,
                            const descend::i32 *const b_array) -> void {
  extern __shared__ descend::byte $buffer[];
  {
    {
      const auto a_ref = (&(a_array[blockIdx.x - 0 * 1024 + threadIdx.x - 0]));
      (*a_ref) = (*a_ref) + (b_array[blockIdx.x - 0 * 1024 + threadIdx.x - 0]);
    }
  }
}

auto main() -> int {
    auto h_array = descend::HeapBuffer<descend::array<descend::i32, 64*64>>(descend::create_array<64*64, descend::i32>(1));
    inplace_vector_add<64*1024>(&h_array);

    for (size_t i = 0; i < 64*1024; i++) {
        if (h_array[i] != 5) {
            std::cout << "At i = " << i << "Wrong number. Found " << h_array[i] << " instead of 1.";
            exit(EXIT_FAILURE);
        }
    }
    exit(EXIT_SUCCESS);
}
