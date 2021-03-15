#include "descend.cuh"

auto scalar_mult(descend::i32 *const h_array) -> void {
  auto gpu = descend::gpu(0);
  auto array =
      descend::gpu_alloc<descend::array<descend::i32, 4096>>(&gpu, &*h_array);
  auto grid = descend::spawn_threads<64, 64>(&gpu);
  descend::par_for(
      &grid,
      [] __device__(descend::i32 *const p0) -> void {
        p0[blockIdx.x * blockDim.x + threadIdx.x] =
            5 * p0[blockIdx.x * blockDim.x + threadIdx.x];
      },
      &array);
  descend::copy_to_host<descend::array<descend::i32, 4096>>(&array, h_array);
}

auto main() -> int {
    auto h_array = descend::HeapBuffer<descend::array<descend::i32, 64*64>>(descend::create_array<64*64, descend::i32>(1));
    scalar_mult(&h_array);

    for (size_t i = 0; i < 64*64; i++) {
        if (h_array[i] != 5) {
            std::cout << "At i = " << i << "Wrong number. Found " << h_array[i] << " instead of 1.";
            exit(EXIT_FAILURE);
        }
    }
    exit(EXIT_SUCCESS);
}
