#include <iostream>
#include <numeric>

#define BENCH
#include "descend.cuh"
/*
function declarations
*/
template <std::size_t width, std::size_t gs, std::size_t bsx, std::size_t bsy>
// FIXME manually substituted: multi-dim arrays are compiled to pointer to array instead of only pointer
__host__ auto transpose(descend::f32 *const h_vec) -> void;
template <std::size_t width, std::size_t gs, std::size_t bsx, std::size_t bsy>
__global__ auto
par_transpose(const descend::f32 *const in_vec, descend::f32 *const out_vec) -> void;
/*
function definitions
*/
template <std::size_t width, std::size_t gs, std::size_t bsx, std::size_t bsy>
__host__ auto transpose(descend::f32 *const h_vec) -> void {
  auto gpu = descend::gpu_device(0);
  const auto d_vec = descend::gpu_alloc_copy<descend::array<descend::f32, (width * width)>>((&gpu), (&(*h_vec)));
  auto d_vec_out = descend::gpu_alloc_copy<descend::array<descend::f32, (width * width)>>((&gpu), (&(*h_vec)));

   // BENCHMARK
  descend::Timing timing{};
  timing.record_begin();
  par_transpose<width, gs, bsx, bsy>
      <<<dim3(gs, gs, 1), dim3(bsx, bsy, 1), (0 + (4 * ((1 * bsx) * bsx)))>>>((&d_vec), (&d_vec_out));
  CHECK_CUDA_ERR( cudaDeviceSynchronize() );
  timing.record_end();
  benchmark.current_run().insert_timing(timing);

  descend::copy_to_host<descend::array<descend::f32, (width*width)>>((&d_vec_out), h_vec);
}

template <std::size_t width, std::size_t gs, std::size_t bsx, std::size_t bsy>
__global__ auto
par_transpose(const descend::f32 *const in_vec, descend::f32 *const out_vec) -> void {
  extern __shared__ descend::byte $buffer[];
  descend::f32 *const tmp = (descend::f32 *)(&$buffer[0]);
  {
    {
      {
        {
          for (std::size_t i = 0; i < (bsx / bsy); i = i + 1) {
            const auto tmp_tile =
                // FIXME manually adjusted from two-dimensional to one-dimensional indexing
                (&(tmp[((i * bsy) + (threadIdx.y - 0)) * bsx + threadIdx.x]));
                // FIXME manually adjusted from two-dimensional to one-dimensional indexing
            (*tmp_tile) = in_vec[((blockIdx.y - 0) * bsx)*width + blockIdx.x * bsx  + ((i * bsy) + (threadIdx.y - 0)) * width + (threadIdx.x - 0)];
          }

          __syncthreads();
          for (std::size_t i = 0; i < (bsx / bsy); i = i + 1) {
            const auto tmp_tile =
                // FIXME manually adjusted from two-dimensional to one-dimensional indexing
                (&(tmp[bsx * (threadIdx.x - 0) + (i * bsy) + (threadIdx.y - 0)]));
            out_vec[((blockIdx.x - 0) * bsx) * width + (blockIdx.y - 0) * bsx + (((threadIdx.y - 0) + (i * bsy)) * width) + (threadIdx.x - 0)] = (*tmp_tile);
          }
        }
      }
    }
  }
}

void transpose_cpu(float *in, float *out, const std::size_t width) {
  for(std::size_t k = 0; k < width*width; k++) {
    std::size_t i = k/width;
    std::size_t j = k%width;
    out[k] = in[j*width + i];
  }
}

descend::Benchmark benchmark{descend::BenchConfig({"transpose"})};
auto main() -> int {
  static constexpr std::size_t gs[] = {256, 384, 512, 768};
  static_for<0, 3>([](auto i) {
    static constexpr auto bsx = 32;
    static constexpr auto bsy = 8;
    static constexpr std::size_t width = gs[i] * bsx;

    auto gold = new descend::f32[width * width];
    auto in_cpu = new descend::f32[width * width];
    std::iota(in_cpu, in_cpu + width*width, 1.0f);
    transpose_cpu(in_cpu, gold, width);
    delete[] in_cpu;

    auto harray = new descend::f32[width*width];
    for (std::size_t iter = 0; iter < 100; iter++) {
      std::iota(harray, harray + width*width, 1.0f);

      transpose<width, gs[i], bsx, bsy>(harray);

      for (size_t i = 0; i < width*width; i++) {
          if (harray[i] != gold[i]) {
              std::cout << "At i = " << i << std::endl << "Wrong number. Found " << harray[i] << " instead of " << gold[i]<< std::endl;
              exit(EXIT_FAILURE);
          }
      }
    }
    delete[] harray;
    delete[] gold;

    std::size_t size_in_mib = width*width * sizeof(descend::f32)/1024/1024;
    std::cout << "Input Size: " << size_in_mib << " MiB" << std::endl;
    std::cout << benchmark.to_csv();
    std::cout << "--------------" << std::endl;
    
    benchmark.reset();
  });

  exit(EXIT_SUCCESS);
}
