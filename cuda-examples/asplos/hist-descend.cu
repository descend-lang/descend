#include "descend.cuh"
/*
function declarations
*/
template <std::size_t gs, std::size_t ts>
__host__ auto hist(const descend::u8 *const h_in, descend::u32 *const h_out)
    -> void;
template <std::size_t gs, std::size_t ts>
__global__ auto gpu_hist(const descend::u8 *const buffer,
                         descend::u32 *const histo) -> void;
/*
function definitions
*/
template <std::size_t gs, std::size_t ts>
__host__ auto hist(const descend::u8 *const h_in, descend::u32 *const h_out)
    -> void {
  auto gpu = descend::gpu_device(0);
  const auto buffer =
      descend::gpu_alloc_copy<descend::array<descend::u8, ((gs * 256) * ts)>>(
          (&gpu), (&(*h_in)));
  auto histo = descend::gpu_alloc_copy<descend::array<descend::u32, 256>>(
      (&gpu), (&(*h_out)));
  gpu_hist<gs, ts><<<dim3(gs, 1, 1), dim3(256, 1, 1), (0 + (4 * (1 * 256)))>>>(
      (&buffer), (&histo));
  descend::copy_to_host<descend::array<descend::u32, 256>>((&histo), h_out);
}

template <std::size_t gs, std::size_t ts>
__global__ auto gpu_hist(const descend::u8 *const buffer,
                         descend::u32 *const histo) -> void {
  extern __shared__ descend::byte $buffer[];
  descend::u32 *const temp = (descend::u32 *)((&$buffer[0]));

  const auto histo_atomic = histo;
  {
    { temp[(threadIdx.x - 0)] = 0u; }

    __syncthreads();
    const auto atomic_temp = temp;
    {
      for (std::size_t i = 0; (i < ts); i = (i + 1u)) {
        const auto bucket = buffer[(
            (i * (gs * 256)) + (((blockIdx.x - 0) * 256) + (threadIdx.x - 0)))];
        descend::atomic_fetch_add(
            descend::atomic_ref<descend::u32>(atomic_temp[bucket]), 1u);
      }

      __syncthreads();
      descend::atomic_fetch_add(
          descend::atomic_ref<descend::u32>(histo_atomic[(threadIdx.x - 0)]),
          descend::atomic_load(descend::atomic_ref<descend::u32>(
              atomic_temp[(threadIdx.x - 0)])));
    }
  }
}

auto cpu_histo(const descend::u8 *const buffer, descend::u32 *const hist) -> void {
    for (auto &b : buffer) {
        hist[b]++
    }
}

descend::Benchmark benchmark{descend::BenchConfig({"hist"})};
auto main() -> int {
    // 65536*1024, 131072*1024, 262144*1024,524288*1024
    static constexpr std::size_t gs[] = {65536/256, 131072/256, 262144/256, 524288/256};
    static constexpr std::size_t ts = 1024;

    static_for<0, 1>([](auto i) {
        const auto buffer = new descend::u8[gs*256*ts];
        auto histo = new descend::u32[256];

        std::random_device rand_dev;
        std::mt19937 generator(rand_dev());
        std::uniform_int_distribution<unsigned short> distr(0, 256);
        std::generate(buffer, buffer + gs*256*ts, [&](){ return (descend::u8) distr(generator) });

        std::cout << "Footprint: " << ((gs[i]*256*ts)*sizeof(descend::u8) + 256*sizeof(descend::u32))/1024/1024 << " MiB" << std::endl;
        auto gold = new descend::u32[256];
        std::cout << "Compute gold..." << std::endl;
        cpu_histo(buffer, gold);
        std::cout << "Gold computed. Starting measurement ..." << std::endl;

        for (std::size_t iter = 0; iter < 100; iter++) {
            std::fill(histo, 256, 0);

            hist<gs[i], ts>(buffer, histo);

            for (size_t j = 0; j < 256; j++) {
                if (gold[j] != histo[j]) {
                    std::cout << "Error at " << j << ". Expected: " << gold[j] << " but found " << histo[j] << "." << std::endl;
                    exit(EXIT_FAILURE);
                }
            }
        }
        delete[] gold;
        delete[] histo;
        delete[] buffer;

        std::cout << "Input sizes: gs =" << gs[i] << ", ts = " << ts << std::endl;
        std::cout << benchmark.to_csv();

        benchmark.reset();
    });

    exit(EXIT_SUCCESS);
}