/*
 * https://github.com/yuhc/gpu-rodinia/blob/master/cuda/huffman/hist.cu
 */
__global__ void histo_kernel(unsigned char *buffer,
        long size,
        unsigned int *histo ) {

    __shared__  unsigned int temp[256];

    temp[threadIdx.x] = 0;
    __syncthreads();

    int i = threadIdx.x + blockIdx.x * blockDim.x;
    int offset = blockDim.x * gridDim.x;
    while (i < size) {
        atomicAdd( &temp[buffer[i]], 1 );
        i += offset;
    }

    __syncthreads();
    atomicAdd( &(histo[threadIdx.x]), temp[threadIdx.x] );
}

template <std::size_t gs, std::size_t ts>
__host__ auto hist(const descend::u8 *const h_in, descend::u32 *const h_out)
-> void {
    const auto buffer =
    descend::gpu_alloc_copy<descend::array<descend::u8, ((gs * 256) * ts)>>(
            (&gpu), (&(*h_in)));
    auto histo = descend::gpu_alloc_copy<descend::array<descend::u32, 256>>(
            (&gpu), (&(*h_out)));
    histo_kernel<<<dim3(gs, 1, 1), dim3(256, 1, 1)>>>((&buffer), ts, (&histo));
    descend::copy_to_host<descend::array<descend::u32, 256>>((&histo), h_out);
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