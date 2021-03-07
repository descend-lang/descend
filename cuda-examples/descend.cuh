#ifndef DESCEND_DESCEND_CUH
#define DESCEND_DESCEND_CUH
#include <cstdint>

#include <array>
#include <iostream>

#define CHECK_CUDA_ERR(err) { check_cuda_err((err), __FILE__, __LINE__); }
inline void check_cuda_err(const cudaError_t err, const char * const file, const int line) {
    if (err != cudaSuccess) {
        std::cerr << "Cuda Error: " << cudaGetErrorString(err) << " "  << file << " " << line << std::endl;
        exit(err);
    }
}

namespace descend {

using i32 = std::int32_t;
// FIXME there is no way to guarantee that float holds 32 bits
using f32 = float;

template<typename T, std::size_t n>
using array = std::array<T, n>;

template<typename ... Types>
using tuple = std::tuple<Types...>;

using Gpu = size_t;

Gpu gpu(size_t device_id) {
    return device_id;
};

template<std::size_t num_blocks, std::size_t num_threads>
struct GridConfig {
    const Gpu gpu;

    GridConfig(const Gpu * const gpu) : gpu(*gpu) {}
};

template<std::size_t num_blocks, std::size_t num_threads>
GridConfig<num_blocks, num_threads> spawn_threads(const Gpu * const gpu) {
    return GridConfig<num_blocks, num_threads>(gpu);
}

template<typename T>
constexpr auto size_in_bytes() -> std::size_t {
    return sizeof(T);
};

template<
template<typename, typename> typename Array,
typename E
>
constexpr auto size_in_bytes< Array<E,std::size_t> >() -> std::size_t {
    return std::tuple_size<Array<E, std::size_t>>::value * size_in_bytes<E>();
};

template<
template<typename ...> typename Tuple,
typename Head, typename ... Tail
>
constexpr auto size_in_bytes< Tuple<Head, Tail...> >() -> std::size_t {
    return size_in_bytes<Head>() + size_in_bytes<Tail ...>();
};

enum Memory {
    CpuHeap,
    GpuGlobal
};

template<Memory mem, typename DescendType>
class Buffer;

template<typename DescendType>
class Buffer<Memory::CpuHeap, DescendType> {
    DescendType * const ptr_;

public:
    static constexpr std::size_t size = size_in_bytes<DescendType>;

    Buffer(const DescendType init_val) : ptr_{new DescendType(init_val)} {}
    Buffer(const DescendType * const __restrict__ init_ptr) : ptr_{new DescendType(*init_ptr)} {}
    ~Buffer() {
        delete ptr_;
    }

    auto operator&() -> DescendType * {
        return ptr_;
    }

    auto operator&() const -> const DescendType * {
        return ptr_;
    }
};

template<typename DescendType, std::size_t n>
class Buffer<Memory::CpuHeap, descend::array<DescendType, n>> {
    descend::array<DescendType, n> * const ptr_;

public:
    static constexpr std::size_t size = size_in_bytes<descend::array<DescendType, n>>();

    Buffer(const descend::array<DescendType, n> init) : ptr_{new descend::array<DescendType, n>} {
        std::copy(init.begin(), init.end(), ptr_->data());
    }

    Buffer(const DescendType * const __restrict__ init_ptr) : ptr_{new descend::array<DescendType, n>} {
        std::copy(init_ptr, init_ptr + size, ptr_->data());
    }
    ~Buffer() {
        delete ptr_;
    }

    auto operator&() -> DescendType * {
        return ptr_->data();
    }

    auto operator&() const -> const DescendType * {
        return ptr_->data();
    }

    DescendType& operator[](std::size_t idx) { return (*ptr_)[idx]; }
    const DescendType& operator[](std::size_t idx) const { return (*ptr_)[idx]; }
};

template<typename DescendType>
class Buffer<Memory::GpuGlobal, DescendType> {
    const Gpu gpu_;
    DescendType * dev_ptr_;

public:
    static constexpr std::size_t size = size_in_bytes<DescendType>();

    Buffer(const Gpu * const __restrict__ gpu, const DescendType * const __restrict__ init_ptr): gpu_{*gpu} {
        CHECK_CUDA_ERR( cudaSetDevice(gpu_) );
        CHECK_CUDA_ERR( cudaMalloc(&dev_ptr_, size) );
        CHECK_CUDA_ERR( cudaMemcpy(dev_ptr_, init_ptr, size_in_bytes<DescendType>(), cudaMemcpyHostToDevice) );
    }

    ~Buffer() {
        CHECK_CUDA_ERR( cudaSetDevice(gpu_) );
        CHECK_CUDA_ERR( cudaFree(dev_ptr_) );
    }

    auto operator&() -> DescendType * {
        return dev_ptr_;
    }

    auto operator&() const -> const DescendType * {
        return dev_ptr_;
    }
};

template<typename DescendType, std::size_t n>
class Buffer<Memory::GpuGlobal, descend::array<DescendType, n>> {
    const Gpu gpu_;
    DescendType * dev_ptr_;

public:
    static constexpr std::size_t size = size_in_bytes<array<DescendType, n>>();

    Buffer(const Gpu * const __restrict__ gpu, const DescendType * const __restrict__ init_ptr) : gpu_{*gpu} {
        CHECK_CUDA_ERR( cudaSetDevice(gpu_) );
        CHECK_CUDA_ERR( cudaMalloc(&dev_ptr_, size) );
        CHECK_CUDA_ERR( cudaMemcpy(dev_ptr_, init_ptr, size, cudaMemcpyHostToDevice) );
    }

    ~Buffer() {
        CHECK_CUDA_ERR( cudaSetDevice(gpu_) );
        CHECK_CUDA_ERR( cudaFree(dev_ptr_) );
    }

    auto operator&() -> DescendType * {
        return dev_ptr_;
    }
    auto operator&() const -> const DescendType * {
        return dev_ptr_;
    }
};

template<typename DescendType>
using HeapBuffer = Buffer<Memory::CpuHeap, DescendType>;

template<typename DescendType>
using GpuBuffer = Buffer<Memory::GpuGlobal, DescendType>;

template<typename DescendType, typename PtrType>
auto gpu_alloc(const Gpu * const __restrict__ gpu, const PtrType * const __restrict__ init_ptr) -> GpuBuffer<DescendType>  {
    return descend::GpuBuffer<DescendType>(gpu, init_ptr);
}

template<typename DescendType, typename PtrTypeDev, typename PtrTypeHost>
auto copy_to_host(const PtrTypeDev * __restrict__ device_ptr, PtrTypeHost * const __restrict__ host_ptr) -> void {
    CHECK_CUDA_ERR( cudaMemcpy(host_ptr, device_ptr, size_in_bytes<DescendType>(), cudaMemcpyDeviceToHost) );
}

template <typename F, typename... Args>
__global__ void launch(F f, Args... args)
{
    f(args...);
}

template<std::size_t num_blocks, std::size_t num_threads, typename F, typename... Args>
auto par_for(const GridConfig<num_blocks, num_threads> * const thread_config, F &&f, Args... args) -> void {
    CHECK_CUDA_ERR( cudaSetDevice(thread_config->gpu) );
    launch<<<num_blocks, num_threads>>>(f, args...);
    CHECK_CUDA_ERR( cudaPeekAtLastError() );
    CHECK_CUDA_ERR( cudaDeviceSynchronize() );
}

namespace detail
{
    template <typename T, std::size_t ... Is>
    constexpr descend::array<T, sizeof...(Is)>
    create_array(T value, std::index_sequence<Is...>)
    {
        // cast Is to void to remove the warning: unused value
        return {{(static_cast<void>(Is), value)...}};
    }
};

template <std::size_t N, typename T>
constexpr descend::array<T, N> create_array(const T& value)
{
    return detail::create_array(value, std::make_index_sequence<N>());
}

};
#endif //DESCEND_DESCEND_CUH