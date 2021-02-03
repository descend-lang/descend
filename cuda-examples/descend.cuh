//
// Created by basti on 1/28/21.
//

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

using i32_t = std::int32_t;
// FIXME there is no way to guarantee that float holds 32 bits
using f32_t = float;

template<typename T, std::size_t n>
using array_t = std::array<T, n>;

template<typename ... Types>
using tuple_t = std::tuple<Types...>;

using Gpu = size_t;

Gpu create_gpu(size_t device_id) {
    return device_id;
};

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
    DescendType * const _ptr;

public:
    static constexpr std::size_t size = size_in_bytes<DescendType>;

    Buffer(const DescendType * const __restrict__ init_ptr) : _ptr{new DescendType(*init_ptr)} {}
    Buffer(const DescendType init_val) : _ptr{new DescendType}
    ~Buffer() {
        delete _ptr;
    }

    auto operator&() -> DescendType * {
        return _ptr;
    }

    auto operator&() const -> const DescendType * {
        return _ptr;
    }
};

template<typename DescendType, std::size_t n>
class Buffer<Memory::CpuHeap, descend::array_t<DescendType, n>> {
    descend::array_t<DescendType, n> * const _ptr;

public:
    static constexpr std::size_t size = size_in_bytes<descend::array_t<DescendType, n>>();

    Buffer(const descend::array_t<DescendType, n> init) : _ptr{new descend::array_t<DescendType, n>} {
        std::copy(init.begin(), init.end(), _ptr->data());
    }

    Buffer(const DescendType * const __restrict__ init_ptr) : _ptr{new descend::array_t<DescendType, n>} {
        std::copy(init_ptr, init_ptr + size, _ptr);
    }
    ~Buffer() {
        delete _ptr;
    }

    auto operator&() -> DescendType * {
        return _ptr->data();
    }

    auto operator&() const -> const DescendType * {
        return _ptr->data();
    }

    DescendType& operator[](std::size_t idx) { return (*_ptr)[idx]; }
    const DescendType& operator[](std::size_t idx) const { return (*_ptr)[idx]; }
};

template<typename DescendType>
class Buffer<Memory::GpuGlobal, DescendType> {
    DescendType * _dev_ptr;
    const Gpu _gpu;

public:
    static constexpr std::size_t size = size_in_bytes<DescendType>;

    Buffer(Gpu * const __restrict__ gpu, const DescendType * const __restrict__ init_ptr): _gpu{*gpu} {
        CHECK_CUDA_ERR( cudaSetDevice(_gpu) );
        CHECK_CUDA_ERR( cudaMalloc(_dev_ptr, size) );
        CHECK_CUDA_ERR( cudaMemcpy(_dev_ptr, init_ptr, size_in_bytes<DescendType>(), cudaMemcpyHostToDevice) );
    }

    ~Buffer() {
        CHECK_CUDA_ERR( cudaSetDevice(_gpu) );
        CHECK_CUDA_ERR( cudaFree(_dev_ptr) );
        ~Buffer();
    }

    auto operator&() -> DescendType * {
        return _dev_ptr;
    }

    auto operator&() const -> const DescendType * {
        return _dev_ptr;
    }
};

template<typename DescendType, std::size_t n>
class Buffer<Memory::GpuGlobal, descend::array_t<DescendType, n>> {
    DescendType * const _dev_ptr;
    const Gpu _gpu;

public:
    static constexpr std::size_t size = size_in_bytes<array_t<DescendType, n>>();

    Buffer(Gpu * const __restrict__ gpu, const DescendType * const __restrict__ init_ptr) {
        _gpu = *gpu;
        CHECK_CUDA_ERR( cudaSetDevice(_gpu) );
        CHECK_CUDA_ERR( cudaMalloc(_dev_ptr, size) );
        CHECK_CUDA_ERR( cudaMemcpy(_dev_ptr, init_ptr, size, cudaMemcpyHostToDevice) );
    }

    ~Buffer() {
        CHECK_CUDA_ERR( cudaSetDevice(_gpu) );
        CHECK_CUDA_ERR( cudaFree(_dev_ptr) );
    }

    auto operator&() -> DescendType * {
        return _dev_ptr;
    }

    auto operator&() const -> const DescendType * {
        return _dev_ptr;
    }
};

template<typename DescendType>
using HeapBuffer = Buffer<Memory::CpuHeap, DescendType>;

template<typename DescendType>
using GpuBuffer = Buffer<Memory::GpuGlobal, DescendType>;

template<typename DescendType>
auto gpu_alloc(Gpu * const __restrict__ gpu, const DescendType * const __restrict__ init_ptr) -> GpuBuffer<DescendType>  {
    return descend::GpuBuffer<DescendType>(gpu, init_ptr);
}

template<typename DescendType, std::size_t n>
auto gpu_alloc<descend::array_t<DescendType, n>>(Gpu * gpu, DescendType * const __restrict__ init_ptr) -> GpuBuffer<DescendType> {
    return descend::GpuBuffer<descend::array_t<DescendType, n>>(gpu, init_ptr);
}

template<typename DescendType>
auto copy_to_host(const DescendType * const __restrict__ device_ptr, DescendType * const __restrict__ host_ptr) -> void {
    CHECK_CUDA_ERR( cudaMemcpy(host_ptr, device_ptr, size_in_bytes<DescendType>(), cudaMemcpyDeviceToHost) );
}

template<std::size_t num_blocks, std::size_t num_threads, typename F>
auto par_for_across(Gpu *gpu, F &function, void *args ...) -> void {
    CHECK_CUDA_ERR( cudaSetDevice(*gpu) );
    [] __global__ (descend::i32_t * const __restrict__ a_array, const descend::i32_t * const __restrict__ b_array) {
        int g_tid = blockIdx.x * blockDim.x + threadIdx.x;
        a_array[g_tid] = a_array[g_tid] + b_array[g_tid];
    }<<<num_blocks, num_threads>>>(args);
    CHECK_CUDA_ERR( cudaPeekAtLastError() );
}

namespace detail
{
    template <typename T, std::size_t ... Is>
    constexpr std::array<T, sizeof...(Is)>
    create_array(T value, std::index_sequence<Is...>)
    {
        // cast Is to void to remove the warning: unused value
        return {{(static_cast<void>(Is), value)...}};
    }
};

template <std::size_t N, typename T>
constexpr std::array<T, N> create_array(const T& value)
{
    return detail::create_array(value, std::make_index_sequence<N>());
}

};
#endif //DESCEND_DESCEND_CUH
