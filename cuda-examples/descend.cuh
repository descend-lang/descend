#ifndef DESCEND_DESCEND_CUH
#define DESCEND_DESCEND_CUH
#include <cstdint>

#include <array>
#include <thrust/tuple.h>
#include <iostream>
#include <sstream>
#include <vector>
#include <atomic>

#define CHECK_CUDA_ERR(err) { check_cuda_err((err), __FILE__, __LINE__); }
inline void check_cuda_err(const cudaError_t err, const char * const file, const int line) {
    if (err != cudaSuccess) {
        std::cerr << "Cuda Error: " << cudaGetErrorString(err) << " "  << file << " " << line << std::endl;
        exit(err);
    }
}

//
// Define BENCH in order to enable benchmarking (of kernels).
// If BENCH is defined, the file that is including this header must define the variable `benchmark`.
// A `Benchmark` is created by supplying a configuration `BenchConfig`, that includes the names of all the kernels
//  that are executed in a single run. The names of the kernels have to be specified in the order of the kernel calls.
// `benchmark` will hold all measurements.
//
#ifdef BENCH
namespace descend {
    class Benchmark;
};
extern descend::Benchmark benchmark;
#endif

namespace descend {
#ifdef BENCH
class Timing {
private:
    cudaEvent_t begin_, end_;

public:
    Timing() {
        CHECK_CUDA_ERR( cudaEventCreate(&begin_) );
        CHECK_CUDA_ERR( cudaEventCreate(&end_) );
    }

    auto time_in_ms() const -> float {
        float time;
        CHECK_CUDA_ERR( cudaEventElapsedTime(&time, begin_, end_) );
        return time;
    }

    auto record_begin() -> void { CHECK_CUDA_ERR( cudaEventRecord(begin_) )}
    auto record_end() -> void { CHECK_CUDA_ERR( cudaEventRecord(end_) )}

    auto begin() const -> cudaEvent_t { return begin_; }
    auto end() const -> cudaEvent_t { return end_; }
};

class BenchRun {
private:
    size_t num_kernels_;
    std::vector<Timing> timings_;

public:
    BenchRun(size_t num_kernels): num_kernels_{num_kernels} {}

    auto insert_timing(Timing t) -> void {
        if (timings_.size() < num_kernels_)
            timings_.push_back(t);
        else
            throw std::logic_error("Trying to add timing for non-specified kernel.");
    }

    auto full_runtime_in_ms() const -> float {
        float time = 0;
        for (const auto& t : timings_) {
            time += t.time_in_ms();
        }
        return time;
    }

    auto is_finished() const -> bool {
        return timings_.size() == num_kernels_;
    }

    auto kernel_runtimes_in_ms() const -> std::vector<float> {
        std::vector<float> ts;
        for (const auto& t : timings_) {
            ts.push_back(t.time_in_ms());
        }
        return ts;
    }

    auto csv_line() const -> std::string {
        std::stringstream sstr;
        for (const auto t : kernel_runtimes_in_ms()) {
             sstr << t << ", ";
        }
        sstr << full_runtime_in_ms() << std::endl;
        return sstr.str();
    }
};

class BenchConfig {
private:
    std::vector<std::string> kernel_idents_;

public:
    BenchConfig(std::initializer_list<std::string> kernel_idents): kernel_idents_(kernel_idents) {}
    BenchConfig(std::size_t num_kernels){
        for (int i = 0; i < num_kernels; i++){
            std::stringstream ss;
            ss << "kernel_" << i;
            kernel_idents_.push_back(ss.str());
        }
    }
    auto num_kernels() const -> size_t {
        return kernel_idents_.size();
    }

    auto get_kernel_idents() const -> std::vector<std::string> {
        return kernel_idents_;
    }
};

class Benchmark {
private:
    BenchConfig cfg_;
    std::vector<BenchRun> runs_;

    auto csv_header() const -> std::string {
        std::stringstream sstr;
        for (const auto& ident : cfg_.get_kernel_idents()) {
            sstr << "kernel:" << ident << ", ";
        }
        sstr << "Total kernel runtime" << std::endl;
        return sstr.str();
    }

public:
    Benchmark(BenchConfig cfg): cfg_{cfg} {
        runs_.push_back(BenchRun{cfg_.num_kernels()});
    }

    auto current_run() -> BenchRun& {
        BenchRun& current = runs_.back();
        if (current.is_finished()) {
            runs_.push_back(BenchRun{cfg_.num_kernels()});
        }
        return runs_.back();
    }

    auto to_csv() const -> std::string {
        std::stringstream sstr;
        sstr << csv_header();
        for (const auto& r : runs_) {
            sstr << r.csv_line();
        }
        return sstr.str();
    }

    // The last value in the result vector is the average total time
    auto avg_kernel_timings() const -> std::vector<float> {
        std::vector<float> avg_timings(cfg_.num_kernels() + 1);
        for (const auto& r : runs_) {
            auto iter = avg_timings.begin();
            for (const auto& t : r.kernel_runtimes_in_ms()) {
                *iter += t;
                iter++;
            }
            avg_timings.back() += r.full_runtime_in_ms();
        }
        for (auto& avg_t: avg_timings) {
            avg_t = avg_t / runs_.size();
        }

        return avg_timings;
    }

    auto avg_to_csv() const -> std::string {
        std::stringstream sstr;
        sstr << csv_header();
        for (const auto& avg : avg_kernel_timings()) {
            sstr << avg << ", ";
        }
        sstr << std::endl;
        return sstr.str();
    }
};
#endif


// TODO cuda::std::int32_t
using i32 = std::int32_t;
extern const i32 NO_ERROR = -1;
using u32 = std::uint32_t;
// FIXME there is no way to guarantee that float holds 32 bits
using f32 = float;

template<typename T, std::size_t n>
using array = std::array<T, n>;

template<typename ... Types>
using tuple = thrust::tuple<Types...>;

template<typename T>
using atomic = std::atomic<T>;

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



// TODO remove copy constructor, assign constructor and add move constructor
using Gpu = size_t;

Gpu gpu_device(size_t device_id) {
    return device_id;
};


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

    Buffer(const DescendType default_value): ptr_{new descend::array<DescendType, n>} {
        std::fill(ptr_->begin(), ptr_->end(), default_value);
    }

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

    Buffer(const Gpu * const __restrict__ gpu, const DescendType default_value): gpu_{*gpu} {
        CHECK_CUDA_ERR( cudaSetDevice(gpu_) );
        CHECK_CUDA_ERR( cudaMalloc(&dev_ptr_, size) );
        CHECK_CUDA_ERR( cudaMemset(dev_ptr_, default_value, size));
    }

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
auto gpu_alloc_copy(const Gpu * const __restrict__ gpu, const PtrType * const __restrict__ init_ptr) -> GpuBuffer<DescendType>  {
    return descend::GpuBuffer<DescendType>(gpu, init_ptr);
}

template<typename DescendType, typename PtrTypeDev, typename PtrTypeHost>
auto copy_to_host(const PtrTypeDev * const __restrict__ device_ptr, PtrTypeHost * const __restrict__ host_ptr) -> void {
    CHECK_CUDA_ERR( cudaMemcpy(host_ptr, device_ptr, size_in_bytes<DescendType>(), cudaMemcpyDeviceToHost) );
}

template<typename DescendType, typename PtrTypeDev, typename PtrTypeHost>
auto copy_to_gpu(PtrTypeDev * const __restrict__ device_ptr, const PtrTypeHost * const __restrict__ host_ptr) -> void {
    CHECK_CUDA_ERR( cudaMemcpy(device_ptr, host_ptr, size_in_bytes<DescendType>(), cudaMemcpyHostToDevice) );
}

template <typename F, typename... Args>
__global__ void launch(F f, Args... args)
{
    f(args...);
}

template<std::size_t num_blocks, std::size_t num_threads, typename F, typename... Args>
auto exec(const descend::Gpu * const gpu, F &&f, Args... args) -> void {
    CHECK_CUDA_ERR( cudaSetDevice(*gpu) );
#ifdef BENCH
    Timing timing{};
    timing.record_begin();
#endif
    launch<<<num_blocks, num_threads>>>(f, args...);
#ifdef BENCH
    timing.record_end();
    benchmark.current_run().insert_timing(timing);
#endif
    CHECK_CUDA_ERR( cudaPeekAtLastError() );
    CHECK_CUDA_ERR( cudaDeviceSynchronize() );
}

template <typename T>
__device__ void atomic_set(bool *address, bool val)
{
    unsigned long long addr = (unsigned long long)address;
    unsigned pos = addr & 3;  // byte position within the int
    int *int_addr = (int *)(addr - pos);  // int-aligned address
    int old = *int_addr, assumed, ival;
    bool current_value;

    do
    {
        current_value = (bool)(old & ((0xFFU) << (8 * pos)));

        if(current_value == val)
            break;

        assumed = old;
        if(val)
            ival = old | (1 << (8 * pos));
        else
            ival = old & (~((0xFFU) << (8 * pos)));
        old = atomicCAS(int_addr, assumed, ival);
    } while(assumed != old);
}

template <typename T>
__device__ void atomic_set(T *address, T val) {
    atomicExch(address, val);
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

template <typename T>
inline __device__ T* to_raw_ptr(T* ptr) {
    return ptr - (blockIdx.x * blockDim.x + threadIdx.x);
}

template <typename T>
inline __host__ __device__ T* offset_raw_ptr(T* ptr, i32 off) {
    return ptr + off;
}

};


#endif //DESCEND_DESCEND_CUH
