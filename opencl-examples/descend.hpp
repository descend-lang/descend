#include <CL/cl.hpp>
#include <iostream>
#include <cstdlib>
#include <fstream>
#include <sstream>
#include <array>

#define CHECK_OPENCL_ERR(err) { check_opencl_err((err), __FILE__, __LINE__); }
const char *getErrorString(cl_int error);
inline void check_opencl_err(const cl_int err, const char * const file, const int line) {
    if (err != CL_SUCCESS) {
        std::cerr << getErrorString(err) << " " << file << " " << line << std::endl;
    }
}

namespace descend {

    using i32 = std::int32_t;

    template<typename T, std::size_t n>
    using array = std::array<T, n>;


    class Gpu {
    public:
        cl::Device *device;
        cl::Context *context;
        cl::CommandQueue *queue;

        Gpu(cl::Device device, cl::Context context, cl::CommandQueue queue){
            this->device = &device;
            this->context = &context;
            this->queue = &queue;
        }
        ~ Gpu () {
            this->queue->finish();
        }
    };

    enum Memory {
        CpuHeap,
        GpuGlobal
    };

    template<Memory mem, typename DescendType>
    class Buffer;

    Gpu* gpu_device(std::size_t device_id) { // add param cl_uint device_id
        std::vector<cl::Platform> platforms;
        cl::Platform::get(&platforms);
        if(platforms.empty()){
            throw std::runtime_error("No Platforms found on Computer!");
        }
        // TODO refactor
        cl_context_properties properties[] = {CL_CONTEXT_PLATFORM, (cl_context_properties) (platforms[0])(), 0};
        cl::Context context(CL_DEVICE_TYPE_ALL);
        std::vector<cl::Device> devices = context.getInfo<CL_CONTEXT_DEVICES>();

        cl::Device device = devices[device_id];

        cl_int err;
        // Create command queue for first device
        cl::CommandQueue queue(context, device, CL_QUEUE_PROFILING_ENABLE, &err);

        if(err != CL_SUCCESS) {
            throw std::runtime_error(getErrorString(err));
        }

        return new Gpu (device, context, queue);
    };

    template<typename DescendType, std::size_t n>
    class Buffer<Memory::CpuHeap, descend::array<DescendType, n>> {
        descend::array<DescendType, n> * const ptr_;

    public:
        // static constexpr std::size_t size = size_in_bytes<descend::array<DescendType, n>>();
        static constexpr std::size_t size = n * sizeof(DescendType);

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

    template<typename DescendType, std::size_t n>
    class Buffer<Memory::GpuGlobal, descend::array<DescendType, n>> {
        const Gpu *gpu_;
        cl::Buffer buffer;

    public:
        static constexpr std::size_t size = n * sizeof(DescendType);

        Buffer(const Gpu * const __restrict__ gpu, const DescendType default_value): gpu_{gpu} {
            // CHECK_CUDA_ERR( cudaSetDevice(gpu_) );
            // CHECK_CUDA_ERR( cudaMalloc(&dev_ptr_, size) );
            // CHECK_CUDA_ERR( cudaMemset(dev_ptr_, default_value, size));
            // TODO
        }

        Buffer(const Gpu * const __restrict__ gpu, const DescendType * const __restrict__ init_ptr) : gpu_{gpu} {
            //TODO: Error Handling
            std::cout << "buf: " << gpu->context->getInfo() << std::endl;
            buffer = cl::Buffer(*(gpu_->context), CL_MEM_READ_WRITE, size);
            // Bind memory buffers
            gpu_->queue->enqueueWriteBuffer(buffer, CL_TRUE, 0, size, init_ptr);
        }

        ~Buffer() {
            // CHECK_CUDA_ERR( cudaSetDevice(gpu_) );
            // CHECK_CUDA_ERR( cudaFree(dev_ptr_) );
        }

        //auto operator&() -> DescendType * {
        //    return dev_ptr_;
        //}
        //auto operator&() const -> const DescendType * {
        //    return dev_ptr_;
        //}
    };

    template<typename DescendType>
    using HeapBuffer = Buffer<Memory::CpuHeap, DescendType>;

    template<typename DescendType>
    using GpuBuffer = Buffer<Memory::GpuGlobal, DescendType>;

    template<typename DescendType, typename PtrType>
    auto gpu_alloc_copy(const Gpu * const __restrict__ gpu, const PtrType * const __restrict__ init_ptr) -> GpuBuffer<DescendType>  {
        return descend::GpuBuffer<DescendType>(gpu, init_ptr);
    }



}

const char *getErrorString(cl_int error)
{
switch(error){
    // run-time and JIT compiler errors
    case 0: return "CL_SUCCESS";
    case -1: return "CL_DEVICE_NOT_FOUND";
    case -2: return "CL_DEVICE_NOT_AVAILABLE";
    case -3: return "CL_COMPILER_NOT_AVAILABLE";
    case -4: return "CL_MEM_OBJECT_ALLOCATION_FAILURE";
    case -5: return "CL_OUT_OF_RESOURCES";
    case -6: return "CL_OUT_OF_HOST_MEMORY";
    case -7: return "CL_PROFILING_INFO_NOT_AVAILABLE";
    case -8: return "CL_MEM_COPY_OVERLAP";
    case -9: return "CL_IMAGE_FORMAT_MISMATCH";
    case -10: return "CL_IMAGE_FORMAT_NOT_SUPPORTED";
    case -11: return "CL_BUILD_PROGRAM_FAILURE";
    case -12: return "CL_MAP_FAILURE";
    case -13: return "CL_MISALIGNED_SUB_BUFFER_OFFSET";
    case -14: return "CL_EXEC_STATUS_ERROR_FOR_EVENTS_IN_WAIT_LIST";
    case -15: return "CL_COMPILE_PROGRAM_FAILURE";
    case -16: return "CL_LINKER_NOT_AVAILABLE";
    case -17: return "CL_LINK_PROGRAM_FAILURE";
    case -18: return "CL_DEVICE_PARTITION_FAILED";
    case -19: return "CL_KERNEL_ARG_INFO_NOT_AVAILABLE";

    // compile-time errors
    case -30: return "CL_INVALID_VALUE";
    case -31: return "CL_INVALID_DEVICE_TYPE";
    case -32: return "CL_INVALID_PLATFORM";
    case -33: return "CL_INVALID_DEVICE";
    case -34: return "CL_INVALID_CONTEXT";
    case -35: return "CL_INVALID_QUEUE_PROPERTIES";
    case -36: return "CL_INVALID_COMMAND_QUEUE";
    case -37: return "CL_INVALID_HOST_PTR";
    case -38: return "CL_INVALID_MEM_OBJECT";
    case -39: return "CL_INVALID_IMAGE_FORMAT_DESCRIPTOR";
    case -40: return "CL_INVALID_IMAGE_SIZE";
    case -41: return "CL_INVALID_SAMPLER";
    case -42: return "CL_INVALID_BINARY";
    case -43: return "CL_INVALID_BUILD_OPTIONS";
    case -44: return "CL_INVALID_PROGRAM";
    case -45: return "CL_INVALID_PROGRAM_EXECUTABLE";
    case -46: return "CL_INVALID_KERNEL_NAME";
    case -47: return "CL_INVALID_KERNEL_DEFINITION";
    case -48: return "CL_INVALID_KERNEL";
    case -49: return "CL_INVALID_ARG_INDEX";
    case -50: return "CL_INVALID_ARG_VALUE";
    case -51: return "CL_INVALID_ARG_SIZE";
    case -52: return "CL_INVALID_KERNEL_ARGS";
    case -53: return "CL_INVALID_WORK_DIMENSION";
    case -54: return "CL_INVALID_WORK_GROUP_SIZE";
    case -55: return "CL_INVALID_WORK_ITEM_SIZE";
    case -56: return "CL_INVALID_GLOBAL_OFFSET";
    case -57: return "CL_INVALID_EVENT_WAIT_LIST";
    case -58: return "CL_INVALID_EVENT";
    case -59: return "CL_INVALID_OPERATION";
    case -60: return "CL_INVALID_GL_OBJECT";
    case -61: return "CL_INVALID_BUFFER_SIZE";
    case -62: return "CL_INVALID_MIP_LEVEL";
    case -63: return "CL_INVALID_GLOBAL_WORK_SIZE";
    case -64: return "CL_INVALID_PROPERTY";
    case -65: return "CL_INVALID_IMAGE_DESCRIPTOR";
    case -66: return "CL_INVALID_COMPILER_OPTIONS";
    case -67: return "CL_INVALID_LINKER_OPTIONS";
    case -68: return "CL_INVALID_DEVICE_PARTITION_COUNT";

    // extension errors
    case -1000: return "CL_INVALID_GL_SHAREGROUP_REFERENCE_KHR";
    case -1001: return "CL_PLATFORM_NOT_FOUND_KHR";
    case -1002: return "CL_INVALID_D3D10_DEVICE_KHR";
    case -1003: return "CL_INVALID_D3D10_RESOURCE_KHR";
    case -1004: return "CL_D3D10_RESOURCE_ALREADY_ACQUIRED_KHR";
    case -1005: return "CL_D3D10_RESOURCE_NOT_ACQUIRED_KHR";
    default: return "Unknown OpenCL error";
    }
}

