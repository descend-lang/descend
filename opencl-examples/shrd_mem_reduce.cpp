#include "descend.hpp"
#define WG 4
#define WI 2


template <std::size_t wg, std::size_t wi>
auto reduce_shared_mem(cl_int *const a_h, cl_int *const out_h) -> void;

int main(void)
{
    // could be nicer
    cl_int a_h[] = {1, 2, 3, 4, 5, 6, 7, 8};
    cl_int out_h[] = {0, 0, 0, 0};
    
    reduce_shared_mem<WG, WI>(a_h, out_h);

    cl_int res = 0;
    for (int i = 0; i < WG*WI; i++) {
        res += a_h[i];
    }
    std::cout << "result should be: " << res << std::endl;

    
    return 0;
}

// wg: corresponds to gs, num of work groups 
// wi: corresponds to bs, num of wis per wg  
template <std::size_t wg, std::size_t wi>
auto reduce_shared_mem(cl_int *const a_h, cl_int *const out_h) -> void {

    std::cout << "a_h: " << a_h[0] << ", out_h: " << out_h[0] << std::endl;

    // auto gpu = descend::gpu_device(0);
    // cl_platform_id all_platforms;
    // cl_uint num;

    // cl_int res = clGetPlatformIDs(1, &all_platforms, &num);
    // if (res != CL_SUCCESS) {
    //     std::cerr << getErrorString(res) << std::endl;
    // }
    // cl_device_id device;
    // clGetDeviceIDs(all_platforms, CL_DEVICE_TYPE_ALL, 1, &device, &num);
    // if (res != CL_SUCCESS) {
    //     std::cerr << getErrorString(res) << std::endl;
    // }

    // cl_context context = clCreateContext(NULL, 1, &device, NULL, NULL, &res);
    // if (res != CL_SUCCESS) {
    //     std::cerr << getErrorString(res) << std::endl;
    // }

    // cl_command_queue queue = clCreateCommandQueueWithProperties(context, device, NULL, &res);
    // if (res != CL_SUCCESS) {
    //     std::cerr << getErrorString(res) << std::endl;
    // }

    //delete
    cl_int res = 0;
    auto gpu = descend::gpu_device(0);




    /*// allocate on GPU
    //
    // const auto a_array =
    //   descend::gpu_alloc_copy<descend::array<descend::i32, (gs * bs)>>(
    //       (&gpu), ha_array);
    
    //cl_mem a = clCreateBuffer(gpu.context, CL_MEM_READ_ONLY | CL_MEM_USE_HOST_PTR, sizeof(cl_int) * (wg * wi), a_h, &res);
    //if (res != CL_SUCCESS) {
    //    std::cerr << getErrorString(res) << std::endl;
    //}
    res = clEnqueueWriteBuffer(gpu.queue, a, true, 0, sizeof(cl_int) * (wg * wi), a_h, NULL, NULL, NULL);
    if (res != CL_SUCCESS) {
        std::cerr << getErrorString(res) << std::endl;
    }

    // auto out_array = descend::gpu_alloc_copy<descend::array<descend::i32, gs>>(
    //     (&gpu), (&(*h_output)));

    cl_mem out = clCreateBuffer(gpu.context, CL_MEM_READ_WRITE | CL_MEM_USE_HOST_PTR, sizeof(cl_int) * wg, out_h, &res);
    if (res != CL_SUCCESS) {
        std::cerr << getErrorString(res) << std::endl;
    }
    res = clEnqueueWriteBuffer(gpu.queue, a, true, 0, sizeof(cl_int) * wg, out_h, NULL, NULL, NULL);
    if (res != CL_SUCCESS) {
        std::cerr << getErrorString(res) << std::endl;
    }

    std::cout << "allocated data on Device" << std::endl;


    // execute

    // descend::exec<gs, bs>(
    //   (&gpu),
    //   [] __device__(const descend::i32 *const p0,
    //                 descend::i32 *const p1) -> void {
    //     __shared__ descend::i32 tmp[bs];
    //     {

    //       { tmp[threadIdx.x] = p0[((blockIdx.x * 1024) + threadIdx.x)]; }
    //       __syncthreads(); // Fehlt noch in generierter Version

    //       for (std::size_t k = (bs / 2); k > 0; k = k / 2) {

    //         if (threadIdx.x < k) {
    //           tmp[threadIdx.x] = tmp[threadIdx.x] + tmp[(threadIdx.x + k)];
    //         } else {
    //         }
    //         __syncthreads(); // Fehlt noch in generierter Version
    //       }

    //       if (threadIdx.x < 1) {
    //         p1[((blockIdx.x * 1) + threadIdx.x)] = tmp[threadIdx.x];
    //       } else {
    //       }
    //     }
    //   },
    //   (&a_array), (&out_array));


    // build program

    const char *kernel_code;
    std::ifstream in("shrd_mem_reduce.cl");
    std::string contents((std::istreambuf_iterator<char>(in)),
    std::istreambuf_iterator<char>());
    kernel_code = contents.c_str();
    std::cout << "read kernel\n" << kernel_code << std::endl;

    size_t len[] = {strlen(kernel_code)};
    cl_program program = clCreateProgramWithSource(gpu.context, 1, &kernel_code, len, &res);
    if (res != CL_SUCCESS) {
        std::cerr << getErrorString(res) << std::endl;
    }
    res = clBuildProgram(program, 1, &gpu.device, NULL, NULL, NULL);
    if (res != CL_SUCCESS) {
        std::cerr << getErrorString(res) << std::endl;
    }


    cl_kernel kernel = clCreateKernel(program, "shrd_red", &res);
    if (res != CL_SUCCESS) {
        std::cerr << getErrorString(res) << std::endl;
    }

    res = clSetKernelArg(kernel, 0, sizeof(a), &a);
    if (res != CL_SUCCESS) {
        std::cerr << getErrorString(res) << std::endl;
    }
    res = clSetKernelArg(kernel, 1, sizeof(out), &out);
    if (res != CL_SUCCESS) {
        std::cerr << getErrorString(res) << std::endl;
    }

    size_t global_size[] = {WG * WI};
    size_t local_size[] = {WI};
    cl_event kernel_exec;
    res = clEnqueueNDRangeKernel(gpu.queue, kernel, 1, NULL, global_size, local_size, NULL, NULL, &kernel_exec);
    if (res != CL_SUCCESS) {
        std::cerr << getErrorString(res) << std::endl;
    }
    res = clWaitForEvents(1, &kernel_exec);
    if (res != CL_SUCCESS) {
        std::cerr << getErrorString(res) << std::endl;
    }

    std::cout << "finished executing kernel" << std::endl;


    // descend::copy_to_host<descend::array<descend::i32, gs>>((&out_array),
                                                        //   (&(*h_output)));

    cl_event copy_data;
    res = clEnqueueReadBuffer(gpu.queue, out, true, 0, sizeof(cl_int) * wg, out_h, NULL, NULL, &copy_data);
    res = clWaitForEvents(1, &copy_data);
    if (res != CL_SUCCESS) {
        std::cerr << getErrorString(res) << std::endl;
    }

    // auto res = 0;
    // for (std::size_t $i___106 = 0; $i___106 < gs; $i___106 = $i___106 + 1) {
    //     res = res + h_output[$i___106];

    auto sol = 0;
    for (std::size_t i = 0; i < wg; i = i + 1) {
        std::cout << "out_h: " << out_h[i] << std::endl;
        sol = sol + out_h[i];
    }

    std::cout << "computed result: " << sol << std::endl;*/

}
