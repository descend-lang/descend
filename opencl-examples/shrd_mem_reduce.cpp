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

    auto gpu = descend::gpu_device(0);

    const auto a_d = descend::gpu_alloc_copy<descend::array<descend::i32, (wg * wi)>>( gpu, a_h);
    const auto out_d = descend::gpu_alloc_copy<descend::array<descend::i32, wg>>( gpu, out_h);

    descend::exec<wg, wi>(gpu, "shrd_mem_reduce.cl", a_d, out_d);

    descend::copy_to_host(*out_d, out_h);

    auto sol = 0;
    for (std::size_t i = 0; i < wg; i = i + 1) {
        std::cout << "out_h: " << out_h[i] << std::endl;
        sol = sol + out_h[i];
    }

    std::cout << "computed result: " << sol << std::endl;

}
