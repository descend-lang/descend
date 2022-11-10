#define WG 4
#define WI 2

__kernel void shrd_red(__global const int *const a, __global int *const out) {

    int id_local = get_local_id(0);
    int id_group = get_group_id(0);
    int id_global = get_global_id(0);
    __local int tmp[WI];

    {
        {tmp[id_local] = a[id_global];} 

        barrier(CLK_LOCAL_MEM_FENCE);

        for (size_t k = (WI / 2); k > 0; k = k / 2 ) {
            if (id_local < k) {
                tmp[id_local] = tmp[id_local] + tmp[id_local + k];
            }
        }
        barrier(CLK_LOCAL_MEM_FENCE);

        if (id_local < 1) {
            out[id_group] = tmp[id_local];
        }
    }
}