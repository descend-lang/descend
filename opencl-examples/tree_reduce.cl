#define WI 256

__kernel void tree_reduce(__global int* array) {
    for(uint k = WI/2; k > 0; k = k / 2) {
        if(get_local_id(0) < k) {
            array[((get_group_id(0) * WI) + get_local_id(0))] =
                array[((get_group_id(0) * WI) + get_local_id(0))] +
                array[((get_group_id(0) * WI) + (get_local_id(0) + k))];
        }
        else {}
        barrier(CLK_GLOBAL_MEM_FENCE);
    }
}