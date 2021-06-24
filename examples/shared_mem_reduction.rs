fn reduce_shared_mem<n: nat, a: prv, b: prv>(
    ha_array: &a uniq cpu.heap [i32; n]
) -[cpu.thread]-> () {
        let gpu: Gpu = gpu(0);
        let mut a_array = gpu_alloc(&uniq gpu, &ha_array);

        exec::<64, 1024>(&uniq gpu,
            group::<1024>(to_view_mut(&uniq a_array)),
            | grid, input| -[gpu]-> () {
                let tmp = shared_alloc::<[i32; 1024]>();
                for grid with <input, tmp> do 
                    | block, ib | -[gpu.group]-> () {

                         for block
                         with zip(ib, to_view_mut(&uniq tmp))
                         do | thread, inp | { *inp.0 = *inp.1; };

                         for k in halfed_range(512) {
                             let active_halves = split_at::<k>(take::<2*k>(ib));

                             for take::<k>(block)
                             with <active_halves.0, active_halves.1>
                             do | thread, inp | { *inp.0 = *inp.0 + *inp.1; };
                         }
                     };
            }
        );
        copy_to_host(&a_array, ha_array);
}
