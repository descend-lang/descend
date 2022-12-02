use crate::ast::{AtomicTy, BinOp, BinOpNat, DataTy, DataTyKind, Exec, Ident, IdentKinded, Kind, Memory, Nat, Ownership, Provenance, ScalarTy, ThreadHierchyTy, Ty, TyKind};

pub static GPU_DEVICE: &str = "gpu_device";
pub static GPU_ALLOC: &str = "gpu_alloc_copy";
pub static COPY_TO_HOST: &str = "copy_to_host";
pub static EXEC: &str = "exec";
pub static SHARED_ALLOC: &str = "shared_alloc";
pub static COPY_TO_GPU: &str = "copy_to_gpu";
pub static TO_RAW_PTR: &str = "to_raw_ptr";
pub static OFFSET_RAW_PTR: &str = "offset_raw_ptr";
pub static SHUFFLE_XOR: &str = "shuffle_xor";

pub static TO_VIEW: &str = "to_view";
pub static TO_VIEW_MUT: &str = "to_view_mut";
pub static GROUP: &str = "group";
pub static GROUP_MUT: &str = "group_mut";
pub static JOIN: &str = "join";
pub static JOIN_MUT: &str = "join_mut";
pub static TRANSPOSE: &str = "transpose";
pub static TRANSPOSE_MUT: &str = "transpose_mut";

pub static SPLIT_BLOCK_GRP: &str = "split_block_grp";
pub static GROUP_BLOCK_GRP: &str = "group_block_grp";
pub static JOIN_BLOCK_GRP: &str = "join_block_grp";

pub static TO_WARPS: &str = "to_warps";
pub static SPLIT_THREAD_GRP: &str = "split_thread_grp";
pub static SPLIT_WARP: &str = "split_warp";
pub static SPLIT_WARP_GRP: &str = "split_warp_grp";

pub static THREAD_ID_X: &str = "thread_id_x";

pub static ATOMIC_STORE: &str = "atomic_store";
pub static ATOMIC_LOAD: &str = "atomic_load";
pub static ATOMIC_FETCH_OR: &str = "atomic_fetch_or";
pub static ATOMIC_FETCH_ADD: &str = "atomic_fetch_add";

pub fn fun_decls() -> Vec<(&'static str, Ty)> {
    let decls = [
        // Built-in functions
        (GPU_DEVICE, gpu_device_ty()),
        (GPU_ALLOC, gpu_alloc_copy_ty()),
        (COPY_TO_HOST, copy_to_host_ty()),
        (EXEC, exec_ty()),
        (SHARED_ALLOC, shared_alloc_ty()),
        (COPY_TO_GPU, copy_to_gpu_ty()),
        (TO_RAW_PTR, to_raw_ptr_ty()),
        (OFFSET_RAW_PTR, offset_raw_ptr_ty()),
        (SHUFFLE_XOR, shuffle_xor_ty()),
        // View constructors
        (TO_VIEW, to_view_ty(Ownership::Shrd)),
        (TO_VIEW_MUT, to_view_ty(Ownership::Uniq)),
        (GROUP, group_ty(Ownership::Shrd)),
        (GROUP_MUT, group_ty(Ownership::Uniq)),
        (JOIN, join_ty(Ownership::Shrd)),
        (JOIN_MUT, join_ty(Ownership::Uniq)),
        (TRANSPOSE, transpose_ty(Ownership::Shrd)),
        (TRANSPOSE_MUT, transpose_ty(Ownership::Uniq)),
        (SPLIT_BLOCK_GRP, split_block_grp_ty()),
        //        (GROUP_BLOCK_GRP, group_block_grp_ty()),
        //        (JOIN_BLOCK_GRP, join_block_grp_ty()),
        (TO_WARPS, to_warps_ty()),
        (SPLIT_WARP_GRP, split_warp_grp_ty()),
        (SPLIT_THREAD_GRP, split_thread_grp_ty()),
        (SPLIT_WARP, split_warp_ty()),
        (THREAD_ID_X, thread_id_x_ty()),
        (ATOMIC_STORE, atomic_store_ty()),
        (ATOMIC_LOAD, atomic_load_ty()),
        (ATOMIC_FETCH_OR, atomic_fetch_or_ty()),
        (ATOMIC_FETCH_ADD, atomic_fetch_add_ty()),
    ];

    decls.to_vec()
}

// to_raw_ptr:
//  <r: prv, m: mem, t: ty> (
//      &r uniq m t
// ) -[gpu.thread]-> RawPtr<t>
fn to_raw_ptr_ty() -> Ty {
    let r = Ident::new("r");
    let m = Ident::new("m");
    let t = Ident::new("t");

    let r_prv = IdentKinded {
        ident: r.clone(),
        kind: Kind::Provenance,
    };
    let m_mem = IdentKinded {
        ident: m.clone(),
        kind: Kind::Memory,
    };
    let t_ty = IdentKinded {
        ident: t.clone(),
        kind: Kind::Ty,
    };

    Ty::new(TyKind::Fn(
        vec![r_prv, m_mem, t_ty],
        vec![Ty::new(TyKind::Data(DataTy::new(DataTyKind::Ref(
            Provenance::Ident(r),
            Ownership::Uniq,
            Memory::Ident(m),
            Box::new(DataTy::new(DataTyKind::Ident(t.clone()))),
        ))))],
        Exec::GpuThread,
        Box::new(Ty::new(TyKind::Data(DataTy::new(DataTyKind::RawPtr(
            Box::new(DataTy::new(DataTyKind::Ident(t))),
        ))))),
    ))
}

// offset_raw_ptr:
//  <m: mem, t: ty> (
//      RawPtr<t>, i32
// ) -[gpu.thread]-> RawPtr<t>
fn offset_raw_ptr_ty() -> Ty {
    let t = Ident::new("t");
    let t_ty = IdentKinded {
        ident: t.clone(),
        kind: Kind::Ty,
    };

    Ty::new(TyKind::Fn(
        vec![t_ty],
        vec![
            Ty::new(TyKind::Data(DataTy::new(DataTyKind::RawPtr(Box::new(
                DataTy::new(DataTyKind::Ident(t.clone())),
            ))))),
            Ty::new(TyKind::Data(DataTy::new(DataTyKind::Scalar(ScalarTy::I32)))),
        ],
        Exec::GpuThread,
        Box::new(Ty::new(TyKind::Data(DataTy::new(DataTyKind::RawPtr(
            Box::new(DataTy::new(DataTyKind::Ident(t))),
        ))))),
    ))
}

// shuffle_xor:
//  <d: dty>(d, i32) -> d
fn shuffle_xor_ty() -> Ty {
    let d = Ident::new("d");
    let d_dty = IdentKinded {
        ident: d.clone(),
        kind: Kind::DataTy,
    };
    Ty::new(TyKind::Fn(
        vec![d_dty],
        vec![
            Ty::new(TyKind::Data(DataTy::new(DataTyKind::Ident(d.clone())))),
            Ty::new(TyKind::Data(DataTy::new(DataTyKind::Scalar(ScalarTy::I32)))),
        ],
        Exec::GpuThread,
        Box::new(Ty::new(TyKind::Data(DataTy::new(DataTyKind::Ident(d))))),
    ))
}

// split_block_grp:
//  <k: nat, n1: nat, n2: nat, n3: nat>(
//      BlockGrp<n1, n2, n3, TH_HIER>
// ) -> (BlockGrp<k, n2, n3, TH_HIER>, BlockGrp<n1-k, n2, n3, TH_HIER>)
fn split_block_grp_ty() -> Ty {
    let k = Ident::new("k");
    let m1 = Ident::new("m1");
    let m2 = Ident::new("m2");
    let m3 = Ident::new("m3");
    let n1 = Ident::new("n1");
    let n2 = Ident::new("n2");
    let n3 = Ident::new("n3");
    let k_nat = IdentKinded {
        ident: k.clone(),
        kind: Kind::Nat,
    };
    let m1_nat = IdentKinded {
        ident: m1.clone(),
        kind: Kind::Nat,
    };
    let m2_nat = IdentKinded {
        ident: m2.clone(),
        kind: Kind::Nat,
    };
    let m3_nat = IdentKinded {
        ident: m3.clone(),
        kind: Kind::Nat,
    };
    let n1_nat = IdentKinded {
        ident: n1.clone(),
        kind: Kind::Nat,
    };
    let n2_nat = IdentKinded {
        ident: n2.clone(),
        kind: Kind::Nat,
    };
    let n3_nat = IdentKinded {
        ident: n3.clone(),
        kind: Kind::Nat,
    };
    Ty::new(TyKind::Fn(
        vec![k_nat, m1_nat, m2_nat, m3_nat, n1_nat, n2_nat, n3_nat],
        vec![Ty::new(TyKind::Data(DataTy::new(
            DataTyKind::ThreadHierchy(Box::new(ThreadHierchyTy::BlockGrp(
                Nat::Ident(m1.clone()),
                Nat::Ident(m2.clone()),
                Nat::Ident(m3.clone()),
                Nat::Ident(n1.clone()),
                Nat::Ident(n2.clone()),
                Nat::Ident(n3.clone()),
            ))),
        )))],
        Exec::View,
        Box::new(Ty::new(TyKind::Data(DataTy::new(DataTyKind::Tuple(vec![
            DataTy::new(DataTyKind::ThreadHierchy(Box::new(
                ThreadHierchyTy::BlockGrp(
                    Nat::Ident(k.clone()),
                    Nat::Ident(m2.clone()),
                    Nat::Ident(m3.clone()),
                    Nat::Ident(n1.clone()),
                    Nat::Ident(n2.clone()),
                    Nat::Ident(n3.clone()),
                ),
            ))),
            DataTy::new(DataTyKind::ThreadHierchy(Box::new(
                ThreadHierchyTy::BlockGrp(
                    Nat::BinOp(
                        BinOpNat::Sub,
                        Box::new(Nat::Ident(m1)),
                        Box::new(Nat::Ident(k)),
                    ),
                    Nat::Ident(m2),
                    Nat::Ident(m3),
                    Nat::Ident(n1),
                    Nat::Ident(n2),
                    Nat::Ident(n3),
                ),
            ))),
        ]))))),
    ))
}

// FIXME deal with n2, n3 dimensions
// to_warp_grp:
//      <n1: nat, n2: nat, n3: nat>(ThreadGrp<n1, n2, n3>) -> WarpGrp<n1/32>
fn to_warps_ty() -> Ty {
    let n1 = Ident::new("n1");
    let n2 = Ident::new("n2");
    let n3 = Ident::new("n3");
    let n1_nat = IdentKinded {
        ident: n1.clone(),
        kind: Kind::Nat,
    };
    let n2_nat = IdentKinded {
        ident: n2.clone(),
        kind: Kind::Nat,
    };
    let n3_nat = IdentKinded {
        ident: n3.clone(),
        kind: Kind::Nat,
    };
    Ty::new(TyKind::Fn(
        vec![n1_nat, n2_nat, n3_nat],
        vec![Ty::new(TyKind::Data(DataTy::new(
            DataTyKind::ThreadHierchy(Box::new(ThreadHierchyTy::ThreadGrp(
                Nat::Ident(n1.clone()),
                Nat::Ident(n2.clone()),
                Nat::Ident(n3.clone()),
            ))),
        )))],
        Exec::View,
        Box::new(Ty::new(TyKind::Data(DataTy::new(
            DataTyKind::ThreadHierchy(Box::new(ThreadHierchyTy::WarpGrp(Nat::BinOp(
                BinOpNat::Div,
                Box::new(Nat::Ident(n1)),
                Box::new(Nat::Lit(32)),
            )))),
        )))),
    ))
}

// group_block_grp:
//  <k: nat, n1: nat, n2: nat, n3: nat>(
//      ThreadGrp<n1, n2, n3>
// ) ->
fn split_thread_grp_ty() -> Ty {
    let k = Ident::new("k");
    let n1 = Ident::new("n1");
    let n2 = Ident::new("n2");
    let n3 = Ident::new("n3");
    let k_nat = IdentKinded {
        ident: k.clone(),
        kind: Kind::Nat,
    };
    let n1_nat = IdentKinded {
        ident: n1.clone(),
        kind: Kind::Nat,
    };
    let n2_nat = IdentKinded {
        ident: n2.clone(),
        kind: Kind::Nat,
    };
    let n3_nat = IdentKinded {
        ident: n3.clone(),
        kind: Kind::Nat,
    };
    let input_th_hy = Box::new(ThreadHierchyTy::ThreadGrp(
        Nat::Ident(n1.clone()),
        Nat::Ident(n2.clone()),
        Nat::Ident(n3.clone()),
    ));
    let input_ty = Ty::new(TyKind::Data(DataTy::new(DataTyKind::ThreadHierchy(
        input_th_hy.clone(),
    ))));
    Ty::new(TyKind::Fn(
        vec![k_nat, n1_nat, n2_nat, n3_nat],
        vec![input_ty],
        Exec::View,
        Box::new(Ty::new(TyKind::Data(DataTy::new(DataTyKind::SplitThreadHierchy(input_th_hy, Nat::Ident(k))))))
        // Box::new(Ty::new(TyKind::Data(DataTy::new(DataTyKind::Tuple(vec![
        //     DataTy::new(DataTyKind::ThreadHierchy(Box::new(
        //         ThreadHierchyTy::ThreadGrp(
        //             Nat::Ident(k.clone()),
        //             Nat::Ident(n2.clone()),
        //             Nat::Ident(n3.clone()),
        //         ),
        //     ))),
        //     DataTy::new(DataTyKind::ThreadHierchy(Box::new(
        //         ThreadHierchyTy::ThreadGrp(
        //             Nat::BinOp(
        //                 BinOpNat::Sub,
        //                 Box::new(Nat::Ident(n1)),
        //                 Box::new(Nat::Ident(k)),
        //             ),
        //             Nat::Ident(n2.clone()),
        //             Nat::Ident(n3.clone()),
        //         ),
        //     ))),
        // ]))))),
    ))
}

fn join_thread_grp_ty() -> Ty {
    unimplemented!()
    // let k = Ident::new("k");
    // let n1 = Ident::new("n1");
    // let n2 = Ident::new("n2");
    // let n3 = Ident::new("n3");
    // let k_nat = IdentKinded {
    //     ident: k.clone(),
    //     kind: Kind::Nat,
    // };
    // let n1_nat = IdentKinded {
    //     ident: n1.clone(),
    //     kind: Kind::Nat,
    // };
    // let n2_nat = IdentKinded {
    //     ident: n2.clone(),
    //     kind: Kind::Nat,
    // };
    // let n3_nat = IdentKinded {
    //     ident: n3.clone(),
    //     kind: Kind::Nat,
    // };
    // Ty::new(TyKind::Fn(
    //     vec![k_nat, n1_nat, n2_nat, n3_nat],
    //     vec![Ty::new(TyKind::Data(DataTy::new(
    //         DataTyKind::ThreadHierchy(Box::new(ThreadHierchyTy::ThreadGrp(
    //             Nat::Ident(n1.clone()),
    //             Nat::Ident(n2.clone()),
    //             Nat::Ident(n3.clone()),
    //         ))),
    //     )))],
    //     Exec::View,
    //     Box::new(Ty::new(TyKind::Data(DataTy::new(DataTyKind::Tuple(vec![
    //         Ty::new(TyKind::Data(DataTy::new(DataTyKind::ThreadHierchy(
    //             Box::new(ThreadHierchyTy::ThreadGrp(
    //                 Nat::Ident(k.clone()),
    //                 Nat::Ident(n2.clone()),
    //                 Nat::Ident(n3.clone()),
    //             )),
    //         )))),
    //         Ty::new(TyKind::Data(DataTy::new(DataTyKind::ThreadHierchy(
    //             Box::new(ThreadHierchyTy::ThreadGrp(
    //                 Nat::BinOp(
    //                     BinOpNat::Sub,
    //                     Box::new(Nat::Ident(n1)),
    //                     Box::new(Nat::Ident(k)),
    //                 ),
    //                 Nat::Ident(n2.clone()),
    //                 Nat::Ident(n3.clone()),
    //             )),
    //         )))),
    //     ]))),
    // ))
}

// split_warp_grp:
//  <k: nat, n: nat>(WarpGrp<n>) -[view]-> <WarpGrp<k>, WarpGrp<n-k>>
fn split_warp_grp_ty() -> Ty {
    let k = Ident::new("k");
    let n = Ident::new("n");
    let k_nat = IdentKinded {
        ident: k.clone(),
        kind: Kind::Nat,
    };
    let n_nat = IdentKinded {
        ident: n.clone(),
        kind: Kind::Nat,
    };
    Ty::new(TyKind::Fn(
        vec![k_nat, n_nat],
        vec![Ty::new(TyKind::Data(DataTy::new(
            DataTyKind::ThreadHierchy(Box::new(ThreadHierchyTy::WarpGrp(Nat::Ident(n.clone())))),
        )))],
        Exec::View,
        Box::new(Ty::new(TyKind::Data(DataTy::new(DataTyKind::Tuple(vec![
            DataTy::new(DataTyKind::ThreadHierchy(Box::new(
                ThreadHierchyTy::WarpGrp(Nat::Ident(k.clone())),
            ))),
            DataTy::new(DataTyKind::ThreadHierchy(Box::new(
                ThreadHierchyTy::WarpGrp(Nat::BinOp(
                    BinOpNat::Sub,
                    Box::new(Nat::Ident(n)),
                    Box::new(Nat::Ident(k)),
                )),
            ))),
        ]))))),
    ))
}

fn split_warp_ty() -> Ty {
    let k = Ident::new("k");
    let k_nat = IdentKinded {
        ident: k.clone(),
        kind: Kind::Nat,
    };
    Ty::new(TyKind::Fn(
        vec![k_nat],
        vec![Ty::new(TyKind::Data(DataTy::new(
            DataTyKind::ThreadHierchy(Box::new(ThreadHierchyTy::Warp)),
        )))],
        Exec::View,
        Box::new(Ty::new(TyKind::Data(DataTy::new(DataTyKind::Tuple(vec![
            DataTy::new(DataTyKind::ThreadHierchy(Box::new(
                ThreadHierchyTy::ThreadGrp(Nat::Ident(k.clone()), Nat::Lit(1), Nat::Lit(1)),
            ))),
            DataTy::new(DataTyKind::ThreadHierchy(Box::new(
                ThreadHierchyTy::ThreadGrp(
                    Nat::BinOp(
                        BinOpNat::Sub,
                        Box::new(Nat::Lit(32)),
                        Box::new(Nat::Ident(k)),
                    ),
                    Nat::Lit(1),
                    Nat::Lit(1),
                ),
            ))),
        ]))))),
    ))
}

// thread_id_x:
//  <>() -[gpu.thread]-> u32
fn thread_id_x_ty() -> Ty {
    Ty::new(TyKind::Fn(
        vec![],
        vec![],
        Exec::GpuThread,
        Box::new(Ty::new(TyKind::Data(DataTy::new(DataTyKind::Scalar(
            ScalarTy::U32
        ))))),
    ))
}

// atomic_store:
//  <>(AtomicU32, u32) -[gpu.thread]-> Unit
fn atomic_store_ty() -> Ty {
    let r = Ident::new("r");
    let m = Ident::new("m");
    let r_prv = IdentKinded {
        ident: r.clone(),
        kind: Kind::Provenance,
    };
    let m_mem = IdentKinded {
        ident: m.clone(),
        kind: Kind::Memory,
    };
    Ty::new(TyKind::Fn(
        vec![r_prv, m_mem],
        vec![
            Ty::new(TyKind::Data(DataTy::new(DataTyKind::Ref(
                Provenance::Ident(r),
                Ownership::Shrd,
                Memory::Ident(m),
                Box::new(DataTy::new(DataTyKind::Atomic(
                    AtomicTy::AtomicU32,
                ))),
            )))),
            Ty::new(TyKind::Data(DataTy::new(DataTyKind::Scalar(
                ScalarTy::U32,
            ))))
        ],
        Exec::GpuThread,
        Box::new(Ty::new(TyKind::Data(DataTy::new(DataTyKind::Scalar(
            ScalarTy::U32,
        ))))))
    )
}

// atomic_fetch_or:
//  <>(AtomicU32, u32) -[gpu.thread]-> u32
fn atomic_fetch_or_ty() -> Ty {
    let r = Ident::new("r");
    let m = Ident::new("m");
    let r_prv = IdentKinded {
        ident: r.clone(),
        kind: Kind::Provenance,
    };
    let m_mem = IdentKinded {
        ident: m.clone(),
        kind: Kind::Memory,
    };
    Ty::new(TyKind::Fn(
        vec![r_prv, m_mem],
        vec![
            Ty::new(TyKind::Data(DataTy::new(DataTyKind::Ref(
                Provenance::Ident(r),
                Ownership::Shrd,
                Memory::Ident(m),
                Box::new(DataTy::new(DataTyKind::Atomic(
                    AtomicTy::AtomicU32,
                ))),
            )))),
            Ty::new(TyKind::Data(DataTy::new(DataTyKind::Scalar(
                ScalarTy::U32,
            ))))
        ],
        Exec::GpuThread,
        Box::new(Ty::new(TyKind::Data(DataTy::new(DataTyKind::Scalar(
            ScalarTy::U32,
        ))))))
    )
}

// atomic_fetch_add:
//  <>(AtomicU32, u32) -[gpu.thread]-> u32
fn atomic_fetch_add_ty() -> Ty {
    let r = Ident::new("r");
    let m = Ident::new("m");
    let r_prv = IdentKinded {
        ident: r.clone(),
        kind: Kind::Provenance,
    };
    let m_mem = IdentKinded {
        ident: m.clone(),
        kind: Kind::Memory,
    };
    Ty::new(TyKind::Fn(
        vec![r_prv, m_mem],
        vec![
            Ty::new(TyKind::Data(DataTy::new(DataTyKind::Ref(
                Provenance::Ident(r),
                Ownership::Shrd,
                Memory::Ident(m),
                Box::new(DataTy::new(DataTyKind::Atomic(
                    AtomicTy::AtomicU32,
                ))),
            )))),
            Ty::new(TyKind::Data(DataTy::new(DataTyKind::Scalar(
                ScalarTy::U32,
            ))))
        ],
        Exec::GpuThread,
        Box::new(Ty::new(TyKind::Data(DataTy::new(DataTyKind::Scalar(
            ScalarTy::U32,
        ))))))
    )
}

// atomic_load:
//  <m: mem>(AtomicU32) -[gpu.thread]-> u32
fn atomic_load_ty() -> Ty {
    let r = Ident::new("r");
    let m = Ident::new("m");
    let r_prv = IdentKinded {
        ident: r.clone(),
        kind: Kind::Provenance,
    };
    let m_mem = IdentKinded {
        ident: m.clone(),
        kind: Kind::Memory,
    };
    Ty::new(TyKind::Fn(
        vec![r_prv, m_mem],
        vec![
            Ty::new(TyKind::Data(DataTy::new(DataTyKind::Ref(
                Provenance::Ident(r),
                Ownership::Shrd,
                Memory::Ident(m),
                Box::new(DataTy::new(DataTyKind::Atomic(
                    AtomicTy::AtomicU32,
                ))),
            )))),
        ],
        Exec::GpuThread,
        Box::new(Ty::new(TyKind::Data(DataTy::new(DataTyKind::Scalar(
            ScalarTy::U32,
        )))))
    ))
}

// gpu:
//   <>(i32) -[cpu.thread]-> Gpu
fn gpu_device_ty() -> Ty {
    Ty::new(TyKind::Fn(
        vec![],
        vec![Ty::new(TyKind::Data(DataTy::new(DataTyKind::Scalar(
            ScalarTy::I32,
        ))))],
        Exec::CpuThread,
        Box::new(Ty::new(TyKind::Data(DataTy::new(DataTyKind::Scalar(
            ScalarTy::Gpu,
        ))))),
    ))
}

// gpu_alloc:
//   <r1: prv, r2: prv, d: dty>(
//      &r1 uniq cpu.mem Gpu, &r2 shrd cpu.mem t
//   ) -[cpu.thread]-> t @ gpu.global
fn gpu_alloc_copy_ty() -> Ty {
    let r1 = Ident::new("r1");
    let r2 = Ident::new("r2");
    let d = Ident::new("d");
    let r1_prv = IdentKinded {
        ident: r1.clone(),
        kind: Kind::Provenance,
    };
    let r2_prv = IdentKinded {
        ident: r2.clone(),
        kind: Kind::Provenance,
    };
    let d_dty = IdentKinded {
        ident: d.clone(),
        kind: Kind::DataTy,
    };
    Ty::new(TyKind::Fn(
        vec![r1_prv, r2_prv, d_dty],
        vec![
            Ty::new(TyKind::Data(DataTy::new(DataTyKind::Ref(
                Provenance::Ident(r1),
                Ownership::Uniq,
                Memory::CpuMem,
                Box::new(DataTy::new(DataTyKind::Scalar(ScalarTy::Gpu))),
            )))),
            Ty::new(TyKind::Data(DataTy::new(DataTyKind::Ref(
                Provenance::Ident(r2),
                Ownership::Shrd,
                Memory::CpuMem,
                Box::new(DataTy::new(DataTyKind::Ident(d.clone()))),
            )))),
        ],
        Exec::CpuThread,
        Box::new(Ty::new(TyKind::Data(DataTy::new(DataTyKind::At(
            Box::new(DataTy::new(DataTyKind::Ident(d))),
            Memory::GpuGlobal,
        ))))),
    ))
}

// copy_to_host:
//   <r1: prv, r2: prv, d: dty>(&r1 shrd gpu.global d, &r2 uniq cpu.mem d)
//      -[cpu.thread]-> ()
fn copy_to_host_ty() -> Ty {
    let r1 = Ident::new("r1");
    let r2 = Ident::new("r2");
    let d = Ident::new("d");
    let r1_prv = IdentKinded {
        ident: r1.clone(),
        kind: Kind::Provenance,
    };
    let r2_prv = IdentKinded {
        ident: r2.clone(),
        kind: Kind::Provenance,
    };
    let d_dty = IdentKinded {
        ident: d.clone(),
        kind: Kind::DataTy,
    };
    Ty::new(TyKind::Fn(
        vec![r1_prv, r2_prv, d_dty],
        vec![
            Ty::new(TyKind::Data(DataTy::new(DataTyKind::Ref(
                Provenance::Ident(r1),
                Ownership::Shrd,
                Memory::GpuGlobal,
                Box::new(DataTy::new(DataTyKind::Ident(d.clone()))),
            )))),
            Ty::new(TyKind::Data(DataTy::new(DataTyKind::Ref(
                Provenance::Ident(r2),
                Ownership::Uniq,
                Memory::CpuMem,
                Box::new(DataTy::new(DataTyKind::Ident(d))),
            )))),
        ],
        Exec::CpuThread,
        Box::new(Ty::new(TyKind::Data(DataTy::new(DataTyKind::Scalar(
            ScalarTy::Unit,
        ))))),
    ))
}

// copy_to_gpu:
//  <r1: prv, r2: prv, d: dty>(& r1 uniq gpu.global d,
//      & r2 shrd cpu.mem d) -[cpu.thread]-> ()
fn copy_to_gpu_ty() -> Ty {
    let r1 = Ident::new("r1");
    let r2 = Ident::new("r2");
    let d = Ident::new("d");
    let r1_prv = IdentKinded {
        ident: r1.clone(),
        kind: Kind::Provenance,
    };
    let r2_prv = IdentKinded {
        ident: r2.clone(),
        kind: Kind::Provenance,
    };
    let d_dty = IdentKinded {
        ident: d.clone(),
        kind: Kind::DataTy,
    };
    Ty::new(TyKind::Fn(
        vec![r1_prv, r2_prv, d_dty],
        vec![
            Ty::new(TyKind::Data(DataTy::new(DataTyKind::Ref(
                Provenance::Ident(r1),
                Ownership::Uniq,
                Memory::GpuGlobal,
                Box::new(DataTy::new(DataTyKind::Ident(d.clone()))),
            )))),
            Ty::new(TyKind::Data(DataTy::new(DataTyKind::Ref(
                Provenance::Ident(r2),
                Ownership::Shrd,
                Memory::CpuMem,
                Box::new(DataTy::new(DataTyKind::Ident(d))),
            )))),
        ],
        Exec::CpuThread,
        Box::new(Ty::new(TyKind::Data(DataTy::new(DataTyKind::Scalar(
            ScalarTy::Unit,
        ))))),
    ))
}

// exec: <blocks: nat, threads: nat, r: prv, d: dty>(
//        &r uniq cpu.mem Gpu,
//        input: d,
//        (BlockGrp<blocks, 1, 1, ThreadGrp<Thread, threads, 1, 1>>, d) -[gpu.grid]-> ())
// -> ()
fn exec_ty() -> Ty {
    let blocks = Ident::new("blocks");
    let threads = Ident::new("threads");
    let r = Ident::new("r");
    let d = Ident::new("d");
    let blocks_nat = IdentKinded {
        ident: blocks.clone(),
        kind: Kind::Nat,
    };
    let threads_nat = IdentKinded {
        ident: threads.clone(),
        kind: Kind::Nat,
    };
    let r_prv = IdentKinded {
        ident: r.clone(),
        kind: Kind::Provenance,
    };
    let d_dty = IdentKinded {
        ident: d.clone(),
        kind: Kind::DataTy,
    };
    Ty::new(TyKind::Fn(
        vec![blocks_nat, threads_nat, r_prv, d_dty],
        vec![
            Ty::new(TyKind::Data(DataTy::new(DataTyKind::Ref(
                Provenance::Ident(r),
                Ownership::Uniq,
                Memory::CpuMem,
                Box::new(DataTy::new(DataTyKind::Scalar(ScalarTy::Gpu))),
            )))),
            Ty::new(TyKind::Data(DataTy::new(DataTyKind::Ident(d.clone())))),
            Ty::new(TyKind::Fn(
                vec![],
                vec![
                    Ty::new(TyKind::Data(DataTy::new(DataTyKind::ThreadHierchy(
                        Box::new(ThreadHierchyTy::BlockGrp(
                            Nat::Ident(blocks),
                            Nat::Lit(1),
                            Nat::Lit(1),
                            Nat::Ident(threads),
                            Nat::Lit(1),
                            Nat::Lit(1),
                        )),
                    )))),
                    Ty::new(TyKind::Data(DataTy::new(DataTyKind::Ident(d.clone())))),
                ],
                Exec::GpuGrid,
                Box::new(Ty::new(TyKind::Data(DataTy::new(DataTyKind::Scalar(
                    ScalarTy::Unit,
                ))))),
            )),
        ],
        Exec::CpuThread,
        Box::new(Ty::new(TyKind::Data(DataTy::new(DataTyKind::Scalar(
            ScalarTy::Unit,
        ))))),
    ))
}

// shared_alloc:
//  <t: ty>() -> t @ gpu.shared
fn shared_alloc_ty() -> Ty {
    let t = Ident::new("t");
    let t_ty = IdentKinded {
        ident: t.clone(),
        kind: Kind::Ty,
    };
    Ty::new(TyKind::Fn(
        vec![t_ty],
        vec![],
        Exec::GpuGrid,
        Box::new(Ty::new(TyKind::Data(DataTy::new(DataTyKind::At(
            Box::new(DataTy::new(DataTyKind::Ident(t))),
            Memory::GpuShared,
        ))))),
    ))
}

// TODO FIX Error: t: ty is too general this means it could contain functions
//  (which is not well-kinded).
// to_view:
//  <r: prv, m: mem, n: nat, d: dty>(&r shrd m [d; n]) -[view]-> &r shrd m [[d; n]]
// to_view_mut:
//  <r: prv, m: mem, n: nat, d: dty>(&r uniq m [d; n]) -[view]-> &r uniq m [[d; n]]
fn to_view_ty(own: Ownership) -> Ty {
    let r = Ident::new("r");
    let m = Ident::new("m");
    let n = Ident::new("n");
    let d = Ident::new("d");
    let r_prv = IdentKinded {
        ident: r.clone(),
        kind: Kind::Provenance,
    };
    let m_mem = IdentKinded {
        ident: m.clone(),
        kind: Kind::Memory,
    };
    let n_nat = IdentKinded {
        ident: n.clone(),
        kind: Kind::Nat,
    };
    let d_dty = IdentKinded {
        ident: d.clone(),
        kind: Kind::DataTy,
    };
    Ty::new(TyKind::Fn(
        vec![r_prv, m_mem, n_nat, d_dty],
        vec![Ty::new(TyKind::Data(DataTy::new(DataTyKind::Ref(
            Provenance::Ident(r.clone()),
            own,
            Memory::Ident(m.clone()),
            Box::new(DataTy::new(DataTyKind::Array(
                Box::new(DataTy::new(DataTyKind::Ident(d.clone()))),
                Nat::Ident(n.clone()),
            ))),
        ))))],
        Exec::View,
        Box::new(Ty::new(TyKind::Data(DataTy::new(DataTyKind::Ref(
            Provenance::Ident(r),
            own,
            Memory::Ident(m),
            Box::new(DataTy::new(DataTyKind::ArrayShape(
                Box::new(DataTy::new(DataTyKind::Ident(d))),
                Nat::Ident(n),
            ))),
        ))))),
    ))
}

// group/group_mut:
//  <size: nat, r: prv, m: mem, n: nat, d: dty>(&r W m [[d; n]]) -> &r W m [[ [[d; size]]; n/size ]]
fn group_ty(own: Ownership) -> Ty {
    let s = Ident::new("s");
    let r = Ident::new("r");
    let m = Ident::new("m");
    let n = Ident::new("n");
    let d = Ident::new("d");
    let s_nat = IdentKinded {
        ident: s.clone(),
        kind: Kind::Nat,
    };
    let r_prv = IdentKinded {
        ident: r.clone(),
        kind: Kind::Provenance,
    };
    let m_mem = IdentKinded {
        ident: m.clone(),
        kind: Kind::Memory,
    };
    let n_nat = IdentKinded {
        ident: n.clone(),
        kind: Kind::Nat,
    };
    let d_ty = IdentKinded {
        ident: d.clone(),
        kind: Kind::DataTy,
    };
    Ty::new(TyKind::Fn(
        vec![s_nat, r_prv, m_mem, n_nat, d_ty],
        vec![Ty::new(TyKind::Data(DataTy::new(DataTyKind::Ref(
            Provenance::Ident(r.clone()),
            own,
            Memory::Ident(m.clone()),
            Box::new(DataTy::new(DataTyKind::ArrayShape(
                Box::new(DataTy::new(DataTyKind::Ident(d.clone()))),
                Nat::Ident(n.clone()),
            ))),
        ))))],
        Exec::View,
        Box::new(Ty::new(TyKind::Data(DataTy::new(DataTyKind::Ref(
            Provenance::Ident(r),
            own,
            Memory::Ident(m),
            Box::new(DataTy::new(DataTyKind::ArrayShape(
                Box::new(DataTy::new(DataTyKind::ArrayShape(
                    Box::new(DataTy::new(DataTyKind::Ident(d))),
                    Nat::Ident(s.clone()),
                ))),
                Nat::BinOp(
                    BinOpNat::Div,
                    Box::new(Nat::Ident(n)),
                    Box::new(Nat::Ident(s)),
                ),
            ))),
        ))))),
    ))
}

// +: <t: ty>(t, t) -> t
fn bin_op() -> Ty {
    let t = Ident::new("t");
    let t_ty = IdentKinded {
        ident: t.clone(),
        kind: Kind::Ty,
    };
    Ty::new(TyKind::Fn(
        vec![t_ty],
        vec![Ty::new(TyKind::Data(DataTy::new(DataTyKind::Ident(
            t.clone(),
        ))))],
        Exec::GpuThread,
        Box::new(Ty::new(TyKind::Data(DataTy::new(DataTyKind::Ident(t))))),
    ))
}

// join/join_mut:
//  <r: prv, m: mem, o: nat, n: nat, d: dty>(&r W m [[ [[d; n]]; o]]) -> [[d; n*o]]
fn join_ty(own: Ownership) -> Ty {
    let r = Ident::new("r");
    let m = Ident::new("m");
    let n = Ident::new("n");
    let o = Ident::new("o");
    let d = Ident::new("d");
    let r_prv = IdentKinded {
        ident: r.clone(),
        kind: Kind::Provenance,
    };
    let m_mem = IdentKinded {
        ident: m.clone(),
        kind: Kind::Memory,
    };
    let n_nat = IdentKinded {
        ident: n.clone(),
        kind: Kind::Nat,
    };
    let o_nat = IdentKinded {
        ident: o.clone(),
        kind: Kind::Nat,
    };
    let d_dty = IdentKinded {
        ident: d.clone(),
        kind: Kind::DataTy,
    };
    Ty::new(TyKind::Fn(
        vec![r_prv, m_mem, o_nat, n_nat, d_dty],
        vec![Ty::new(TyKind::Data(DataTy::new(DataTyKind::Ref(
            Provenance::Ident(r.clone()),
            own,
            Memory::Ident(m.clone()),
            Box::new(DataTy::new(DataTyKind::ArrayShape(
                Box::new(DataTy::new(DataTyKind::ArrayShape(
                    Box::new(DataTy::new(DataTyKind::Ident(d.clone()))),
                    Nat::Ident(n.clone()),
                ))),
                Nat::Ident(o.clone()),
            ))),
        ))))],
        Exec::View,
        Box::new(Ty::new(TyKind::Data(DataTy::new(DataTyKind::Ref(
            Provenance::Ident(r),
            own,
            Memory::Ident(m),
            Box::new(DataTy::new(DataTyKind::ArrayShape(
                Box::new(DataTy::new(DataTyKind::Ident(d))),
                Nat::BinOp(
                    BinOpNat::Mul,
                    Box::new(Nat::Ident(n)),
                    Box::new(Nat::Ident(o)),
                ),
            ))),
        ))))),
    ))
}

// transpose:
//  <r: prv, m: mem, n: nat, o: nat, d: dty>(&r W m [[ [[d; n]]; o]]) -> &r W m [[ [[d; o]]; n]]
fn transpose_ty(own: Ownership) -> Ty {
    let r = Ident::new("r");
    let m = Ident::new("m");
    let n = Ident::new("n");
    let o = Ident::new("o");
    let d = Ident::new("d");
    let r_prv = IdentKinded {
        ident: r.clone(),
        kind: Kind::Provenance,
    };
    let m_mem = IdentKinded {
        ident: m.clone(),
        kind: Kind::Memory,
    };
    let o_nat = IdentKinded {
        ident: o.clone(),
        kind: Kind::Nat,
    };
    let n_nat = IdentKinded {
        ident: n.clone(),
        kind: Kind::Nat,
    };
    let d_ty = IdentKinded {
        ident: d.clone(),
        kind: Kind::DataTy,
    };
    Ty::new(TyKind::Fn(
        vec![r_prv, m_mem, n_nat, o_nat, d_ty],
        vec![Ty::new(TyKind::Data(DataTy::new(DataTyKind::Ref(
            Provenance::Ident(r.clone()),
            own,
            Memory::Ident(m.clone()),
            Box::new(DataTy::new(DataTyKind::ArrayShape(
                Box::new(DataTy::new(DataTyKind::ArrayShape(
                    Box::new(DataTy::new(DataTyKind::Ident(d.clone()))),
                    Nat::Ident(n.clone()),
                ))),
                Nat::Ident(o.clone()),
            ))),
        ))))],
        Exec::View,
        Box::new(Ty::new(TyKind::Data(DataTy::new(DataTyKind::Ref(
            Provenance::Ident(r),
            own,
            Memory::Ident(m),
            Box::new(DataTy::new(DataTyKind::ArrayShape(
                Box::new(DataTy::new(DataTyKind::ArrayShape(
                    Box::new(DataTy::new(DataTyKind::Ident(d))),
                    Nat::Ident(o),
                ))),
                Nat::Ident(n),
            ))),
        ))))),
    ))
}
