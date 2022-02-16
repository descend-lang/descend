use crate::ast::{
    BinOpNat, DataTy, Exec, Ident, IdentKinded, Kind, Memory, Nat, Ownership, Provenance, ScalarTy,
    ThreadHierchyTy, Ty, TyKind,
};

pub static GPU_DEVICE: &str = "gpu_device";
pub static GPU_ALLOC: &str = "gpu_alloc";
pub static COPY_TO_HOST: &str = "copy_to_host";
pub static EXEC: &str = "exec";
pub static SHARED_ALLOC: &str = "shared_alloc";
pub static COPY_TO_GPU: &str = "copy_to_gpu";
pub static LOAD_ATOMIC: &str = "load_atomic";
pub static LOAD_ATOMIC_HOST: &str = "load_atomic_host";
pub static STORE_ATOMIC: &str = "store_atomic";
pub static STORE_ATOMIC_HOST: &str = "store_atomic_host";
pub static TO_RAW_PTR: &str = "to_raw_ptr";
pub static OFFSET_RAW_PTR: &str = "offset_raw_ptr";
pub static ATOMIC_SET: &str = "atomic_set";

pub static TO_VIEW: &str = "to_view";
pub static TO_VIEW_MUT: &str = "to_view_mut";
pub static SPLIT_AT: &str = "split_at";
pub static GROUP: &str = "group";
pub static GROUP_MUT: &str = "group_mut";
pub static JOIN: &str = "join";
pub static ZIP: &str = "zip";
pub static TRANSPOSE: &str = "transpose";

pub static SPLIT_THREAD_GRP: &str = "split_thread_grp";
pub static SPLIT_WARP: &str = "split_warp";

pub fn fun_decls() -> Vec<(&'static str, Ty)> {
    let decls = [
        // Built-in functions
        (GPU_DEVICE, gpu_device_ty()),
        (GPU_ALLOC, gpu_alloc_ty()),
        (COPY_TO_HOST, copy_to_host_ty()),
        (EXEC, exec_ty()),
        (SHARED_ALLOC, shared_alloc_ty()),
        (COPY_TO_GPU, copy_to_gpu_ty()),
        (LOAD_ATOMIC, load_atomic_ty()),
        (LOAD_ATOMIC_HOST, load_atomic_host_ty()),
        (STORE_ATOMIC, store_atomic_ty()),
        (STORE_ATOMIC_HOST, store_atomic_host_ty()),
        (TO_RAW_PTR, to_raw_ptr_ty()),
        (OFFSET_RAW_PTR, offset_raw_ptr_ty()),
        (ATOMIC_SET, atomic_set_ty()),
        // View constructors
        (TO_VIEW, to_view_ty(Ownership::Shrd)),
        (TO_VIEW_MUT, to_view_ty(Ownership::Uniq)),
        //(SPLIT_AT, split_at_ty()),
        // (ZIP, zip_ty()),
        (GROUP, group_ty(Ownership::Shrd)),
        (GROUP_MUT, group_ty(Ownership::Uniq)),
        (SPLIT_THREAD_GRP, split_thread_grp_ty()),
        (SPLIT_WARP, split_warp_ty()),
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
        vec![Ty::new(TyKind::Data(DataTy::Ref(
            Provenance::Ident(r),
            Ownership::Uniq,
            Memory::Ident(m),
            Box::new(DataTy::Ident(t.clone())),
        )))],
        Exec::GpuThread,
        Box::new(Ty::new(TyKind::Data(DataTy::RawPtr(Box::new(
            DataTy::Ident(t),
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
            Ty::new(TyKind::Data(DataTy::RawPtr(Box::new(DataTy::Ident(
                t.clone(),
            ))))),
            Ty::new(TyKind::Data(DataTy::Scalar(ScalarTy::I32))),
        ],
        Exec::GpuThread,
        Box::new(Ty::new(TyKind::Data(DataTy::RawPtr(Box::new(
            DataTy::Ident(t),
        ))))),
    ))
}

fn atomic_set_ty() -> Ty {
    let p = Ident::new("p");
    let m = Ident::new("m");
    let t = Ident::new("t");

    let p_prv = IdentKinded {
        ident: p.clone(),
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
        vec![p_prv, m_mem, t_ty],
        vec![
            Ty::new(TyKind::Data(DataTy::Ref(
                Provenance::Ident(p),
                Ownership::Uniq,
                Memory::Ident(m),
                Box::new(DataTy::Ident(t.clone())),
            ))),
            Ty::new(TyKind::Data(DataTy::Ident(t))),
        ],
        Exec::GpuThread,
        Box::new(Ty::new(TyKind::Data(DataTy::Scalar(ScalarTy::Unit)))),
    ))
}

// split_block_grp:
//  <k: nat, n1: nat, n2: nat, n3: nat>(
//      ThreadGrp<n1, n2, n3>
// ) -> <ThreadGrp<k, n2, n3>, ThreadGrp<n1-k, n2, n3>>
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
    Ty::new(TyKind::Fn(
        vec![k_nat, n1_nat, n2_nat, n3_nat],
        vec![Ty::new(TyKind::Data(DataTy::ThreadHierchy(Box::new(
            ThreadHierchyTy::ThreadGrp(
                Nat::Ident(n1.clone()),
                Nat::Ident(n2.clone()),
                Nat::Ident(n3.clone()),
            ),
        ))))],
        Exec::View,
        Box::new(Ty::new(TyKind::TupleView(vec![
            Ty::new(TyKind::Data(DataTy::ThreadHierchy(Box::new(
                ThreadHierchyTy::ThreadGrp(
                    Nat::Ident(k.clone()),
                    Nat::Ident(n2.clone()),
                    Nat::Ident(n3.clone()),
                ),
            )))),
            Ty::new(TyKind::Data(DataTy::ThreadHierchy(Box::new(
                ThreadHierchyTy::ThreadGrp(
                    Nat::BinOp(
                        BinOpNat::Sub,
                        Box::new(Nat::Ident(n1)),
                        Box::new(Nat::Ident(k)),
                    ),
                    Nat::Ident(n2.clone()),
                    Nat::Ident(n3.clone()),
                ),
            )))),
        ]))),
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
        vec![Ty::new(TyKind::Data(DataTy::ThreadHierchy(Box::new(
            ThreadHierchyTy::Warp,
        ))))],
        Exec::View,
        Box::new(Ty::new(TyKind::TupleView(vec![
            Ty::new(TyKind::Data(DataTy::ThreadHierchy(Box::new(
                ThreadHierchyTy::ThreadGrp(Nat::Ident(k.clone()), Nat::Lit(1), Nat::Lit(1)),
            )))),
            Ty::new(TyKind::Data(DataTy::ThreadHierchy(Box::new(
                ThreadHierchyTy::ThreadGrp(
                    Nat::BinOp(
                        BinOpNat::Sub,
                        Box::new(Nat::Lit(32)),
                        Box::new(Nat::Ident(k)),
                    ),
                    Nat::Lit(1),
                    Nat::Lit(1),
                ),
            )))),
        ]))),
    ))
}

// gpu:
//   <>(i32) -[cpu.thread]-> Gpu
fn gpu_device_ty() -> Ty {
    Ty::new(TyKind::Fn(
        vec![],
        vec![Ty::new(TyKind::Data(DataTy::Scalar(ScalarTy::I32)))],
        Exec::CpuThread,
        Box::new(Ty::new(TyKind::Data(DataTy::Scalar(ScalarTy::Gpu)))),
    ))
}

//  <r: prv, m: mem>(&r shrd m Atomic<i32>) -[gpu.global]-> i32
fn load_atomic_ty() -> Ty {
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
        vec![Ty::new(TyKind::Data(DataTy::Ref(
            Provenance::Ident(r),
            Ownership::Shrd,
            Memory::Ident(m),
            Box::new(DataTy::Atomic(ScalarTy::I32)),
        )))],
        Exec::GpuThread,
        Box::new(Ty::new(TyKind::Data(DataTy::Scalar(ScalarTy::I32)))),
    ))
}

fn load_atomic_host_ty() -> Ty {
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
        vec![Ty::new(TyKind::Data(DataTy::Ref(
            Provenance::Ident(r),
            Ownership::Shrd,
            Memory::Ident(m),
            Box::new(DataTy::Atomic(ScalarTy::I32)),
        )))],
        Exec::CpuThread,
        Box::new(Ty::new(TyKind::Data(DataTy::Scalar(ScalarTy::I32)))),
    ))
}

// <r: prv, m: mem>(&r shrd m t, i32) -[gpu.global]-> ()
fn store_atomic_ty() -> Ty {
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
            Ty::new(TyKind::Data(DataTy::Ref(
                Provenance::Ident(r),
                Ownership::Shrd,
                Memory::Ident(m),
                Box::new(DataTy::Atomic(ScalarTy::I32)),
            ))),
            Ty::new(TyKind::Data(DataTy::Scalar(ScalarTy::I32))),
        ],
        Exec::GpuThread,
        Box::new(Ty::new(TyKind::Data(DataTy::Scalar(ScalarTy::Unit)))),
    ))
}

// <r: prv, m: mem>(&r shrd m t, i32) -[gpu.global]-> ()
fn store_atomic_host_ty() -> Ty {
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
            Ty::new(TyKind::Data(DataTy::Ref(
                Provenance::Ident(r),
                Ownership::Shrd,
                Memory::Ident(m),
                Box::new(DataTy::Atomic(ScalarTy::I32)),
            ))),
            Ty::new(TyKind::Data(DataTy::Scalar(ScalarTy::I32))),
        ],
        Exec::CpuThread,
        Box::new(Ty::new(TyKind::Data(DataTy::Scalar(ScalarTy::Unit)))),
    ))
}

// gpu_alloc:
//   <r1: prv, r2: prv, m1: mem, m2: mem, d: dty>(
//      &r1 uniq m1 Gpu, &r2 shrd m2 t
//   ) -[cpu.thread]-> t @ gpu.global
fn gpu_alloc_ty() -> Ty {
    let r1 = Ident::new("r1");
    let r2 = Ident::new("r2");
    let m1 = Ident::new("m1");
    let m2 = Ident::new("m2");
    let d = Ident::new("d");
    let r1_prv = IdentKinded {
        ident: r1.clone(),
        kind: Kind::Provenance,
    };
    let m1_mem = IdentKinded {
        ident: m1.clone(),
        kind: Kind::Memory,
    };
    let r2_prv = IdentKinded {
        ident: r2.clone(),
        kind: Kind::Provenance,
    };
    let m2_mem = IdentKinded {
        ident: m2.clone(),
        kind: Kind::Memory,
    };
    let d_dty = IdentKinded {
        ident: d.clone(),
        kind: Kind::DataTy,
    };
    Ty::new(TyKind::Fn(
        vec![r1_prv, r2_prv, m1_mem, m2_mem, d_dty],
        vec![
            Ty::new(TyKind::Data(DataTy::Ref(
                Provenance::Ident(r1),
                Ownership::Uniq,
                Memory::Ident(m1),
                Box::new(DataTy::Scalar(ScalarTy::Gpu)),
            ))),
            Ty::new(TyKind::Data(DataTy::Ref(
                Provenance::Ident(r2),
                Ownership::Shrd,
                Memory::Ident(m2),
                Box::new(DataTy::Ident(d.clone())),
            ))),
        ],
        Exec::CpuThread,
        Box::new(Ty::new(TyKind::Data(DataTy::At(
            Box::new(DataTy::Ident(d)),
            Memory::GpuGlobal,
        )))),
    ))
}

// copy_to_host:
//   <r1: prv, r2: prv, m: mem, d: dty>(&r1 shrd gpu.global d, &r2 uniq m d)
//      -[cpu.thread]-> ()
fn copy_to_host_ty() -> Ty {
    let r1 = Ident::new("r1");
    let r2 = Ident::new("r2");
    let m = Ident::new("m");
    let d = Ident::new("d");
    let r1_prv = IdentKinded {
        ident: r1.clone(),
        kind: Kind::Provenance,
    };
    let r2_prv = IdentKinded {
        ident: r2.clone(),
        kind: Kind::Provenance,
    };
    let m_mem = IdentKinded {
        ident: m.clone(),
        kind: Kind::Memory,
    };
    let d_dty = IdentKinded {
        ident: d.clone(),
        kind: Kind::DataTy,
    };
    Ty::new(TyKind::Fn(
        vec![r1_prv, r2_prv, m_mem, d_dty],
        vec![
            Ty::new(TyKind::Data(DataTy::Ref(
                Provenance::Ident(r1),
                Ownership::Shrd,
                Memory::GpuGlobal,
                Box::new(DataTy::Ident(d.clone())),
            ))),
            Ty::new(TyKind::Data(DataTy::Ref(
                Provenance::Ident(r2),
                Ownership::Uniq,
                Memory::Ident(m),
                Box::new(DataTy::Ident(d)),
            ))),
        ],
        Exec::CpuThread,
        Box::new(Ty::new(TyKind::Data(DataTy::Scalar(ScalarTy::Unit)))),
    ))
}

// copy_to_gpu:
//  <r1: prv, r2: prv, d: dty>(& r1 uniq gpu.global d,
//      & r2 shrd cpu.heap d) -[cpu.thread]-> ()
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
            Ty::new(TyKind::Data(DataTy::Ref(
                Provenance::Ident(r1),
                Ownership::Uniq,
                Memory::GpuGlobal,
                Box::new(DataTy::Ident(d.clone())),
            ))),
            Ty::new(TyKind::Data(DataTy::Ref(
                Provenance::Ident(r2),
                Ownership::Shrd,
                Memory::CpuHeap,
                Box::new(DataTy::Ident(d)),
            ))),
        ],
        Exec::CpuThread,
        Box::new(Ty::new(TyKind::Data(DataTy::Scalar(ScalarTy::Unit)))),
    ))
}

// exec: <blocks: nat, threads: nat, r: prv, m: mem, t: ty>(
//        &r uniq m Gpu,
//        input: t,
//        (BlockGrp<blocks, 1, 1, ThreadGrp<Thread, threads, 1, 1>>, t) -[gpu.grid]-> ())
// -> ()
fn exec_ty() -> Ty {
    let blocks = Ident::new("blocks");
    let threads = Ident::new("threads");
    let r = Ident::new("r");
    let m = Ident::new("m");
    let t = Ident::new("t");
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
    let m_mem = IdentKinded {
        ident: m.clone(),
        kind: Kind::Memory,
    };
    let t_ty = IdentKinded {
        ident: t.clone(),
        kind: Kind::Ty,
    };
    Ty::new(TyKind::Fn(
        vec![blocks_nat, threads_nat, r_prv, m_mem, t_ty],
        vec![
            Ty::new(TyKind::Data(DataTy::Ref(
                Provenance::Ident(r),
                Ownership::Uniq,
                Memory::Ident(m),
                Box::new(DataTy::Scalar(ScalarTy::Gpu)),
            ))),
            Ty::new(TyKind::Ident(t.clone())),
            Ty::new(TyKind::Fn(
                vec![],
                vec![
                    // Ty::View(ViewTy::Array(
                    //     Box::new(Ty::View(ViewTy::Array(
                    //         Box::new(Ty::Data(DataTy::Scalar(ScalarTy::Thread))),
                    //         Nat::Ident(threads),
                    //     ))),
                    //     Nat::Ident(blocks),
                    // )),
                    Ty::new(TyKind::Data(DataTy::ThreadHierchy(Box::new(
                        ThreadHierchyTy::BlockGrp(
                            Nat::Ident(blocks),
                            Nat::Lit(1),
                            Nat::Lit(1),
                            Nat::Ident(threads),
                            Nat::Lit(1),
                            Nat::Lit(1),
                        ),
                    )))),
                    Ty::new(TyKind::Ident(t)),
                ],
                Exec::GpuGrid,
                Box::new(Ty::new(TyKind::Data(DataTy::Scalar(ScalarTy::Unit)))),
            )),
        ],
        Exec::CpuThread,
        Box::new(Ty::new(TyKind::Data(DataTy::Scalar(ScalarTy::Unit)))),
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
        Box::new(Ty::new(TyKind::Data(DataTy::At(
            Box::new(DataTy::Ident(t)),
            Memory::GpuShared,
        )))),
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
        vec![Ty::new(TyKind::Data(DataTy::Ref(
            Provenance::Ident(r.clone()),
            own,
            Memory::Ident(m.clone()),
            Box::new(DataTy::Array(
                Box::new(DataTy::Ident(d.clone())),
                Nat::Ident(n.clone()),
            )),
        )))],
        Exec::View,
        Box::new(Ty::new(TyKind::Data(DataTy::Ref(
            Provenance::Ident(r),
            own,
            Memory::Ident(m),
            Box::new(DataTy::ArrayShape(
                Box::new(DataTy::Ident(d)),
                Nat::Ident(n),
            )),
        )))),
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
        vec![Ty::new(TyKind::Data(DataTy::Ref(
            Provenance::Ident(r.clone()),
            own,
            Memory::Ident(m.clone()),
            Box::new(DataTy::ArrayShape(
                Box::new(DataTy::Ident(d.clone())),
                Nat::Ident(n.clone()),
            )),
        )))],
        Exec::View,
        Box::new(Ty::new(TyKind::Data(DataTy::Ref(
            Provenance::Ident(r),
            own,
            Memory::Ident(m),
            Box::new(DataTy::ArrayShape(
                Box::new(DataTy::ArrayShape(
                    Box::new(DataTy::Ident(d)),
                    Nat::Ident(s.clone()),
                )),
                Nat::BinOp(
                    BinOpNat::Div,
                    Box::new(Nat::Ident(n)),
                    Box::new(Nat::Ident(s)),
                ),
            )),
        )))),
    ))
}

// join:
//  <m: nat, n: nat, t: ty>([[ [[t; n]]; m]]) -> [[t; m*n]]
// fn join_ty() -> Ty {
//     let m = Ident::new("m");
//     let n = Ident::new("n");
//     let t = Ident::new("t");
//     let m_nat = IdentKinded {
//         ident: m.clone(),
//         kind: Kind::Nat,
//     };
//     let n_nat = IdentKinded {
//         ident: n.clone(),
//         kind: Kind::Nat,
//     };
//     let t_ty = IdentKinded {
//         ident: t.clone(),
//         kind: Kind::Ty,
//     };
//     Ty::new(TyKind::Fn(
//         vec![m_nat, n_nat, t_ty],
//         vec![Ty::new(TyKind::View(ViewTy::Array(
//             Box::new(Ty::new(TyKind::View(ViewTy::Array(
//                 Box::new(Ty::new(TyKind::Ident(t.clone()))),
//                 Nat::Ident(n.clone()),
//             )))),
//             Nat::Ident(m.clone()),
//         )))],
//         Exec::View,
//         Box::new(Ty::new(TyKind::View(ViewTy::Array(
//             Box::new(Ty::new(TyKind::Ident(t))),
//             Nat::BinOp(
//                 BinOpNat::Mul,
//                 Box::new(Nat::Ident(m)),
//                 Box::new(Nat::Ident(n)),
//             ),
//         )))),
//     ))
// }

// transpose:
//  <m: nat, n: nat, t: ty>([[ [[t; n]]; m]]) -> [[ [[t; m]]; n]]
// fn transpose_ty() -> Ty {
//     let m = Ident::new("m");
//     let n = Ident::new("n");
//     let t = Ident::new("t");
//     let m_nat = IdentKinded {
//         ident: m.clone(),
//         kind: Kind::Nat,
//     };
//     let n_nat = IdentKinded {
//         ident: n.clone(),
//         kind: Kind::Nat,
//     };
//     let t_ty = IdentKinded {
//         ident: t.clone(),
//         kind: Kind::Ty,
//     };
//     Ty::new(TyKind::Fn(
//         vec![m_nat, n_nat, t_ty],
//         vec![Ty::new(TyKind::View(ViewTy::Array(
//             Box::new(Ty::new(TyKind::View(ViewTy::Array(
//                 Box::new(Ty::new(TyKind::Ident(t.clone()))),
//                 Nat::Ident(n.clone()),
//             )))),
//             Nat::Ident(m.clone()),
//         )))],
//         Exec::View,
//         Box::new(Ty::new(TyKind::View(ViewTy::Array(
//             Box::new(Ty::new(TyKind::View(ViewTy::Array(
//                 Box::new(Ty::new(TyKind::Ident(t))),
//                 Nat::Ident(m),
//             )))),
//             Nat::Ident(n),
//         )))),
//     ))
// }

// zip:
//  <n: nat, r1: prv, r2: prv, m1: mem, m2: mem, t1: ty, t2:ty>(
//      &r1 W1 m1 [[t1; n]], &r2 W2 m2 [[t2; n]]
//  ) -> ZipView<&r1 W1 m1 [[t1; n]], &r2 W2 m2 [[t2; n]]>
// fn zip_ty() -> Ty {
//     let n = Ident::new("n");
//     let t1 = Ident::new("t1");
//     let t2 = Ident::new("t2");
//     let n_nat = IdentKinded {
//         ident: n.clone(),
//         kind: Kind::Nat,
//     };
//     let t1_ty = IdentKinded {
//         ident: t1.clone(),
//         kind: Kind::Ty,
//     };
//     let t2_ty = IdentKinded {
//         ident: t2.clone(),
//         kind: Kind::Ty,
//     };
//     Ty::new(TyKind::Fn(
//         vec![n_nat, t1_ty, t2_ty],
//         vec![
//             Ty::new(TyKind::View(ViewTy::Array(
//                 Box::new(Ty::new(TyKind::Ident(t1.clone()))),
//                 Nat::Ident(n.clone()),
//             ))),
//             Ty::new(TyKind::View(ViewTy::Array(
//                 Box::new(Ty::new(TyKind::Ident(t2.clone()))),
//                 Nat::Ident(n.clone()),
//             ))),
//         ],
//         Exec::View,
//         Box::new(Ty::new(TyKind::View(ViewTy::Array(
//             Box::new(Ty::new(TyKind::View(ViewTy::Tuple(vec![
//                 Ty::new(TyKind::Ident(t1)),
//                 Ty::new(TyKind::Ident(t2)),
//             ])))),
//             Nat::Ident(n),
//         )))),
//     ))
// }

// split:
//  <s: nat, n: nat, t: ty>(&[[t; n]]) -> <[[t; s]], [[t; n-s]]>
// fn split_at_ty() -> Ty {
//     let s = Ident::new("s");
//     let n = Ident::new("n");
//     let t = Ident::new("t");
//     let s_nat = IdentKinded {
//         ident: s.clone(),
//         kind: Kind::Nat,
//     };
//     let n_nat = IdentKinded {
//         ident: n.clone(),
//         kind: Kind::Nat,
//     };
//     let t_ty = IdentKinded {
//         ident: t.clone(),
//         kind: Kind::Ty,
//     };
//     Ty::new(TyKind::Fn(
//         vec![s_nat, n_nat, t_ty],
//         vec![Ty::new(TyKind::View(ViewTy::Array(
//             Box::new(Ty::new(TyKind::Ident(t.clone()))),
//             Nat::Ident(n.clone()),
//         )))],
//         Exec::View,
//         Box::new(Ty::new(TyKind::View(ViewTy::Tuple(vec![
//             Ty::new(TyKind::View(ViewTy::Array(
//                 Box::new(Ty::new(TyKind::Ident(t.clone()))),
//                 Nat::Ident(s.clone()),
//             ))),
//             Ty::new(TyKind::View(ViewTy::Array(
//                 Box::new(Ty::new(TyKind::Ident(t))),
//                 Nat::BinOp(
//                     BinOpNat::Sub,
//                     Box::new(Nat::Ident(n)),
//                     Box::new(Nat::Ident(s)),
//                 ),
//             ))),
//         ])))),
//     ))
// }
