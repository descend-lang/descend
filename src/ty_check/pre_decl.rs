use crate::ast::{
    BinOpNat, DataTy, DataTyKind, Dim, ExecTy, ExecTyKind, FnTy, Ident, IdentKinded, Kind, Memory,
    Nat, Ownership, Provenance, ScalarTy, Ty, TyKind,
};

pub static GPU_DEVICE: &str = "gpu_device";
pub static GPU_ALLOC: &str = "gpu_alloc_copy";
pub static COPY_TO_HOST: &str = "copy_to_host";
pub static EXEC: &str = "exec";
pub static EXEC_XY: &str = "exec_xy";
// pub static SHARED_ALLOC: &str = "shared_alloc";
pub static COPY_TO_GPU: &str = "copy_to_gpu";
pub static LOAD_ATOMIC: &str = "load_atomic";
pub static LOAD_ATOMIC_HOST: &str = "load_atomic_host";
pub static STORE_ATOMIC: &str = "store_atomic";
pub static STORE_ATOMIC_HOST: &str = "store_atomic_host";
pub static TO_RAW_PTR: &str = "to_raw_ptr";
pub static OFFSET_RAW_PTR: &str = "offset_raw_ptr";
pub static ATOMIC_SET: &str = "atomic_set";
pub static SHUFFLE_XOR: &str = "shuffle_xor";

pub static TO_VIEW: &str = "to_view";
pub static TO_VIEW_MUT: &str = "to_view_mut";
pub static GROUP: &str = "group";
pub static GROUP_MUT: &str = "group_mut";
pub static JOIN: &str = "join";
pub static JOIN_MUT: &str = "join_mut";
pub static TRANSPOSE: &str = "transpose";
pub static TRANSPOSE_MUT: &str = "transpose_mut";

pub fn fun_decls() -> Vec<(&'static str, FnTy)> {
    let decls = [
        // Built-in functions
        (GPU_DEVICE, gpu_device_ty()),
        (GPU_ALLOC, gpu_alloc_copy_ty()),
        (COPY_TO_HOST, copy_to_host_ty()),
        (EXEC, exec_x_ty()),
        (EXEC_XY, exec_xy_ty()),
        // (SHARED_ALLOC, shared_alloc_ty()),
        (COPY_TO_GPU, copy_to_gpu_ty()),
        (LOAD_ATOMIC, load_atomic_ty()),
        (LOAD_ATOMIC_HOST, load_atomic_host_ty()),
        (STORE_ATOMIC, store_atomic_ty()),
        (STORE_ATOMIC_HOST, store_atomic_host_ty()),
        (TO_RAW_PTR, to_raw_ptr_ty()),
        (OFFSET_RAW_PTR, offset_raw_ptr_ty()),
        (ATOMIC_SET, atomic_set_ty()),
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

    Ty::new(TyKind::FnTy(
        vec![r_prv, m_mem, t_ty],
        vec![Ty::new(TyKind::Data(DataTy::new(DataTyKind::Ref(
            Provenance::Ident(r),
            Ownership::Uniq,
            Memory::Ident(m),
            Box::new(DataTy::new(DataTyKind::Ident(t.clone()))),
        ))))],
        ExecTy::new(ExecTyKind::GpuThread),
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

    Ty::new(TyKind::FnTy(
        vec![t_ty],
        vec![
            Ty::new(TyKind::Data(DataTy::new(DataTyKind::RawPtr(Box::new(
                DataTy::new(DataTyKind::Ident(t.clone())),
            ))))),
            Ty::new(TyKind::Data(DataTy::new(DataTyKind::Scalar(ScalarTy::I32)))),
        ],
        ExecTy::new(ExecTyKind::GpuThread),
        Box::new(Ty::new(TyKind::Data(DataTy::new(DataTyKind::RawPtr(
            Box::new(DataTy::new(DataTyKind::Ident(t))),
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
    Ty::new(TyKind::FnTy(
        vec![p_prv, m_mem, t_ty],
        vec![
            Ty::new(TyKind::Data(DataTy::new(DataTyKind::Ref(
                Provenance::Ident(p),
                Ownership::Uniq,
                Memory::Ident(m),
                Box::new(DataTy::new(DataTyKind::Ident(t.clone()))),
            )))),
            Ty::new(TyKind::Data(DataTy::new(DataTyKind::Ident(t)))),
        ],
        ExecTy::new(ExecTyKind::GpuThread),
        Box::new(Ty::new(TyKind::Data(DataTy::new(DataTyKind::Scalar(
            ScalarTy::Unit,
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
    Ty::new(TyKind::FnTy(
        vec![d_dty],
        vec![
            Ty::new(TyKind::Data(DataTy::new(DataTyKind::Ident(d.clone())))),
            Ty::new(TyKind::Data(DataTy::new(DataTyKind::Scalar(ScalarTy::I32)))),
        ],
        ExecTy::new(ExecTyKind::GpuThread),
        Box::new(Ty::new(TyKind::Data(DataTy::new(DataTyKind::Ident(d))))),
    ))
}

// gpu:
//   <>(i32) -[cpu.thread]-> Gpu
fn gpu_device_ty() -> Ty {
    Ty::new(TyKind::FnTy(
        vec![],
        vec![Ty::new(TyKind::Data(DataTy::new(DataTyKind::Scalar(
            ScalarTy::I32,
        ))))],
        ExecTy::new(ExecTyKind::CpuThread),
        Box::new(Ty::new(TyKind::Data(DataTy::new(DataTyKind::Scalar(
            ScalarTy::Gpu,
        ))))),
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
    Ty::new(TyKind::FnTy(
        vec![r_prv, m_mem],
        vec![Ty::new(TyKind::Data(DataTy::new(DataTyKind::Ref(
            Provenance::Ident(r),
            Ownership::Shrd,
            Memory::Ident(m),
            Box::new(DataTy::new(DataTyKind::Atomic(ScalarTy::I32))),
        ))))],
        ExecTy::new(ExecTyKind::GpuThread),
        Box::new(Ty::new(TyKind::Data(DataTy::new(DataTyKind::Scalar(
            ScalarTy::I32,
        ))))),
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
    Ty::new(TyKind::FnTy(
        vec![r_prv, m_mem],
        vec![Ty::new(TyKind::Data(DataTy::new(DataTyKind::Ref(
            Provenance::Ident(r),
            Ownership::Shrd,
            Memory::Ident(m),
            Box::new(DataTy::new(DataTyKind::Atomic(ScalarTy::I32))),
        ))))],
        ExecTy::new(ExecTyKind::CpuThread),
        Box::new(Ty::new(TyKind::Data(DataTy::new(DataTyKind::Scalar(
            ScalarTy::I32,
        ))))),
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
    Ty::new(TyKind::FnTy(
        vec![r_prv, m_mem],
        vec![
            Ty::new(TyKind::Data(DataTy::new(DataTyKind::Ref(
                Provenance::Ident(r),
                Ownership::Shrd,
                Memory::Ident(m),
                Box::new(DataTy::new(DataTyKind::Atomic(ScalarTy::I32))),
            )))),
            Ty::new(TyKind::Data(DataTy::new(DataTyKind::Scalar(ScalarTy::I32)))),
        ],
        ExecTy::new(ExecTyKind::GpuThread),
        Box::new(Ty::new(TyKind::Data(DataTy::new(DataTyKind::Scalar(
            ScalarTy::Unit,
        ))))),
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
    Ty::new(TyKind::FnTy(
        vec![r_prv, m_mem],
        vec![
            Ty::new(TyKind::Data(DataTy::new(DataTyKind::Ref(
                Provenance::Ident(r),
                Ownership::Shrd,
                Memory::Ident(m),
                Box::new(DataTy::new(DataTyKind::Atomic(ScalarTy::I32))),
            )))),
            Ty::new(TyKind::Data(DataTy::new(DataTyKind::Scalar(ScalarTy::I32)))),
        ],
        ExecTy::new(ExecTyKind::CpuThread),
        Box::new(Ty::new(TyKind::Data(DataTy::new(DataTyKind::Scalar(
            ScalarTy::Unit,
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
    Ty::new(TyKind::FnTy(
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
        ExecTy::new(ExecTyKind::CpuThread),
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
    Ty::new(TyKind::FnTy(
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
        ExecTy::new(ExecTyKind::CpuThread),
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
    Ty::new(TyKind::FnTy(
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
        ExecTy::new(ExecTyKind::CpuThread),
        Box::new(Ty::new(TyKind::Data(DataTy::new(DataTyKind::Scalar(
            ScalarTy::Unit,
        ))))),
    ))
}

fn exec_xy_ty() -> Ty {
    let b_x = Ident::new("b_x");
    let b_y = Ident::new("b_y");
    let t_x = Ident::new("t_x");
    let t_y = Ident::new("t_y");
    let b_x_nat = IdentKinded {
        ident: b_x.clone(),
        kind: Kind::Nat,
    };
    let b_y_nat = IdentKinded {
        ident: b_y.clone(),
        kind: Kind::Nat,
    };
    let t_x_nat = IdentKinded {
        ident: t_x.clone(),
        kind: Kind::Nat,
    };
    let t_y_nat = IdentKinded {
        ident: t_y.clone(),
        kind: Kind::Nat,
    };
    exec_ty(
        vec![b_x_nat, b_y_nat, t_x_nat, t_y_nat],
        (
            Dim::XY(Nat::Ident(b_x), Nat::Ident(b_y)),
            Dim::XY(Nat::Ident(t_x), Nat::Ident(t_y)),
        ),
    )
}

fn exec_x_ty() -> Ty {
    let blocks = Ident::new("blocks");
    let threads = Ident::new("threads");
    let blocks_nat = IdentKinded {
        ident: blocks.clone(),
        kind: Kind::Nat,
    };
    let threads_nat = IdentKinded {
        ident: threads.clone(),
        kind: Kind::Nat,
    };
    exec_ty(
        vec![blocks_nat, threads_nat],
        (Dim::X(Nat::Ident(blocks)), Dim::X(Nat::Ident(threads))),
    )
}

// exec: <blocks: nat, threads: nat, r: prv, d: dty>(
//        &r uniq cpu.mem Gpu,
//        input: d,
//        (BlockGrp<blocks, 1, 1, ThreadGrp<Thread, threads, 1, 1>>, d) -[gpu.grid]-> ())
// -> ()
fn exec_ty(mut kinded_idents: Vec<IdentKinded>, (b_dim, t_dim): (Dim, Dim)) -> Ty {
    let r = Ident::new("r");
    let d = Ident::new("d");

    let r_prv = IdentKinded {
        ident: r.clone(),
        kind: Kind::Provenance,
    };
    let d_dty = IdentKinded {
        ident: d.clone(),
        kind: Kind::DataTy,
    };
    let mut common_kinded_idents = vec![r_prv, d_dty];
    kinded_idents.append(&mut common_kinded_idents);
    Ty::new(TyKind::FnTy(
        kinded_idents,
        vec![
            Ty::new(TyKind::Data(DataTy::new(DataTyKind::Ref(
                Provenance::Ident(r),
                Ownership::Uniq,
                Memory::CpuMem,
                Box::new(DataTy::new(DataTyKind::Scalar(ScalarTy::Gpu))),
            )))),
            Ty::new(TyKind::Data(DataTy::new(DataTyKind::Ident(d.clone())))),
            Ty::new(TyKind::FnTy(
                vec![],
                vec![Ty::new(TyKind::Data(DataTy::new(DataTyKind::Ident(
                    d.clone(),
                ))))],
                ExecTy::new(ExecTyKind::GpuGrid(b_dim, t_dim)),
                Box::new(Ty::new(TyKind::Data(DataTy::new(DataTyKind::Scalar(
                    ScalarTy::Unit,
                ))))),
            )),
        ],
        ExecTy::new(ExecTyKind::CpuThread),
        Box::new(Ty::new(TyKind::Data(DataTy::new(DataTyKind::Scalar(
            ScalarTy::Unit,
        ))))),
    ))
}

// shared_alloc:
//  <t: ty>() -> t @ gpu.shared
// fn shared_alloc_ty() -> Ty {
//     let t = Ident::new("t");
//     let t_ty = IdentKinded {
//         ident: t.clone(),
//         kind: Kind::Ty,
//     };
//     Ty::new(TyKind::Fn(
//         vec![t_ty],
//         vec![],
//         ExecTy::new(ExecTyKind::GpuGrid(Dim::X(n.clone()))),
//         Box::new(Ty::new(TyKind::Data(DataTy::new(DataTyKind::At(
//             Box::new(DataTy::new(DataTyKind::Ident(t))),
//             Memory::GpuShared,
//         ))))),
//     ))
// }

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
    Ty::new(TyKind::FnTy(
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
        ExecTy::new(ExecTyKind::View),
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
    Ty::new(TyKind::FnTy(
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
        ExecTy::new(ExecTyKind::View),
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
    Ty::new(TyKind::FnTy(
        vec![t_ty],
        vec![Ty::new(TyKind::Data(DataTy::new(DataTyKind::Ident(
            t.clone(),
        ))))],
        ExecTy::new(ExecTyKind::GpuThread),
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
    Ty::new(TyKind::FnTy(
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
        ExecTy::new(ExecTyKind::View),
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
    Ty::new(TyKind::FnTy(
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
        ExecTy::new(ExecTyKind::View),
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
