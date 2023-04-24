use crate::ast::{
    BinOpNat, DataTy, DataTyKind, Dim, Dim1d, Dim2d, ExecTy, ExecTyKind, FnTy, Ident, IdentKinded,
    Kind, Memory, Nat, Ownership, Provenance, RefDty, ScalarTy, Ty, TyKind,
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

pub static CREATE_ARRAY: &str = "create_array";

pub static TO_VIEW: &str = "to_view";
pub static REVERSE: &str = "rev";
pub static GROUP: &str = "grp";
pub static JOIN: &str = "join";
pub static TRANSPOSE: &str = "transp";
pub static SPLIT_AT: &str = "split_at";
pub static MAP: &str = "map";

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
        (CREATE_ARRAY, create_array_ty()),
        // View constructors
        (TO_VIEW, to_view_ty()),
        (REVERSE, reverse_ty()),
        (MAP, map_ty()),
        (GROUP, group_ty()),
        (JOIN, join_ty()),
        (TRANSPOSE, transpose_ty()),
        (SPLIT_AT, split_at_ty()),
    ];

    decls.to_vec()
}

fn create_array_ty() -> FnTy {
    let n = Ident::new("n");
    let d = Ident::new("d");
    let n_nat = IdentKinded {
        ident: n.clone(),
        kind: Kind::Nat,
    };
    let d_dty = IdentKinded {
        ident: d.clone(),
        kind: Kind::DataTy,
    };
    FnTy::new(
        vec![n_nat, d_dty],
        vec![Ty::new(TyKind::Data(Box::new(DataTy::new(
            DataTyKind::Ident(d.clone()),
        ))))],
        ExecTy::new(ExecTyKind::CpuThread),
        Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Array(
            Box::new(DataTy::new(DataTyKind::Ident(d))),
            Nat::Ident(n),
        ))))),
    )
}

// to_raw_ptr:
//  <r: prv, m: mem, t: ty> (
//      &r uniq m t
// ) -[gpu.thread]-> RawPtr<t>
fn to_raw_ptr_ty() -> FnTy {
    let r = Ident::new("r");
    let m = Ident::new("m");
    let d = Ident::new("d");

    let r_prv = IdentKinded {
        ident: r.clone(),
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

    FnTy::new(
        vec![r_prv, m_mem, d_dty],
        vec![Ty::new(TyKind::Data(Box::new(DataTy::new(
            DataTyKind::Ref(Box::new(RefDty::new(
                Provenance::Ident(r),
                Ownership::Uniq,
                Memory::Ident(m),
                DataTy::new(DataTyKind::Ident(d.clone())),
            ))),
        ))))],
        ExecTy::new(ExecTyKind::GpuThread),
        Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::RawPtr(
            Box::new(DataTy::new(DataTyKind::Ident(d))),
        ))))),
    )
}

// offset_raw_ptr:
//  <m: mem, t: ty> (
//      RawPtr<t>, i32
// ) -[gpu.thread]-> RawPtr<t>
fn offset_raw_ptr_ty() -> FnTy {
    let d = Ident::new("d");
    let d_dty = IdentKinded {
        ident: d.clone(),
        kind: Kind::DataTy,
    };

    FnTy::new(
        vec![d_dty],
        vec![
            Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::RawPtr(
                Box::new(DataTy::new(DataTyKind::Ident(d.clone()))),
            ))))),
            Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
                ScalarTy::I32,
            ))))),
        ],
        ExecTy::new(ExecTyKind::GpuThread),
        Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::RawPtr(
            Box::new(DataTy::new(DataTyKind::Ident(d))),
        ))))),
    )
}

fn atomic_set_ty() -> FnTy {
    let p = Ident::new("p");
    let m = Ident::new("m");
    let d = Ident::new("d");

    let p_prv = IdentKinded {
        ident: p.clone(),
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
    FnTy::new(
        vec![p_prv, m_mem, d_dty],
        vec![
            Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Ref(
                Box::new(RefDty::new(
                    Provenance::Ident(p),
                    Ownership::Uniq,
                    Memory::Ident(m),
                    DataTy::new(DataTyKind::Ident(d.clone())),
                )),
            ))))),
            Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Ident(d))))),
        ],
        ExecTy::new(ExecTyKind::GpuThread),
        Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
            ScalarTy::Unit,
        ))))),
    )
}

// shuffle_xor:
//  <d: dty>(d, i32) -> d
fn shuffle_xor_ty() -> FnTy {
    let d = Ident::new("d");
    let d_dty = IdentKinded {
        ident: d.clone(),
        kind: Kind::DataTy,
    };
    FnTy::new(
        vec![d_dty],
        vec![
            Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Ident(
                d.clone(),
            ))))),
            Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
                ScalarTy::I32,
            ))))),
        ],
        ExecTy::new(ExecTyKind::GpuThread),
        Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Ident(d))))),
    )
}

// gpu:
//   <>(i32) -[cpu.thread]-> Gpu
fn gpu_device_ty() -> FnTy {
    FnTy::new(
        vec![],
        vec![Ty::new(TyKind::Data(Box::new(DataTy::new(
            DataTyKind::Scalar(ScalarTy::I32),
        ))))],
        ExecTy::new(ExecTyKind::CpuThread),
        Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
            ScalarTy::Gpu,
        ))))),
    )
}

//  <r: prv, m: mem>(&r shrd m Atomic<i32>) -[gpu.global]-> i32
fn load_atomic_ty() -> FnTy {
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
    FnTy::new(
        vec![r_prv, m_mem],
        vec![Ty::new(TyKind::Data(Box::new(DataTy::new(
            DataTyKind::Ref(Box::new(RefDty::new(
                Provenance::Ident(r),
                Ownership::Shrd,
                Memory::Ident(m),
                DataTy::new(DataTyKind::Atomic(ScalarTy::I32)),
            ))),
        ))))],
        ExecTy::new(ExecTyKind::GpuThread),
        Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
            ScalarTy::I32,
        ))))),
    )
}

fn load_atomic_host_ty() -> FnTy {
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
    FnTy::new(
        vec![r_prv, m_mem],
        vec![Ty::new(TyKind::Data(Box::new(DataTy::new(
            DataTyKind::Ref(Box::new(RefDty::new(
                Provenance::Ident(r),
                Ownership::Shrd,
                Memory::Ident(m),
                DataTy::new(DataTyKind::Atomic(ScalarTy::I32)),
            ))),
        ))))],
        ExecTy::new(ExecTyKind::CpuThread),
        Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
            ScalarTy::I32,
        ))))),
    )
}

// <r: prv, m: mem>(&r shrd m t, i32) -[gpu.global]-> ()
fn store_atomic_ty() -> FnTy {
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
    FnTy::new(
        vec![r_prv, m_mem],
        vec![
            Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Ref(
                Box::new(RefDty::new(
                    Provenance::Ident(r),
                    Ownership::Shrd,
                    Memory::Ident(m),
                    DataTy::new(DataTyKind::Atomic(ScalarTy::I32)),
                )),
            ))))),
            Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
                ScalarTy::I32,
            ))))),
        ],
        ExecTy::new(ExecTyKind::GpuThread),
        Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
            ScalarTy::Unit,
        ))))),
    )
}

// <r: prv, m: mem>(&r shrd m t, i32) -[gpu.global]-> ()
fn store_atomic_host_ty() -> FnTy {
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
    FnTy::new(
        vec![r_prv, m_mem],
        vec![
            Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Ref(
                Box::new(RefDty::new(
                    Provenance::Ident(r),
                    Ownership::Shrd,
                    Memory::Ident(m),
                    DataTy::new(DataTyKind::Atomic(ScalarTy::I32)),
                )),
            ))))),
            Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
                ScalarTy::I32,
            ))))),
        ],
        ExecTy::new(ExecTyKind::CpuThread),
        Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
            ScalarTy::Unit,
        ))))),
    )
}

// gpu_alloc:
//   <r1: prv, r2: prv, d: dty>(
//      &r1 uniq cpu.mem Gpu, &r2 shrd cpu.mem t
//   ) -[cpu.thread]-> t @ gpu.global
fn gpu_alloc_copy_ty() -> FnTy {
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
    FnTy::new(
        vec![r1_prv, r2_prv, d_dty],
        vec![
            Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Ref(
                Box::new(RefDty::new(
                    Provenance::Ident(r1),
                    Ownership::Uniq,
                    Memory::CpuMem,
                    DataTy::new(DataTyKind::Scalar(ScalarTy::Gpu)),
                )),
            ))))),
            Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Ref(
                Box::new(RefDty::new(
                    Provenance::Ident(r2),
                    Ownership::Shrd,
                    Memory::CpuMem,
                    DataTy::new(DataTyKind::Ident(d.clone())),
                )),
            ))))),
        ],
        ExecTy::new(ExecTyKind::CpuThread),
        Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::At(
            Box::new(DataTy::new(DataTyKind::Ident(d))),
            Memory::GpuGlobal,
        ))))),
    )
}

// copy_to_host:
//   <r1: prv, r2: prv, d: dty>(&r1 shrd gpu.global d, &r2 uniq cpu.mem d)
//      -[cpu.thread]-> ()
fn copy_to_host_ty() -> FnTy {
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
    FnTy::new(
        vec![r1_prv, r2_prv, d_dty],
        vec![
            Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Ref(
                Box::new(RefDty::new(
                    Provenance::Ident(r1),
                    Ownership::Shrd,
                    Memory::GpuGlobal,
                    DataTy::new(DataTyKind::Ident(d.clone())),
                )),
            ))))),
            Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Ref(
                Box::new(RefDty::new(
                    Provenance::Ident(r2),
                    Ownership::Uniq,
                    Memory::CpuMem,
                    DataTy::new(DataTyKind::Ident(d)),
                )),
            ))))),
        ],
        ExecTy::new(ExecTyKind::CpuThread),
        Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
            ScalarTy::Unit,
        ))))),
    )
}

// copy_to_gpu:
//  <r1: prv, r2: prv, d: dty>(& r1 uniq gpu.global d,
//      & r2 shrd cpu.mem d) -[cpu.thread]-> ()
fn copy_to_gpu_ty() -> FnTy {
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
    FnTy::new(
        vec![r1_prv, r2_prv, d_dty],
        vec![
            Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Ref(
                Box::new(RefDty::new(
                    Provenance::Ident(r1),
                    Ownership::Uniq,
                    Memory::GpuGlobal,
                    DataTy::new(DataTyKind::Ident(d.clone())),
                )),
            ))))),
            Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Ref(
                Box::new(RefDty::new(
                    Provenance::Ident(r2),
                    Ownership::Shrd,
                    Memory::CpuMem,
                    DataTy::new(DataTyKind::Ident(d)),
                )),
            ))))),
        ],
        ExecTy::new(ExecTyKind::CpuThread),
        Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
            ScalarTy::Unit,
        ))))),
    )
}

fn exec_xy_ty() -> FnTy {
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
            Dim::XY(Box::new(Dim2d(Nat::Ident(b_x), Nat::Ident(b_y)))),
            Dim::XY(Box::new(Dim2d(Nat::Ident(t_x), Nat::Ident(t_y)))),
        ),
    )
}

fn exec_x_ty() -> FnTy {
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
        (
            Dim::X(Box::new(Dim1d(Nat::Ident(blocks)))),
            Dim::X(Box::new(Dim1d(Nat::Ident(threads)))),
        ),
    )
}

// exec: <blocks: nat, threads: nat, r: prv, d: dty>(
//        &r uniq cpu.mem Gpu,
//        input: d,
//        (BlockGrp<blocks, 1, 1, ThreadGrp<Thread, threads, 1, 1>>, d) -[gpu.grid]-> ())
// -> ()
fn exec_ty(mut kinded_idents: Vec<IdentKinded>, (b_dim, t_dim): (Dim, Dim)) -> FnTy {
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
    FnTy::new(
        kinded_idents,
        vec![
            Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Ref(
                Box::new(RefDty::new(
                    Provenance::Ident(r),
                    Ownership::Uniq,
                    Memory::CpuMem,
                    DataTy::new(DataTyKind::Scalar(ScalarTy::Gpu)),
                )),
            ))))),
            Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Ident(
                d.clone(),
            ))))),
            Ty::new(TyKind::FnTy(Box::new(FnTy::new(
                vec![],
                vec![Ty::new(TyKind::Data(Box::new(DataTy::new(
                    DataTyKind::Ident(d.clone()),
                ))))],
                ExecTy::new(ExecTyKind::GpuGrid(b_dim, t_dim)),
                Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
                    ScalarTy::Unit,
                ))))),
            )))),
        ],
        ExecTy::new(ExecTyKind::CpuThread),
        Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
            ScalarTy::Unit,
        ))))),
    )
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
fn to_view_ty() -> FnTy {
    let n = Ident::new("n");
    let d = Ident::new("d");
    let n_nat = IdentKinded {
        ident: n.clone(),
        kind: Kind::Nat,
    };
    let d_dty = IdentKinded {
        ident: d.clone(),
        kind: Kind::DataTy,
    };
    FnTy::new(
        vec![n_nat, d_dty],
        vec![Ty::new(TyKind::Data(Box::new(DataTy::new(
            DataTyKind::Array(
                Box::new(DataTy::new(DataTyKind::Ident(d.clone()))),
                Nat::Ident(n.clone()),
            ),
        ))))],
        ExecTy::new(ExecTyKind::View),
        Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::ArrayShape(
            Box::new(DataTy::new(DataTyKind::Ident(d))),
            Nat::Ident(n),
        ))))),
    )
}

// rev/rev_mut:
// <n: nat, r: prv, m: mem, d: dty>(&r W m [[d; n]]) -> &r W m [[d; n]]
fn reverse_ty() -> FnTy {
    let n = Ident::new("n");
    let d = Ident::new("d");
    let n_nat = IdentKinded {
        ident: n.clone(),
        kind: Kind::Nat,
    };
    let d_ty = IdentKinded {
        ident: d.clone(),
        kind: Kind::DataTy,
    };
    FnTy::new(
        vec![n_nat, d_ty],
        vec![Ty::new(TyKind::Data(Box::new(DataTy::new(
            DataTyKind::ArrayShape(
                Box::new(DataTy::new(DataTyKind::Ident(d.clone()))),
                Nat::Ident(n.clone()),
            ),
        ))))],
        ExecTy::new(ExecTyKind::View),
        Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::ArrayShape(
            Box::new(DataTy::new(DataTyKind::Ident(d.clone()))),
            Nat::Ident(n.clone()),
        ))))),
    )
}

//map_mut:<r1: prv, d: dty, d2: dty, m: mem, n: nat>(lambda: |&r1 uniq d| -[view]-> d2, [[d;n]]) -[view]-> &r1 uniq m [[d2; n]]
fn map_ty() -> FnTy {
    let d = Ident::new("d");
    let d2 = Ident::new("d2");
    let n = Ident::new("n");
    let d_dty = IdentKinded {
        ident: d.clone(),
        kind: Kind::DataTy,
    };
    let d2_dty = IdentKinded {
        ident: d2.clone(),
        kind: Kind::DataTy,
    };
    let n_nat = IdentKinded {
        ident: n.clone(),
        kind: Kind::Nat,
    };

    FnTy::new(
        vec![d_dty.clone(), d2_dty.clone(), n_nat.clone()],
        vec![
            Ty::new(TyKind::FnTy(Box::new(FnTy::new(
                vec![],
                vec![Ty::new(TyKind::Data(Box::new(DataTy::new(
                    DataTyKind::Ident(d.clone()),
                ))))],
                ExecTy::new(ExecTyKind::View),
                Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Ident(
                    d2.clone(),
                ))))),
            )))),
            Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::ArrayShape(
                Box::new(DataTy::new(DataTyKind::Ident(d))),
                Nat::Ident(n.clone()),
            ))))),
        ],
        ExecTy::new(ExecTyKind::View),
        Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::ArrayShape(
            Box::new(DataTy::new(DataTyKind::Ident(d2))),
            Nat::Ident(n),
        ))))),
    )
}

// group/group_mut:
//  <size: nat, r: prv, m: mem, n: nat, d: dty>(&r W m [[d; n]]) -> &r W m [[ [[d; size]]; n/size ]]
fn group_ty() -> FnTy {
    let s = Ident::new("s");
    let n = Ident::new("n");
    let d = Ident::new("d");
    let s_nat = IdentKinded {
        ident: s.clone(),
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
    FnTy::new(
        vec![s_nat, n_nat, d_ty],
        vec![Ty::new(TyKind::Data(Box::new(DataTy::new(
            DataTyKind::ArrayShape(
                Box::new(DataTy::new(DataTyKind::Ident(d.clone()))),
                Nat::Ident(n.clone()),
            ),
        ))))],
        ExecTy::new(ExecTyKind::View),
        Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::ArrayShape(
            Box::new(DataTy::new(DataTyKind::ArrayShape(
                Box::new(DataTy::new(DataTyKind::Ident(d))),
                Nat::Ident(s.clone()),
            ))),
            Nat::BinOp(
                BinOpNat::Div,
                Box::new(Nat::Ident(n)),
                Box::new(Nat::Ident(s)),
            ),
        ))))),
    )
}

// split_at:
//  <split_pos: nat, n: nat, d: dty>([[d; n]]) -> ([[d; split_pos]], [[d; n-split_pos]])
fn split_at_ty() -> FnTy {
    let s = Ident::new("s");
    let n = Ident::new("n");
    let d = Ident::new("d");
    let s_nat = IdentKinded {
        ident: s.clone(),
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
    FnTy::new(
        vec![s_nat, n_nat, d_ty],
        vec![Ty::new(TyKind::Data(Box::new(DataTy::new(
            DataTyKind::ArrayShape(
                Box::new(DataTy::new(DataTyKind::Ident(d.clone()))),
                Nat::Ident(n.clone()),
            ),
        ))))],
        ExecTy::new(ExecTyKind::View),
        Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Tuple(
            vec![
                DataTy::new(DataTyKind::ArrayShape(
                    Box::new(DataTy::new(DataTyKind::Ident(d.clone()))),
                    Nat::Ident(s.clone()),
                )),
                DataTy::new(DataTyKind::ArrayShape(
                    Box::new(DataTy::new(DataTyKind::Ident(d))),
                    Nat::BinOp(
                        BinOpNat::Sub,
                        Box::new(Nat::Ident(n)),
                        Box::new(Nat::Ident(s)),
                    ),
                )),
            ],
        ))))),
    )
}

// +: <t: ty>(t, t) -> t
// fn bin_op() -> FnTy {
//     let t = Ident::new("t");
//     let t_ty = IdentKinded {
//         ident: t.clone(),
//         kind: Kind::Ty,
//     };
//     FnTy::new(
//         vec![t_ty],
//         vec![Ty::new(TyKind::Data(Box::new(DataTy::new(
//             DataTyKind::Ident(t.clone()),
//         ))))],
//         ExecTy::new(ExecTyKind::GpuThread),
//         Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Ident(t))))),
//     )
// }

// join/join_mut:
//  <r: prv, m: mem, o: nat, n: nat, d: dty>(&r W m [[ [[d; n]]; o]]) -> [[d; n*o]]
fn join_ty() -> FnTy {
    let n = Ident::new("n");
    let o = Ident::new("o");
    let d = Ident::new("d");
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
    FnTy::new(
        vec![o_nat, n_nat, d_dty],
        vec![Ty::new(TyKind::Data(Box::new(DataTy::new(
            DataTyKind::ArrayShape(
                Box::new(DataTy::new(DataTyKind::ArrayShape(
                    Box::new(DataTy::new(DataTyKind::Ident(d.clone()))),
                    Nat::Ident(n.clone()),
                ))),
                Nat::Ident(o.clone()),
            ),
        ))))],
        ExecTy::new(ExecTyKind::View),
        Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::ArrayShape(
            Box::new(DataTy::new(DataTyKind::Ident(d))),
            Nat::BinOp(
                BinOpNat::Mul,
                Box::new(Nat::Ident(n)),
                Box::new(Nat::Ident(o)),
            ),
        ))))),
    )
}

// transpose:
//  <r: prv, m: mem, n: nat, o: nat, d: dty>(&r W m [[ [[d; n]]; o]]) -> &r W m [[ [[d; o]]; n]]
fn transpose_ty() -> FnTy {
    let n = Ident::new("n");
    let o = Ident::new("o");
    let d = Ident::new("d");
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
    FnTy::new(
        vec![n_nat, o_nat, d_ty],
        vec![Ty::new(TyKind::Data(Box::new(DataTy::new(
            DataTyKind::ArrayShape(
                Box::new(DataTy::new(DataTyKind::ArrayShape(
                    Box::new(DataTy::new(DataTyKind::Ident(d.clone()))),
                    Nat::Ident(n.clone()),
                ))),
                Nat::Ident(o.clone()),
            ),
        ))))],
        ExecTy::new(ExecTyKind::View),
        Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::ArrayShape(
            Box::new(DataTy::new(DataTyKind::ArrayShape(
                Box::new(DataTy::new(DataTyKind::Ident(d))),
                Nat::Ident(o),
            ))),
            Nat::Ident(n),
        ))))),
    )
}
