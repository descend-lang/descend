use crate::ast::AtomicTy::AtomicU32;
use crate::ast::{
    AtomicTy, BinOpNat, DataTy, DataTyKind, Dim, Dim1d, Dim2d, ExecTy, ExecTyKind, FnTy, Ident,
    IdentKinded, Kind, Memory, Nat, Ownership, Provenance, RefDty, ScalarTy, Ty, TyKind,
};

pub static GPU_DEVICE: &str = "gpu_device";
pub static GPU_ALLOC: &str = "gpu_alloc_copy";
pub static COPY_TO_HOST: &str = "copy_to_host";
pub static EXEC: &str = "exec";
pub static EXEC_XY: &str = "exec_xy";
pub static SHARED_ALLOC: &str = "shared_alloc";
pub static COPY_TO_GPU: &str = "copy_to_gpu";
pub static TO_RAW_PTR: &str = "to_raw_ptr";
pub static OFFSET_RAW_PTR: &str = "offset_raw_ptr";
pub static SHFL_UP: &str = "shfl_up";
pub static NAT_AS_U64: &str = "nat_as_u64";
pub static THREAD_ID_X: &str = "thread_id_x";

pub static ATOMIC_STORE: &str = "atomic_store";
pub static ATOMIC_LOAD: &str = "atomic_load";
pub static ATOMIC_FETCH_OR: &str = "atomic_fetch_or";
pub static ATOMIC_FETCH_ADD: &str = "atomic_fetch_add";
pub static TO_ATOMIC_ARRAY: &str = "to_atomic_array";
pub static TO_ATOMIC: &str = "to_atomic";

pub static CREATE_ARRAY: &str = "create_array";

pub static TO_VIEW: &str = "to_view";
pub static TO_VIEW_MUT: &str = "to_view_mut";
pub static REVERSE: &str = "rev";
pub static REVERSE_MUT: &str = "rev_mut";
pub static GROUP: &str = "group";
pub static GROUP_MUT: &str = "group_mut";
pub static JOIN: &str = "join";
pub static JOIN_MUT: &str = "join_mut";
pub static TRANSPOSE: &str = "transpose";
pub static TRANSPOSE_MUT: &str = "transpose_mut";
pub static MAP: &str = "map";
pub static MAP_MUT: &str = "map_mut";

pub fn fun_decls() -> Vec<(&'static str, FnTy)> {
    let decls = [
        // Built-in functions
        (GPU_DEVICE, gpu_device_ty()),
        (GPU_ALLOC, gpu_alloc_copy_ty()),
        (COPY_TO_HOST, copy_to_host_ty()),
        (EXEC, exec_x_ty()),
        (EXEC_XY, exec_xy_ty()),
        (SHARED_ALLOC, shared_alloc_ty()),
        (COPY_TO_GPU, copy_to_gpu_ty()),
        (TO_RAW_PTR, to_raw_ptr_ty()),
        (OFFSET_RAW_PTR, offset_raw_ptr_ty()),
        (SHFL_UP, shfl_up_ty()),
        (THREAD_ID_X, thread_id_x_ty()),
        (NAT_AS_U64, nat_as_u64_ty()),
        // Built-in atomic functions
        (ATOMIC_STORE, atomic_store_ty()),
        (ATOMIC_LOAD, atomic_load_ty()),
        (ATOMIC_FETCH_OR, atomic_fetch_or_ty()),
        (ATOMIC_FETCH_ADD, atomic_fetch_add_ty()),
        (TO_ATOMIC_ARRAY, to_atomic_array_ty()),
        (TO_ATOMIC, to_atomic_ty()),
        // View constructors
        (TO_VIEW, to_view_ty(Ownership::Shrd)),
        (TO_VIEW_MUT, to_view_ty(Ownership::Uniq)),
        (REVERSE, reverse_ty(Ownership::Shrd)),
        (REVERSE_MUT, reverse_ty(Ownership::Uniq)),
        (MAP, map_ty(Ownership::Shrd)),
        (MAP_MUT, map_ty(Ownership::Uniq)),
        (GROUP, group_ty(Ownership::Shrd)),
        (GROUP_MUT, group_ty(Ownership::Uniq)),
        (JOIN, join_ty(Ownership::Shrd)),
        (JOIN_MUT, join_ty(Ownership::Uniq)),
        (TRANSPOSE, transpose_ty(Ownership::Shrd)),
        (TRANSPOSE_MUT, transpose_ty(Ownership::Uniq)),
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

// shfl_up:
//  <>(u32, i32) -[gpu.warp]-> u32
fn shfl_up_ty() -> FnTy {
    FnTy::new(
        vec![],
        vec![
            Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
                ScalarTy::U32,
            ))))),
            Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
                ScalarTy::I32,
            ))))),
        ],
        ExecTy::new(ExecTyKind::GpuWarp),
        Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
            ScalarTy::U32,
        ))))),
    )
}

// nat_as_u64:
//  <n: nat>() -[view]-> u64
fn nat_as_u64_ty() -> FnTy {
    let n = Ident::new("n");
    let n_nat = IdentKinded {
        ident: n.clone(),
        kind: Kind::Nat,
    };
    FnTy::new(
        vec![n_nat],
        vec![],
        ExecTy::new(ExecTyKind::View),
        Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
            ScalarTy::U64,
        ))))),
    )
}

// thread_id_x:
//  <>() -[gpu.thread]-> u32
fn thread_id_x_ty() -> FnTy {
    FnTy::new(
        vec![],
        vec![],
        ExecTy::new(ExecTyKind::GpuThread),
        Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
            ScalarTy::U32,
        ))))),
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

// to_atomic_array:
//  <r: prv, m: mem, n: nat>(&r uniq m [u32; n]) -[view]-> &r uniq m [AtomicU32; n]
fn to_atomic_array_ty() -> FnTy {
    let r = Ident::new("r");
    let m = Ident::new("m");
    let n = Ident::new("n");
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
    FnTy::new(
        vec![r_prv, m_mem, n_nat],
        vec![Ty::new(TyKind::Data(Box::new(DataTy::new(
            DataTyKind::Ref(Box::new(RefDty::new(
                Provenance::Ident(r.clone()),
                Ownership::Uniq,
                Memory::Ident(m.clone()),
                DataTy::new(DataTyKind::Array(
                    Box::new(DataTy::new(DataTyKind::Scalar(ScalarTy::U32))),
                    Nat::Ident(n.clone()),
                )),
            ))),
        ))))],
        ExecTy::new(ExecTyKind::View),
        Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Ref(
            Box::new(RefDty::new(
                Provenance::Ident(r),
                Ownership::Uniq,
                Memory::Ident(m),
                DataTy::new(DataTyKind::Array(
                    Box::new(DataTy::new(DataTyKind::Atomic(AtomicTy::AtomicU32))),
                    Nat::Ident(n.clone()),
                )),
            )),
        ))))),
    )
}

// to_atomic:
//  <r: prv, m: mem>(&r uniq m u32) -[view]-> &r uniq m AtomicU32
fn to_atomic_ty() -> FnTy {
    let r = Ident::new("r");
    let m = Ident::new("m");
    let n = Ident::new("n");
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
                Provenance::Ident(r.clone()),
                Ownership::Uniq,
                Memory::Ident(m.clone()),
                DataTy::new(DataTyKind::Scalar(ScalarTy::U32)),
            ))),
        ))))],
        ExecTy::new(ExecTyKind::View),
        Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Ref(
            Box::new(RefDty::new(
                Provenance::Ident(r),
                Ownership::Uniq,
                Memory::Ident(m),
                DataTy::new(DataTyKind::Atomic(AtomicTy::AtomicU32)),
            )),
        ))))),
    )
}

// atomic_store:
//  <r: prv, m: mem>(&r shrd m AtomicU32, u32) -[gpu.thread]-> ()
fn atomic_store_ty() -> FnTy {
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
                    DataTy::new(DataTyKind::Atomic(AtomicTy::AtomicU32)),
                )),
            ))))),
            Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
                ScalarTy::U32,
            ))))),
        ],
        ExecTy::new(ExecTyKind::GpuThread),
        Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
            ScalarTy::Unit,
        ))))),
    )
}

// atomic_fetch_or:
//  <r: prv, m: mem>(&r shrd m AtomicU32, u32) -[gpu.thread]-> u32
fn atomic_fetch_or_ty() -> FnTy {
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
                    DataTy::new(DataTyKind::Atomic(AtomicTy::AtomicU32)),
                )),
            ))))),
            Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
                ScalarTy::U32,
            ))))),
        ],
        ExecTy::new(ExecTyKind::GpuThread),
        Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
            ScalarTy::U32,
        ))))),
    )
}

// atomic_fetch_add:
//  <r: prv, m: mem>(&r shrd m AtomicU32, u32) -[gpu.thread]-> u32
fn atomic_fetch_add_ty() -> FnTy {
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
                    DataTy::new(DataTyKind::Atomic(AtomicTy::AtomicU32)),
                )),
            ))))),
            Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
                ScalarTy::U32,
            ))))),
        ],
        ExecTy::new(ExecTyKind::GpuThread),
        Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
            ScalarTy::U32,
        ))))),
    )
}

// atomic_load:
//  <r: prv, m: mem>(&r shrd m AtomicU32) -[gpu.thread]-> u32
fn atomic_load_ty() -> FnTy {
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
                DataTy::new(DataTyKind::Atomic(AtomicTy::AtomicU32)),
            ))),
        ))))],
        ExecTy::new(ExecTyKind::GpuThread),
        Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
            ScalarTy::U32,
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
//  <t: dty>() -[view]-> t @ gpu.shared
fn shared_alloc_ty() -> FnTy {
    let t = Ident::new("t");
    let t_ty = IdentKinded {
        ident: t.clone(),
        kind: Kind::DataTy,
    };
    FnTy::new(
        vec![t_ty],
        vec![],
        ExecTy::new(ExecTyKind::View),
        Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::At(
            Box::new(DataTy::new(DataTyKind::Ident(t))),
            Memory::GpuShared,
        ))))),
    )
}

// TODO FIX Error: t: ty is too general this means it could contain functions
//  (which is not well-kinded).
// to_view:
//  <r: prv, m: mem, n: nat, d: dty>(&r shrd m [d; n]) -[view]-> &r shrd m [[d; n]]
// to_view_mut:
//  <r: prv, m: mem, n: nat, d: dty>(&r uniq m [d; n]) -[view]-> &r uniq m [[d; n]]
fn to_view_ty(own: Ownership) -> FnTy {
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
    FnTy::new(
        vec![r_prv, m_mem, n_nat, d_dty],
        vec![Ty::new(TyKind::Data(Box::new(DataTy::new(
            DataTyKind::Ref(Box::new(RefDty::new(
                Provenance::Ident(r.clone()),
                own,
                Memory::Ident(m.clone()),
                DataTy::new(DataTyKind::Array(
                    Box::new(DataTy::new(DataTyKind::Ident(d.clone()))),
                    Nat::Ident(n.clone()),
                )),
            ))),
        ))))],
        ExecTy::new(ExecTyKind::View),
        Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Ref(
            Box::new(RefDty::new(
                Provenance::Ident(r),
                own,
                Memory::Ident(m),
                DataTy::new(DataTyKind::ArrayShape(
                    Box::new(DataTy::new(DataTyKind::Ident(d))),
                    Nat::Ident(n),
                )),
            )),
        ))))),
    )
}

// rev/rev_mut:
// <n: nat, r: prv, m: mem, d: dty>(&r W m [[d; n]]) -> &r W m [[d; n]]
fn reverse_ty(own: Ownership) -> FnTy {
    let n = Ident::new("n");
    let r = Ident::new("r");
    let m = Ident::new("m");
    let d = Ident::new("d");
    let n_nat = IdentKinded {
        ident: n.clone(),
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
    let d_ty = IdentKinded {
        ident: d.clone(),
        kind: Kind::DataTy,
    };
    FnTy::new(
        vec![n_nat, r_prv, m_mem, d_ty],
        vec![Ty::new(TyKind::Data(Box::new(DataTy::new(
            DataTyKind::Ref(Box::new(RefDty::new(
                Provenance::Ident(r.clone()),
                own,
                Memory::Ident(m.clone()),
                DataTy::new(DataTyKind::ArrayShape(
                    Box::new(DataTy::new(DataTyKind::Ident(d.clone()))),
                    Nat::Ident(n.clone()),
                )),
            ))),
        ))))],
        ExecTy::new(ExecTyKind::View),
        Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Ref(
            Box::new(RefDty::new(
                Provenance::Ident(r.clone()),
                own,
                Memory::Ident(m.clone()),
                DataTy::new(DataTyKind::ArrayShape(
                    Box::new(DataTy::new(DataTyKind::Ident(d.clone()))),
                    Nat::Ident(n.clone()),
                )),
            )),
        ))))),
    )
}

//map_mut:<r1: prv, d: dty, d2: dty, m: mem, n: nat>(lambda: |&r1 uniq d| -[view]-> d2, &r1 uniq m [[d;n]]) -[view]-> &r1 uniq m [[d2; n]]
fn map_ty(own: Ownership) -> FnTy {
    let r = Ident::new("r");
    let d = Ident::new("d");
    let d2 = Ident::new("d2");
    let m = Ident::new("m");
    let n = Ident::new("n");

    let r_prv = IdentKinded {
        ident: r.clone(),
        kind: Kind::Provenance,
    };
    let d_dty = IdentKinded {
        ident: d.clone(),
        kind: Kind::DataTy,
    };
    let d2_dty = IdentKinded {
        ident: d2.clone(),
        kind: Kind::DataTy,
    };
    let m_mem = IdentKinded {
        ident: m.clone(),
        kind: Kind::Memory,
    };
    let n_nat = IdentKinded {
        ident: n.clone(),
        kind: Kind::Nat,
    };

    FnTy::new(
        vec![
            r_prv.clone(),
            d_dty.clone(),
            d2_dty.clone(),
            m_mem.clone(),
            n_nat.clone(),
        ],
        //Parameter
        vec![
            //Lambda function
            Ty::new(TyKind::FnTy(Box::new(FnTy::new(
                vec![],
                vec![Ty::new(TyKind::Data(Box::new(DataTy::new(
                    DataTyKind::Ref(Box::new(RefDty::new(
                        Provenance::Ident(r.clone()),
                        own,
                        Memory::Ident(m.clone()),
                        DataTy::new(DataTyKind::Ident(d.clone())),
                    ))),
                ))))],
                ExecTy::new(ExecTyKind::View),
                Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Ref(
                    Box::new(RefDty::new(
                        Provenance::Ident(r.clone()),
                        own,
                        Memory::Ident(m.clone()),
                        DataTy::new(DataTyKind::Ident(d2.clone())),
                    )),
                ))))),
            )))),
            //Arrayshape
            Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Ref(
                Box::new(RefDty::new(
                    Provenance::Ident(r.clone()),
                    own,
                    Memory::Ident(m.clone()),
                    DataTy::new(DataTyKind::ArrayShape(
                        Box::new(DataTy::new(DataTyKind::Ident(d))),
                        Nat::Ident(n.clone()),
                    )),
                )),
            ))))),
        ],
        //Execution Resource
        ExecTy::new(ExecTyKind::View),
        //Return value -> arrayshape
        Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Ref(
            Box::new(RefDty::new(
                Provenance::Ident(r),
                own,
                Memory::Ident(m),
                DataTy::new(DataTyKind::ArrayShape(
                    Box::new(DataTy::new(DataTyKind::Ident(d2))),
                    Nat::Ident(n),
                )),
            )),
        ))))),
    )
}

// group/group_mut:
//  <size: nat, r: prv, m: mem, n: nat, d: dty>(&r W m [[d; n]]) -> &r W m [[ [[d; size]]; n/size ]]
fn group_ty(own: Ownership) -> FnTy {
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
    FnTy::new(
        vec![s_nat, r_prv, m_mem, n_nat, d_ty],
        vec![Ty::new(TyKind::Data(Box::new(DataTy::new(
            DataTyKind::Ref(Box::new(RefDty::new(
                Provenance::Ident(r.clone()),
                own,
                Memory::Ident(m.clone()),
                DataTy::new(DataTyKind::ArrayShape(
                    Box::new(DataTy::new(DataTyKind::Ident(d.clone()))),
                    Nat::Ident(n.clone()),
                )),
            ))),
        ))))],
        ExecTy::new(ExecTyKind::View),
        Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Ref(
            Box::new(RefDty::new(
                Provenance::Ident(r),
                own,
                Memory::Ident(m),
                DataTy::new(DataTyKind::ArrayShape(
                    Box::new(DataTy::new(DataTyKind::ArrayShape(
                        Box::new(DataTy::new(DataTyKind::Ident(d))),
                        Nat::Ident(s.clone()),
                    ))),
                    Nat::BinOp(
                        BinOpNat::Div,
                        Box::new(Nat::Ident(n)),
                        Box::new(Nat::Ident(s)),
                    ),
                )),
            )),
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
fn join_ty(own: Ownership) -> FnTy {
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
    FnTy::new(
        vec![r_prv, m_mem, o_nat, n_nat, d_dty],
        vec![Ty::new(TyKind::Data(Box::new(DataTy::new(
            DataTyKind::Ref(Box::new(RefDty::new(
                Provenance::Ident(r.clone()),
                own,
                Memory::Ident(m.clone()),
                DataTy::new(DataTyKind::ArrayShape(
                    Box::new(DataTy::new(DataTyKind::ArrayShape(
                        Box::new(DataTy::new(DataTyKind::Ident(d.clone()))),
                        Nat::Ident(n.clone()),
                    ))),
                    Nat::Ident(o.clone()),
                )),
            ))),
        ))))],
        ExecTy::new(ExecTyKind::View),
        Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Ref(
            Box::new(RefDty::new(
                Provenance::Ident(r),
                own,
                Memory::Ident(m),
                DataTy::new(DataTyKind::ArrayShape(
                    Box::new(DataTy::new(DataTyKind::Ident(d))),
                    Nat::BinOp(
                        BinOpNat::Mul,
                        Box::new(Nat::Ident(n)),
                        Box::new(Nat::Ident(o)),
                    ),
                )),
            )),
        ))))),
    )
}

// transpose:
//  <r: prv, m: mem, n: nat, o: nat, d: dty>(&r W m [[ [[d; n]]; o]]) -> &r W m [[ [[d; o]]; n]]
fn transpose_ty(own: Ownership) -> FnTy {
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
    FnTy::new(
        vec![r_prv, m_mem, n_nat, o_nat, d_ty],
        vec![Ty::new(TyKind::Data(Box::new(DataTy::new(
            DataTyKind::Ref(Box::new(RefDty::new(
                Provenance::Ident(r.clone()),
                own,
                Memory::Ident(m.clone()),
                DataTy::new(DataTyKind::ArrayShape(
                    Box::new(DataTy::new(DataTyKind::ArrayShape(
                        Box::new(DataTy::new(DataTyKind::Ident(d.clone()))),
                        Nat::Ident(n.clone()),
                    ))),
                    Nat::Ident(o.clone()),
                )),
            ))),
        ))))],
        ExecTy::new(ExecTyKind::View),
        Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Ref(
            Box::new(RefDty::new(
                Provenance::Ident(r),
                own,
                Memory::Ident(m),
                DataTy::new(DataTyKind::ArrayShape(
                    Box::new(DataTy::new(DataTyKind::ArrayShape(
                        Box::new(DataTy::new(DataTyKind::Ident(d))),
                        Nat::Ident(o),
                    ))),
                    Nat::Ident(n),
                )),
            )),
        ))))),
    )
}
