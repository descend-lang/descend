use crate::ast::{
    AtomicTy, BaseExec, BinOpNat, DataTy, DataTyKind, DimCompo, ExecExpr, ExecExprKind, ExecTy,
    ExecTyKind, FnTy, Ident, IdentExec, IdentKinded, Kind, Memory, Nat, NatConstr, Ownership,
    ParamSig, Provenance, RefDty, ScalarTy, Ty, TyKind,
};

pub static GPU_DEVICE: &str = "gpu_device";
pub static GPU_ALLOC: &str = "gpu_alloc_copy";
pub static COPY_TO_HOST: &str = "copy_to_host";
pub static COPY_TO_GPU: &str = "copy_to_gpu";

pub static CREATE_ARRAY: &str = "create_array";
pub static TO_RAW_PTR: &str = "to_raw_ptr";
pub static OFFSET_RAW_PTR: &str = "offset_raw_ptr";

pub static SHFL_SYNC: &str = "shfl_sync";
pub static SHFL_UP: &str = "shfl_up";
pub static BALLOT_SYNC: &str = "ballot_sync";

pub static NAT_AS_U64: &str = "nat_as_u64";
pub static THREAD_ID_X: &str = "thread_id_x";

pub static GET_WARP_ID: &str = "get_warp_id";
pub static GET_LANE_ID: &str = "get_lane_id";

pub static ATOMIC_STORE: &str = "atomic_store";
pub static ATOMIC_LOAD: &str = "atomic_load";
pub static ATOMIC_FETCH_OR: &str = "atomic_fetch_or";
pub static ATOMIC_FETCH_ADD: &str = "atomic_fetch_add";
pub static ATOMIC_MIN: &str = "atomic_min";
pub static TO_ATOMIC_ARRAY: &str = "to_atomic_array";
pub static TO_ATOMIC: &str = "to_atomic";

pub static TO_VIEW: &str = "to_view";
pub static REVERSE: &str = "rev";
pub static GROUP: &str = "grp";
pub static JOIN: &str = "join";
pub static TRANSPOSE: &str = "transp";
pub static TAKE_LEFT: &str = "take_left";
pub static TAKE_RIGHT: &str = "take_right";
pub static SELECT_RANGE: &str = "select_range";
pub static MAP: &str = "map";

pub fn fun_decls() -> Vec<(&'static str, FnTy)> {
    let decls = [
        // Built-in functions
        (GPU_DEVICE, gpu_device_ty()),
        (GPU_ALLOC, gpu_alloc_copy_ty()),
        (COPY_TO_HOST, copy_to_host_ty()),
        (COPY_TO_GPU, copy_to_gpu_ty()),
        (CREATE_ARRAY, create_array_ty()),
        (TO_RAW_PTR, to_raw_ptr_ty()),
        (OFFSET_RAW_PTR, offset_raw_ptr_ty()),
        (SHFL_SYNC, shfl_sync_ty()),
        (SHFL_UP, shfl_up_ty()),
        (BALLOT_SYNC, ballot_sync_ty()),
        (THREAD_ID_X, thread_id_x_ty()),
        (GET_WARP_ID, get_warp_id_ty()),
        (GET_LANE_ID, get_lane_id_ty()),
        (NAT_AS_U64, nat_as_u64_ty()),
        // Built-in atomic functions
        (ATOMIC_STORE, atomic_store_ty()),
        (ATOMIC_LOAD, atomic_load_ty()),
        (ATOMIC_FETCH_OR, atomic_fetch_or_ty()),
        (ATOMIC_FETCH_ADD, atomic_fetch_add_ty()),
        (ATOMIC_MIN, atomic_min_ty()),
        (TO_ATOMIC_ARRAY, to_atomic_array_ty()),
        (TO_ATOMIC, to_atomic_ty()),
        // View constructors
        (TO_VIEW, to_view_ty()),
        (REVERSE, reverse_ty()),
        (MAP, map_ty()),
        (GROUP, group_ty()),
        (JOIN, join_ty()),
        (TRANSPOSE, transpose_ty()),
        // (TAKE_LEFT, take_ty(TakeSide::Left)),
        // (TAKE_RIGHT, take_ty(TakeSide::Right)),
        (SELECT_RANGE, select_range_ty()),
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
    let ident_exec = IdentExec::new(Ident::new("ex"), ExecTy::new(ExecTyKind::Any));
    let exec_expr = ExecExpr::new(ExecExprKind::new(BaseExec::Ident(ident_exec.ident.clone())));
    FnTy::new(
        vec![n_nat, d_dty],
        Some(ident_exec),
        vec![ParamSig::new(
            exec_expr.clone(),
            Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Ident(
                d.clone(),
            ))))),
        )],
        exec_expr,
        Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Array(
            Box::new(DataTy::new(DataTyKind::Ident(d))),
            Nat::Ident(n),
        ))))),
        vec![],
    )
}

// to_raw_ptr:
//  <r: prv, m: mem, t: ty> (
//      &r gpu.thread uniq m t
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
    let ident_exec = IdentExec::new(Ident::new("ex"), ExecTy::new(ExecTyKind::GpuThread));
    let exec_expr = ExecExpr::new(ExecExprKind::new(BaseExec::Ident(ident_exec.ident.clone())));
    FnTy::new(
        vec![r_prv, m_mem, d_dty],
        Some(ident_exec),
        vec![ParamSig::new(
            exec_expr.clone(),
            Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Ref(
                Box::new(RefDty::new(
                    Provenance::Ident(r),
                    Ownership::Uniq,
                    Memory::Ident(m),
                    DataTy::new(DataTyKind::Ident(d.clone())),
                )),
            ))))),
        )],
        exec_expr,
        Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::RawPtr(
            Box::new(DataTy::new(DataTyKind::Ident(d))),
        ))))),
        vec![],
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
    let ident_exec = IdentExec::new(Ident::new("ex"), ExecTy::new(ExecTyKind::GpuThread));
    let exec_expr = ExecExpr::new(ExecExprKind::new(BaseExec::Ident(ident_exec.ident.clone())));
    FnTy::new(
        vec![d_dty],
        Some(ident_exec),
        vec![
            ParamSig::new(
                exec_expr.clone(),
                Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::RawPtr(
                    Box::new(DataTy::new(DataTyKind::Ident(d.clone()))),
                ))))),
            ),
            ParamSig::new(
                exec_expr.clone(),
                Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
                    ScalarTy::I32,
                ))))),
            ),
        ],
        exec_expr,
        Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::RawPtr(
            Box::new(DataTy::new(DataTyKind::Ident(d))),
        ))))),
        vec![],
    )
}

// ballot_sync:
//  <>(bool) -[w: gpu.warp]-> u32
fn ballot_sync_ty() -> FnTy {
    let ident_exec = IdentExec::new(Ident::new("w"), ExecTy::new(ExecTyKind::GpuWarp));
    let exec_expr = ExecExpr::new(ExecExprKind::new(BaseExec::Ident(ident_exec.ident.clone())));
    let param_exec = ExecExpr::new(exec_expr.exec.clone().forall(DimCompo::X));

    FnTy::new(
        vec![],
        Some(ident_exec),
        vec![ParamSig::new(
            param_exec,
            Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
                ScalarTy::Bool,
            ))))),
        )],
        exec_expr,
        Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
            ScalarTy::U32,
        ))))),
        vec![],
    )
}

// FIXME warp should have the type given in the comment below
// shfl_sync:
//  <w: gpu.warp>(u32, u32) -[w.forall]-> u32
fn shfl_sync_ty() -> FnTy {
    let ident_exec = IdentExec::new(Ident::new("w"), ExecTy::new(ExecTyKind::GpuWarp));
    let exec_expr_lane = ExecExpr::new(
        ExecExprKind::new(BaseExec::Ident(ident_exec.ident.clone())).forall(DimCompo::X),
    );
    let exec_expr = ExecExpr::new(ExecExprKind::new(BaseExec::Ident(ident_exec.ident.clone())));

    FnTy::new(
        vec![],
        Some(ident_exec),
        vec![
            ParamSig::new(
                exec_expr_lane.clone(),
                Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
                    ScalarTy::U32,
                ))))),
            ),
            ParamSig::new(
                exec_expr_lane.clone(),
                Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
                    ScalarTy::U32,
                ))))),
            ),
        ],
        exec_expr,
        Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
            ScalarTy::U32,
        ))))),
        vec![],
    )
}

// shfl_up:
//  <>(u32, i32) -[gpu.warp]-> u32
fn shfl_up_ty() -> FnTy {
    let ident_exec = IdentExec::new(Ident::new("ex"), ExecTy::new(ExecTyKind::GpuWarp));
    let exec_expr = ExecExpr::new(ExecExprKind::new(BaseExec::Ident(ident_exec.ident.clone())));

    FnTy::new(
        vec![],
        Some(ident_exec),
        vec![
            ParamSig::new(
                exec_expr.clone(),
                Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
                    ScalarTy::U32,
                ))))),
            ),
            ParamSig::new(
                exec_expr.clone(),
                Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
                    ScalarTy::I32,
                ))))),
            ),
        ],
        exec_expr,
        Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
            ScalarTy::U32,
        ))))),
        vec![],
    )
}

// nat_as_u64:
//  <n: nat>() -[view]-> u64
fn nat_as_u64_ty() -> FnTy {
    let n = Ident::new("n");
    let n_nat = IdentKinded {
        ident: n,
        kind: Kind::Nat,
    };
    let ident_exec = IdentExec::new(Ident::new("ex"), ExecTy::new(ExecTyKind::Any));
    let exec_expr = ExecExpr::new(ExecExprKind::new(BaseExec::Ident(ident_exec.ident.clone())));

    FnTy::new(
        vec![n_nat],
        Some(ident_exec),
        vec![],
        exec_expr,
        Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
            ScalarTy::U64,
        ))))),
        vec![],
    )
}

// get_warp_id: <>() -[w: gpu.Warp]-> u32
fn get_warp_id_ty() -> FnTy {
    let ident_exec = IdentExec::new(Ident::new("w"), ExecTy::new(ExecTyKind::GpuWarp));
    let exec_expr = ExecExpr::new(ExecExprKind::new(BaseExec::Ident(ident_exec.ident.clone())));

    FnTy::new(
        vec![],
        Some(ident_exec),
        vec![],
        exec_expr,
        Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
            ScalarTy::U32,
        ))))),
        vec![],
    )
}

// get_lane_id: <>() -[w: gpu.Thread]-> u32
fn get_lane_id_ty() -> FnTy {
    let ident_exec = IdentExec::new(Ident::new("t"), ExecTy::new(ExecTyKind::GpuThread));
    let exec_expr = ExecExpr::new(ExecExprKind::new(BaseExec::Ident(ident_exec.ident.clone())));

    FnTy::new(
        vec![],
        Some(ident_exec),
        vec![],
        exec_expr,
        Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
            ScalarTy::U32,
        ))))),
        vec![],
    )
}

// thread_id_x:
//  <>() -[gpu.thread]-> u32
fn thread_id_x_ty() -> FnTy {
    let ident_exec = IdentExec::new(Ident::new("ex"), ExecTy::new(ExecTyKind::GpuThread));
    let exec_expr = ExecExpr::new(ExecExprKind::new(BaseExec::Ident(ident_exec.ident.clone())));

    FnTy::new(
        vec![],
        Some(ident_exec),
        vec![],
        exec_expr,
        Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
            ScalarTy::U32,
        ))))),
        vec![],
    )
}

// gpu:
//   <>(i32) -[cpu.thread]-> Gpu
fn gpu_device_ty() -> FnTy {
    let ident_exec = IdentExec::new(Ident::new("ex"), ExecTy::new(ExecTyKind::CpuThread));
    let exec_expr = ExecExpr::new(ExecExprKind::new(BaseExec::Ident(ident_exec.ident.clone())));

    FnTy::new(
        vec![],
        Some(ident_exec),
        vec![ParamSig::new(
            exec_expr.clone(),
            Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
                ScalarTy::I32,
            ))))),
        )],
        exec_expr,
        Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
            ScalarTy::Gpu,
        ))))),
        vec![],
    )
}

// to_atomic_array:
//  <r: prv, m: mem, n: nat>(ex: &r uniq m [u32; n]) -[x: Any]-> &r uniq m [AtomicU32; n]
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
    let ident_exec = IdentExec::new(Ident::new("ex"), ExecTy::new(ExecTyKind::Any));
    let exec_expr = ExecExpr::new(ExecExprKind::new(BaseExec::Ident(ident_exec.ident.clone())));

    FnTy::new(
        vec![r_prv, m_mem, n_nat],
        Some(ident_exec),
        vec![ParamSig::new(
            exec_expr.clone(),
            Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Ref(
                Box::new(RefDty::new(
                    Provenance::Ident(r.clone()),
                    Ownership::Uniq,
                    Memory::Ident(m.clone()),
                    DataTy::new(DataTyKind::Array(
                        Box::new(DataTy::new(DataTyKind::Scalar(ScalarTy::U32))),
                        Nat::Ident(n.clone()),
                    )),
                )),
            ))))),
        )],
        exec_expr,
        Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Ref(
            Box::new(RefDty::new(
                Provenance::Ident(r),
                Ownership::Uniq,
                Memory::Ident(m),
                DataTy::new(DataTyKind::Array(
                    Box::new(DataTy::new(DataTyKind::Atomic(AtomicTy::AtomicU32))),
                    Nat::Ident(n),
                )),
            )),
        ))))),
        vec![],
    )
}

// to_atomic:
//  <r: prv, m: mem>(&r uniq x m u32) -[x: Any]-> &r uniq x m AtomicU32
fn to_atomic_ty() -> FnTy {
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
    let ident_exec = IdentExec::new(Ident::new("ex"), ExecTy::new(ExecTyKind::Any));
    let exec_expr = ExecExpr::new(ExecExprKind::new(BaseExec::Ident(ident_exec.ident.clone())));

    FnTy::new(
        vec![r_prv, m_mem],
        Some(ident_exec),
        vec![ParamSig::new(
            exec_expr.clone(),
            Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Ref(
                Box::new(RefDty::new(
                    Provenance::Ident(r.clone()),
                    Ownership::Uniq,
                    Memory::Ident(m.clone()),
                    DataTy::new(DataTyKind::Scalar(ScalarTy::U32)),
                )),
            ))))),
        )],
        exec_expr,
        Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Ref(
            Box::new(RefDty::new(
                Provenance::Ident(r),
                Ownership::Uniq,
                Memory::Ident(m),
                DataTy::new(DataTyKind::Atomic(AtomicTy::AtomicU32)),
            )),
        ))))),
        vec![],
    )
}

// atomic_store:
//  <r: prv, m: mem>(&r shrd  m AtomicU32, u32) -[gpu.thread]-> ()
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
    let ident_exec = IdentExec::new(Ident::new("ex"), ExecTy::new(ExecTyKind::GpuThread));
    let exec_expr = ExecExpr::new(ExecExprKind::new(BaseExec::Ident(ident_exec.ident.clone())));

    FnTy::new(
        vec![r_prv, m_mem],
        Some(ident_exec),
        vec![
            ParamSig::new(
                exec_expr.clone(),
                Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Ref(
                    Box::new(RefDty::new(
                        Provenance::Ident(r),
                        Ownership::Shrd,
                        Memory::Ident(m),
                        DataTy::new(DataTyKind::Atomic(AtomicTy::AtomicU32)),
                    )),
                ))))),
            ),
            ParamSig::new(
                exec_expr.clone(),
                Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
                    ScalarTy::U32,
                ))))),
            ),
        ],
        exec_expr,
        Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
            ScalarTy::Unit,
        ))))),
        vec![],
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
    let ident_exec = IdentExec::new(Ident::new("ex"), ExecTy::new(ExecTyKind::GpuThread));
    let exec_expr = ExecExpr::new(ExecExprKind::new(BaseExec::Ident(ident_exec.ident.clone())));

    FnTy::new(
        vec![r_prv, m_mem],
        Some(ident_exec),
        vec![
            ParamSig::new(
                exec_expr.clone(),
                Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Ref(
                    Box::new(RefDty::new(
                        Provenance::Ident(r),
                        Ownership::Shrd,
                        Memory::Ident(m),
                        DataTy::new(DataTyKind::Atomic(AtomicTy::AtomicU32)),
                    )),
                ))))),
            ),
            ParamSig::new(
                exec_expr.clone(),
                Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
                    ScalarTy::U32,
                ))))),
            ),
        ],
        exec_expr,
        Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
            ScalarTy::U32,
        ))))),
        vec![],
    )
}

// atomic_min:
//  <r: prv, m: mem>(&r shrd m AtomicI32, i32) -[gpu.thread]-> i32
fn atomic_min_ty() -> FnTy {
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
    let ident_exec = IdentExec::new(Ident::new("t"), ExecTy::new(ExecTyKind::GpuThread));
    let exec_expr = ExecExpr::new(ExecExprKind::new(BaseExec::Ident(ident_exec.ident.clone())));

    FnTy::new(
        vec![r_prv, m_mem],
        Some(ident_exec),
        vec![
            ParamSig::new(
                exec_expr.clone(),
                Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Ref(
                    Box::new(RefDty::new(
                        Provenance::Ident(r),
                        Ownership::Shrd,
                        Memory::Ident(m),
                        DataTy::new(DataTyKind::Atomic(AtomicTy::AtomicI32)),
                    )),
                ))))),
            ),
            ParamSig::new(
                exec_expr.clone(),
                Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
                    ScalarTy::I32,
                ))))),
            ),
        ],
        exec_expr.clone(),
        Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
            ScalarTy::I32,
        ))))),
        vec![],
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
    let ident_exec = IdentExec::new(Ident::new("ex"), ExecTy::new(ExecTyKind::GpuThread));
    let exec_expr = ExecExpr::new(ExecExprKind::new(BaseExec::Ident(ident_exec.ident.clone())));

    FnTy::new(
        vec![r_prv, m_mem],
        Some(ident_exec),
        vec![
            ParamSig::new(
                exec_expr.clone(),
                Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Ref(
                    Box::new(RefDty::new(
                        Provenance::Ident(r),
                        Ownership::Shrd,
                        Memory::Ident(m),
                        DataTy::new(DataTyKind::Atomic(AtomicTy::AtomicU32)),
                    )),
                ))))),
            ),
            ParamSig::new(
                exec_expr.clone(),
                Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
                    ScalarTy::U32,
                ))))),
            ),
        ],
        exec_expr.clone(),
        Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
            ScalarTy::U32,
        ))))),
        vec![],
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
    let ident_exec = IdentExec::new(Ident::new("ex"), ExecTy::new(ExecTyKind::GpuThread));
    let exec_expr = ExecExpr::new(ExecExprKind::new(BaseExec::Ident(ident_exec.ident.clone())));

    FnTy::new(
        vec![r_prv, m_mem],
        Some(ident_exec),
        vec![ParamSig::new(
            exec_expr.clone(),
            Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Ref(
                Box::new(RefDty::new(
                    Provenance::Ident(r),
                    Ownership::Shrd,
                    Memory::Ident(m),
                    DataTy::new(DataTyKind::Atomic(AtomicTy::AtomicU32)),
                )),
            ))))),
        )],
        exec_expr,
        Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
            ScalarTy::U32,
        ))))),
        vec![],
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
    let exec_expr = ExecExpr::new(ExecExprKind::new(BaseExec::CpuThread));

    FnTy::new(
        vec![r1_prv, r2_prv, d_dty],
        None,
        vec![
            ParamSig::new(
                exec_expr.clone(),
                Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Ref(
                    Box::new(RefDty::new(
                        Provenance::Ident(r1),
                        Ownership::Uniq,
                        Memory::CpuMem,
                        DataTy::new(DataTyKind::Scalar(ScalarTy::Gpu)),
                    )),
                ))))),
            ),
            ParamSig::new(
                exec_expr.clone(),
                Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Ref(
                    Box::new(RefDty::new(
                        Provenance::Ident(r2),
                        Ownership::Shrd,
                        Memory::CpuMem,
                        DataTy::new(DataTyKind::Ident(d.clone())),
                    )),
                ))))),
            ),
        ],
        exec_expr.clone(),
        Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::At(
            Box::new(DataTy::new(DataTyKind::Ident(d))),
            Memory::GpuGlobal,
        ))))),
        vec![],
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
    let exec_expr = ExecExpr::new(ExecExprKind::new(BaseExec::CpuThread));

    FnTy::new(
        vec![r1_prv, r2_prv, d_dty],
        None,
        vec![
            ParamSig::new(
                exec_expr.clone(),
                Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Ref(
                    Box::new(RefDty::new(
                        Provenance::Ident(r1),
                        Ownership::Shrd,
                        Memory::GpuGlobal,
                        DataTy::new(DataTyKind::Ident(d.clone())),
                    )),
                ))))),
            ),
            ParamSig::new(
                exec_expr.clone(),
                Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Ref(
                    Box::new(RefDty::new(
                        Provenance::Ident(r2),
                        Ownership::Uniq,
                        Memory::CpuMem,
                        DataTy::new(DataTyKind::Ident(d)),
                    )),
                ))))),
            ),
        ],
        exec_expr,
        Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
            ScalarTy::Unit,
        ))))),
        vec![],
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
    let exec_expr = ExecExpr::new(ExecExprKind::new(BaseExec::CpuThread));

    FnTy::new(
        vec![r1_prv, r2_prv, d_dty],
        None,
        vec![
            ParamSig::new(
                exec_expr.clone(),
                Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Ref(
                    Box::new(RefDty::new(
                        Provenance::Ident(r1),
                        Ownership::Uniq,
                        Memory::GpuGlobal,
                        DataTy::new(DataTyKind::Ident(d.clone())),
                    )),
                ))))),
            ),
            ParamSig::new(
                exec_expr.clone(),
                Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Ref(
                    Box::new(RefDty::new(
                        Provenance::Ident(r2),
                        Ownership::Shrd,
                        Memory::CpuMem,
                        DataTy::new(DataTyKind::Ident(d)),
                    )),
                ))))),
            ),
        ],
        exec_expr,
        Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
            ScalarTy::Unit,
        ))))),
        vec![],
    )
}

// to_view:
//  <r: prv, m: mem, n: nat, d: dty>([d; n]) -[view]-> [[d; n]]
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
    let ident_exec = IdentExec::new(Ident::new("ex"), ExecTy::new(ExecTyKind::Any));
    let exec_expr = ExecExpr::new(ExecExprKind::new(BaseExec::Ident(ident_exec.ident.clone())));

    FnTy::new(
        vec![n_nat, d_dty],
        Some(ident_exec),
        vec![ParamSig::new(
            exec_expr.clone(),
            Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Array(
                Box::new(DataTy::new(DataTyKind::Ident(d.clone()))),
                Nat::Ident(n.clone()),
            ))))),
        )],
        exec_expr,
        Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::ArrayShape(
            Box::new(DataTy::new(DataTyKind::Ident(d))),
            Nat::Ident(n),
        ))))),
        vec![],
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
    let ident_exec = IdentExec::new(Ident::new("ex"), ExecTy::new(ExecTyKind::Any));
    let exec_expr = ExecExpr::new(ExecExprKind::new(BaseExec::Ident(ident_exec.ident.clone())));

    FnTy::new(
        vec![n_nat, d_ty],
        Some(ident_exec),
        vec![ParamSig::new(
            exec_expr.clone(),
            Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::ArrayShape(
                Box::new(DataTy::new(DataTyKind::Ident(d.clone()))),
                Nat::Ident(n.clone()),
            ))))),
        )],
        exec_expr,
        Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::ArrayShape(
            Box::new(DataTy::new(DataTyKind::Ident(d))),
            Nat::Ident(n),
        ))))),
        vec![],
    )
}

//map_mut:<d: dty, d2: dty, n: nat>(|d| -[ex]-> d2, [[d;n]]) -[ex: Any]-> [[d2; n]]
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
    let ident_exec = IdentExec::new(Ident::new("ex"), ExecTy::new(ExecTyKind::Any));
    let exec_expr = ExecExpr::new(ExecExprKind::new(BaseExec::Ident(ident_exec.ident.clone())));

    FnTy::new(
        vec![d_dty, d2_dty, n_nat],
        Some(ident_exec),
        vec![
            ParamSig::new(
                exec_expr.clone(),
                Ty::new(TyKind::FnTy(Box::new(FnTy::new(
                    vec![],
                    None,
                    vec![ParamSig::new(
                        exec_expr.clone(),
                        Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Ident(
                            d.clone(),
                        ))))),
                    )],
                    exec_expr.clone(),
                    Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Ident(
                        d2.clone(),
                    ))))),
                    vec![],
                )))),
            ),
            ParamSig::new(
                exec_expr.clone(),
                Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::ArrayShape(
                    Box::new(DataTy::new(DataTyKind::Ident(d))),
                    Nat::Ident(n.clone()),
                ))))),
            ),
        ],
        exec_expr,
        Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::ArrayShape(
            Box::new(DataTy::new(DataTyKind::Ident(d2))),
            Nat::Ident(n),
        ))))),
        vec![],
    )
}

// group/group_mut:
//  <size: nat, n: nat, d: dty>([[d; n]]) -> [[ [[d; size]]; n/size ]]
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
    let ident_exec = IdentExec::new(Ident::new("ex"), ExecTy::new(ExecTyKind::Any));
    let exec_expr = ExecExpr::new(ExecExprKind::new(BaseExec::Ident(ident_exec.ident.clone())));

    FnTy::new(
        vec![s_nat, n_nat, d_ty],
        Some(ident_exec),
        vec![ParamSig::new(
            exec_expr.clone(),
            Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::ArrayShape(
                Box::new(DataTy::new(DataTyKind::Ident(d.clone()))),
                Nat::Ident(n.clone()),
            ))))),
        )],
        exec_expr,
        Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::ArrayShape(
            Box::new(DataTy::new(DataTyKind::ArrayShape(
                Box::new(DataTy::new(DataTyKind::Ident(d))),
                Nat::Ident(s.clone()),
            ))),
            Nat::BinOp(
                BinOpNat::Div,
                Box::new(Nat::Ident(n.clone())),
                Box::new(Nat::Ident(s.clone())),
            ),
        ))))),
        vec![NatConstr::Eq(
            Box::new(Nat::BinOp(
                BinOpNat::Mod,
                Box::new(Nat::Ident(n)),
                Box::new(Nat::Ident(s)),
            )),
            Box::new(Nat::Lit(0)),
        )],
    )
}

pub enum TakeSide {
    Left,
    Right,
}

// take_left:
//  <split_pos: nat, n: nat, d: dty>([[d; n]]) -> [[d; split_pos]]
// take_right:
//  <split_pos: nat, n: nat, d: dty>([[d; n]]) -> [[d; n - split_pos]])
// fn take_ty(take_side: TakeSide) -> FnTy {
//     let s = Ident::new("s");
//     let n = Ident::new("n");
//     let d = Ident::new("d");
//     let s_nat = IdentKinded {
//         ident: s.clone(),
//         kind: Kind::Nat,
//     };
//     let n_nat = IdentKinded {
//         ident: n.clone(),
//         kind: Kind::Nat,
//     };
//     let d_ty = IdentKinded {
//         ident: d.clone(),
//         kind: Kind::DataTy,
//     };
//     let ident_exec = IdentExec::new(Ident::new("ex"), ExecTy::new(ExecTyKind::Any));
//     let exec_expr = ExecExpr::new(ExecExprKind::new(BaseExec::Ident(ident_exec.ident.clone())));
//
//     let output_dty = match take_side {
//         TakeSide::Left => DataTy::new(DataTyKind::ArrayShape(
//             Box::new(DataTy::new(DataTyKind::Ident(d.clone()))),
//             Nat::Ident(s.clone()),
//         )),
//         TakeSide::Right => DataTy::new(DataTyKind::ArrayShape(
//             Box::new(DataTy::new(DataTyKind::Ident(d.clone()))),
//             Nat::BinOp(
//                 BinOpNat::Sub,
//                 Box::new(Nat::Ident(n.clone())),
//                 Box::new(Nat::Ident(s)),
//             ),
//         )),
//     };
//     FnTy::new(
//         vec![s_nat, n_nat, d_ty],
//         Some(ident_exec),
//         vec![ParamSig::new(
//             exec_expr.clone(),
//             Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::ArrayShape(
//                 Box::new(DataTy::new(DataTyKind::Ident(d))),
//                 Nat::Ident(n),
//             ))))),
//         )],
//         exec_expr,
//         Ty::new(TyKind::Data(Box::new(output_dty))),
//     )
// }

// select: <l: nat, u: nat, n: nat, d: dty>([[ d; n ]]) -[a: any]-> [[ d; u-l ]]
fn select_range_ty() -> FnTy {
    let l = Ident::new("l");
    let u = Ident::new("u");
    let n = Ident::new("n");
    let d = Ident::new("d");
    let l_nat = IdentKinded {
        ident: l.clone(),
        kind: Kind::Nat,
    };
    let u_nat = IdentKinded {
        ident: u.clone(),
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
    let ident_exec = IdentExec::new(Ident::new("ex"), ExecTy::new(ExecTyKind::Any));
    let exec_expr = ExecExpr::new(ExecExprKind::new(BaseExec::Ident(ident_exec.ident.clone())));

    FnTy::new(
        vec![l_nat, u_nat, n_nat, d_ty],
        Some(ident_exec),
        vec![ParamSig::new(
            exec_expr.clone(),
            Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::ArrayShape(
                Box::new(DataTy::new(DataTyKind::Ident(d.clone()))),
                Nat::Ident(n.clone()),
            ))))),
        )],
        exec_expr,
        Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::ArrayShape(
            Box::new(DataTy::new(DataTyKind::Ident(d))),
            Nat::BinOp(
                BinOpNat::Sub,
                Box::new(Nat::Ident(u.clone())),
                Box::new(Nat::Ident(l.clone())),
            ),
        ))))),
        vec![NatConstr::And(
            Box::new(NatConstr::Lt(
                Box::new(Nat::Ident(l)),
                Box::new(Nat::Ident(u.clone())),
            )),
            Box::new(NatConstr::Or(
                Box::new(NatConstr::Lt(
                    Box::new(Nat::Ident(u.clone())),
                    Box::new(Nat::Ident(n.clone())),
                )),
                Box::new(NatConstr::Eq(
                    Box::new(Nat::Ident(u)),
                    Box::new(Nat::Ident(n)),
                )),
            )),
        )],
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
    let ident_exec = IdentExec::new(Ident::new("ex"), ExecTy::new(ExecTyKind::Any));
    let exec_expr = ExecExpr::new(ExecExprKind::new(BaseExec::Ident(ident_exec.ident.clone())));

    FnTy::new(
        vec![o_nat, n_nat, d_dty],
        Some(ident_exec),
        vec![ParamSig::new(
            exec_expr.clone(),
            Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::ArrayShape(
                Box::new(DataTy::new(DataTyKind::ArrayShape(
                    Box::new(DataTy::new(DataTyKind::Ident(d.clone()))),
                    Nat::Ident(n.clone()),
                ))),
                Nat::Ident(o.clone()),
            ))))),
        )],
        exec_expr,
        Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::ArrayShape(
            Box::new(DataTy::new(DataTyKind::Ident(d))),
            Nat::BinOp(
                BinOpNat::Mul,
                Box::new(Nat::Ident(n)),
                Box::new(Nat::Ident(o)),
            ),
        ))))),
        vec![],
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
    let ident_exec = IdentExec::new(Ident::new("ex"), ExecTy::new(ExecTyKind::Any));
    let exec_expr = ExecExpr::new(ExecExprKind::new(BaseExec::Ident(ident_exec.ident.clone())));

    FnTy::new(
        vec![n_nat, o_nat, d_ty],
        Some(ident_exec),
        vec![ParamSig::new(
            exec_expr.clone(),
            Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::ArrayShape(
                Box::new(DataTy::new(DataTyKind::ArrayShape(
                    Box::new(DataTy::new(DataTyKind::Ident(d.clone()))),
                    Nat::Ident(n.clone()),
                ))),
                Nat::Ident(o.clone()),
            ))))),
        )],
        exec_expr,
        Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::ArrayShape(
            Box::new(DataTy::new(DataTyKind::ArrayShape(
                Box::new(DataTy::new(DataTyKind::Ident(d))),
                Nat::Ident(o),
            ))),
            Nat::Ident(n),
        ))))),
        vec![],
    )
}
