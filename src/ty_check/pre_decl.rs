use crate::arena_ast::{
    AtomicTy, BaseExec, BinOpNat, DataTy, DataTyKind, DimCompo, ExecExpr, ExecExprKind, ExecTy,
    ExecTyKind, FnTy, Ident, IdentExec, IdentKinded, Kind, Memory, Nat, NatConstr, Ownership,
    ParamSig, Provenance, RefDty, ScalarTy, Ty, TyKind,
};

use bumpalo::{collections::Vec as BumpVec, Bump};

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

pub fn fun_decls<'a>(arena: &'a Bump) -> BumpVec<'a, (&'static str, FnTy<'a>)> {
    let mut decls = BumpVec::new_in(arena);

    decls.push((GPU_DEVICE, gpu_device_ty(arena)));
    decls.push((GPU_ALLOC, gpu_alloc_copy_ty(arena)));
    decls.push((COPY_TO_HOST, copy_to_host_ty(arena)));
    decls.push((COPY_TO_GPU, copy_to_gpu_ty(arena)));
    decls.push((CREATE_ARRAY, create_array_ty(arena)));
    decls.push((TO_RAW_PTR, to_raw_ptr_ty(arena)));
    decls.push((OFFSET_RAW_PTR, offset_raw_ptr_ty(arena)));
    decls.push((SHFL_SYNC, shfl_sync_ty(arena)));
    decls.push((SHFL_UP, shfl_up_ty(arena)));
    decls.push((BALLOT_SYNC, ballot_sync_ty(arena)));
    decls.push((THREAD_ID_X, thread_id_x_ty(arena)));
    decls.push((GET_WARP_ID, get_warp_id_ty(arena)));
    decls.push((GET_LANE_ID, get_lane_id_ty(arena)));
    decls.push((NAT_AS_U64, nat_as_u64_ty(arena)));
    decls.push((ATOMIC_STORE, atomic_store_ty(arena)));
    decls.push((ATOMIC_LOAD, atomic_load_ty(arena)));
    decls.push((ATOMIC_FETCH_OR, atomic_fetch_or_ty(arena)));
    decls.push((ATOMIC_FETCH_ADD, atomic_fetch_add_ty(arena)));
    decls.push((ATOMIC_MIN, atomic_min_ty(arena)));
    decls.push((TO_ATOMIC_ARRAY, to_atomic_array_ty(arena)));
    decls.push((TO_ATOMIC, to_atomic_ty(arena)));
    decls.push((TO_VIEW, to_view_ty(arena)));
    decls.push((REVERSE, reverse_ty(arena)));
    decls.push((MAP, map_ty(arena)));
    decls.push((GROUP, group_ty(arena)));
    decls.push((JOIN, join_ty(arena)));
    decls.push((TRANSPOSE, transpose_ty(arena)));
    decls.push((SELECT_RANGE, select_range_ty(arena)));

    decls
}

// DataTy helpers
fn d_ident<'a>(id: Ident<'a>, arena: &'a Bump) -> DataTy<'a> {
    DataTy::new(arena, DataTyKind::Ident(id))
}
fn d_scalar<'a>(s: ScalarTy, arena: &'a Bump) -> DataTy<'a> {
    DataTy::new(arena, DataTyKind::Scalar(s))
}
fn d_atomic<'a>(a: AtomicTy, arena: &'a Bump) -> DataTy<'a> {
    DataTy::new(arena, DataTyKind::Atomic(a))
}

fn d_array<'a>(arena: &'a Bump, elem: DataTy<'a>, n: Nat<'a>) -> DataTy<'a> {
    let elem_ref = arena.alloc(elem);
    DataTy::new(arena, DataTyKind::Array(elem_ref, n))
}
fn d_array_shape<'a>(arena: &'a Bump, elem: DataTy<'a>, n: Nat<'a>) -> DataTy<'a> {
    let elem_ref = arena.alloc(elem);
    DataTy::new(arena, DataTyKind::ArrayShape(elem_ref, n))
}
fn d_ref<'a>(
    arena: &'a Bump,
    prv: Provenance<'a>,
    own: Ownership,
    mem: Memory<'a>,
    ty: DataTy<'a>,
) -> DataTy<'a> {
    let reff = arena.alloc(RefDty::new(arena, prv, own, mem, ty));
    DataTy::new(arena, DataTyKind::Ref(reff))
}

// Ty helpers
fn ty_data_ref<'a>(arena: &'a Bump, d: DataTy<'a>) -> &'a Ty<'a> {
    let data_ty = arena.alloc(d);
    arena.alloc(Ty {
        ty: TyKind::Data(data_ty),
        span: None,
    })
}

// Exec helpers
fn exec_ident<'a>(arena: &'a Bump, id: Ident<'a>) -> ExecExpr<'a> {
    let kind = arena.alloc(ExecExprKind::new(arena, BaseExec::Ident(id)));
    ExecExpr {
        exec: kind,
        ty: None,
        span: None,
    }
}

fn create_array_ty<'a>(arena: &'a Bump) -> FnTy<'a> {
    // <n: nat, d: dty>(d) -[Any]-> [d; n]
    let n = Ident::new(arena, "n");
    let d = Ident::new(arena, "d");

    let n_nat = IdentKinded {
        ident: n.clone(),
        kind: Kind::Nat,
    };
    let d_dty = IdentKinded {
        ident: d.clone(),
        kind: Kind::DataTy,
    };

    let ident_exec =
        IdentExec::new_in(arena, Ident::new(arena, "ex"), ExecTy::new(ExecTyKind::Any));
    let exec_expr = exec_ident(arena, ident_exec.ident.clone());

    // param: d
    let param_ty = ty_data_ref(arena, d_ident(d.clone(), arena));

    // return: [d; n]
    let ret_dt = d_array(arena, d_ident(d, arena), Nat::Ident(n));
    let ret_ty = ty_data_ref(arena, ret_dt);

    FnTy::new(
        arena,
        [n_nat, d_dty],
        Some(ident_exec),
        [ParamSig::new(exec_expr.clone(), param_ty)],
        exec_expr,
        ret_ty,
        [],
    )
}

// to_raw_ptr:
//  <r: prv, m: mem, t: ty> (
//      &r gpu.thread uniq m t
// ) -[gpu.thread]-> RawPtr<t>
fn to_raw_ptr_ty<'a>(arena: &'a Bump) -> FnTy<'a> {
    // <r: prv, m: mem, d: dty>(&r uniq m d) -[gpu.thread]-> RawPtr<d>
    let r = Ident::new(arena, "r");
    let m = Ident::new(arena, "m");
    let d = Ident::new(arena, "d");

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

    let ident_exec = IdentExec::new_in(
        arena,
        Ident::new(arena, "ex"),
        ExecTy::new(ExecTyKind::GpuThread),
    );
    let exec_expr = exec_ident(arena, ident_exec.ident.clone());

    // param: &r uniq m d
    let param_dt = d_ref(
        arena,
        Provenance::Ident(r.clone()),
        Ownership::Uniq,
        Memory::Ident(m.clone()),
        d_ident(d.clone(), arena),
    );
    let param_ty = ty_data_ref(arena, param_dt);

    // return: RawPtr<d>
    let ret_inner = d_ident(d, arena);
    let ret_dt = DataTy::new(arena, DataTyKind::RawPtr(arena.alloc(ret_inner)));
    let ret_ty = ty_data_ref(arena, ret_dt);

    FnTy::new(
        arena,
        [r_prv, m_mem, d_dty],
        Some(ident_exec),
        [ParamSig::new(exec_expr.clone(), param_ty)],
        exec_expr,
        ret_ty,
        [],
    )
}

// offset_raw_ptr:
//  <m: mem, t: ty> (
//      RawPtr<t>, i32
// ) -[gpu.thread]-> RawPtr<t>
// <d: dty>(RawPtr<d>, i32) -[gpu.thread]-> RawPtr<d>
fn offset_raw_ptr_ty<'a>(arena: &'a Bump) -> FnTy<'a> {
    let d = Ident::new(arena, "d");
    let d_dty = IdentKinded {
        ident: d.clone(),
        kind: Kind::DataTy,
    };

    let ident_exec = IdentExec::new_in(
        arena,
        Ident::new(arena, "ex"),
        ExecTy::new(ExecTyKind::GpuThread),
    );
    let exec_expr = exec_ident(arena, ident_exec.ident.clone());

    // param 1: RawPtr<d>
    let p1_dt = DataTy::new(
        arena,
        DataTyKind::RawPtr(arena.alloc(d_ident(d.clone(), arena))),
    );
    let p1_ty = ty_data_ref(arena, p1_dt);

    // param 2: i32
    let p2_ty = ty_data_ref(arena, d_scalar(ScalarTy::I32, arena));

    // return: RawPtr<d>
    let ret_dt = DataTy::new(arena, DataTyKind::RawPtr(arena.alloc(d_ident(d, arena))));
    let ret_ty = ty_data_ref(arena, ret_dt);

    FnTy::new(
        arena,
        [d_dty],
        Some(ident_exec),
        [
            ParamSig::new(exec_expr.clone(), p1_ty),
            ParamSig::new(exec_expr.clone(), p2_ty),
        ],
        exec_expr,
        ret_ty,
        [],
    )
}

// ballot_sync:
//  <>(bool) -[w: gpu.warp]-> u32
// <>(bool) -[w: gpu.warp]-> u32
fn ballot_sync_ty<'a>(arena: &'a Bump) -> FnTy<'a> {
    let ident_exec = IdentExec::new_in(
        arena,
        Ident::new(arena, "w"),
        ExecTy::new(ExecTyKind::GpuWarp),
    );

    // body exec: w
    let exec_expr = exec_ident(arena, ident_exec.ident.clone());

    // param exec: w.forall(x)
    let lane_kind =
        ExecExprKind::new(arena, BaseExec::Ident(ident_exec.ident.clone())).forall(DimCompo::X);
    let param_exec = ExecExpr {
        exec: arena.alloc(lane_kind),
        ty: None,
        span: None,
    };

    // param: bool
    let p_ty = ty_data_ref(arena, d_scalar(ScalarTy::Bool, arena));
    // return: u32
    let r_ty = ty_data_ref(arena, d_scalar(ScalarTy::U32, arena));

    FnTy::new(
        arena,
        [],
        Some(ident_exec),
        [ParamSig::new(param_exec, p_ty)],
        exec_expr,
        r_ty,
        [],
    )
}

// FIXME warp should have the type given in the comment below
// shfl_sync:
// <w: gpu.warp>(u32, u32) -[w.forall]-> u32
fn shfl_sync_ty<'a>(arena: &'a Bump) -> FnTy<'a> {
    // generic exec: w : gpu.warp
    let ident_exec = IdentExec::new_in(
        arena,
        Ident::new(arena, "w"),
        ExecTy::new(ExecTyKind::GpuWarp),
    );

    // param exec = w.forall(X)
    let lane_kind =
        ExecExprKind::new(arena, BaseExec::Ident(ident_exec.ident.clone())).forall(DimCompo::X);
    let param_exec = ExecExpr {
        exec: arena.alloc(lane_kind),
        ty: None,
        span: None,
    };

    // body exec = w
    let body_exec = exec_ident(arena, ident_exec.ident.clone());

    // types
    let u32_ty = ty_data_ref(arena, d_scalar(ScalarTy::U32, arena));

    FnTy::new(
        arena,
        [],               // generics (kinded Idents)
        Some(ident_exec), // generic exec
        [
            ParamSig::new(param_exec.clone(), u32_ty),
            ParamSig::new(param_exec, u32_ty),
        ],
        body_exec,
        ty_data_ref(arena, d_scalar(ScalarTy::U32, arena)),
        [], // nat constraints
    )
}

// shfl_up:
// <>(u32, i32) -[gpu.warp]-> u32
fn shfl_up_ty<'a>(arena: &'a Bump) -> FnTy<'a> {
    // generic exec: ex : gpu.warp
    let ident_exec = IdentExec::new_in(
        arena,
        Ident::new(arena, "ex"),
        ExecTy::new(ExecTyKind::GpuWarp),
    );
    let exec_expr = exec_ident(arena, ident_exec.ident.clone());

    // types
    let u32_ty = ty_data_ref(arena, d_scalar(ScalarTy::U32, arena));
    let i32_ty = ty_data_ref(arena, d_scalar(ScalarTy::I32, arena));

    FnTy::new(
        arena,
        [], // no kinded generics
        Some(ident_exec),
        [
            ParamSig::new(exec_expr.clone(), u32_ty),
            ParamSig::new(exec_expr.clone(), i32_ty),
        ],
        exec_expr,
        ty_data_ref(arena, d_scalar(ScalarTy::U32, arena)),
        [], // no nat constraints
    )
}

// nat_as_u64:
// <n: nat>() -[Any]-> u64
fn nat_as_u64_ty<'a>(arena: &'a Bump) -> FnTy<'a> {
    // generic nat parameter
    let n = Ident::new(arena, "n");
    let n_nat = IdentKinded {
        ident: n,
        kind: Kind::Nat,
    };

    // execution level: Any, carried via an exec identifier "ex"
    let ident_exec =
        IdentExec::new_in(arena, Ident::new(arena, "ex"), ExecTy::new(ExecTyKind::Any));
    let exec_expr = exec_ident(arena, ident_exec.ident.clone());

    FnTy::new(
        arena,
        [n_nat],                                            // generics
        Some(ident_exec),                                   // generic exec
        [],                                                 // params
        exec_expr,                                          // function exec
        ty_data_ref(arena, d_scalar(ScalarTy::U64, arena)), // return type
        [],                                                 // nat constraints
    )
}

// get_warp_id:
// <>() -[w: gpu.warp]-> u32
fn get_warp_id_ty<'a>(arena: &'a Bump) -> FnTy<'a> {
    // generic exec: w : gpu.warp
    let ident_exec = IdentExec::new_in(
        arena,
        Ident::new(arena, "w"),
        ExecTy::new(ExecTyKind::GpuWarp),
    );
    let exec_expr = exec_ident(arena, ident_exec.ident.clone());

    FnTy::new(
        arena,
        [],                                                 // no kinded generics
        Some(ident_exec),                                   // generic exec
        [],                                                 // params
        exec_expr,                                          // function exec
        ty_data_ref(arena, d_scalar(ScalarTy::U32, arena)), // return type
        [],                                                 // nat constraints
    )
}

// get_lane_id: <>() -[t: gpu.thread]-> u32
fn get_lane_id_ty<'a>(arena: &'a Bump) -> FnTy<'a> {
    let ident_exec = IdentExec::new_in(
        arena,
        Ident::new(arena, "t"),
        ExecTy::new(ExecTyKind::GpuThread),
    );
    let exec_expr = exec_ident(arena, ident_exec.ident.clone());

    FnTy::new(
        arena,
        [],                                                 // no kinded generics
        Some(ident_exec),                                   // generic exec
        [],                                                 // no params
        exec_expr,                                          // function exec
        ty_data_ref(arena, d_scalar(ScalarTy::U32, arena)), // return type
        [],                                                 // no nat constraints
    )
}

// thread_id_x: <>() -[gpu.thread]-> u32
fn thread_id_x_ty<'a>(arena: &'a Bump) -> FnTy<'a> {
    let ident_exec = IdentExec::new_in(
        arena,
        Ident::new(arena, "ex"),
        ExecTy::new(ExecTyKind::GpuThread),
    );
    let exec_expr = exec_ident(arena, ident_exec.ident.clone());

    FnTy::new(
        arena,
        [],                                                 // no kinded generics
        Some(ident_exec),                                   // generic exec
        [],                                                 // no params
        exec_expr,                                          // function exec
        ty_data_ref(arena, d_scalar(ScalarTy::U32, arena)), // return type
        [],                                                 // no nat constraints
    )
}

// gpu:
//   <>(i32) -[cpu.thread]-> Gpu
fn gpu_device_ty<'a>(arena: &'a Bump) -> FnTy<'a> {
    let ident_exec = IdentExec::new_in(
        arena,
        Ident::new(arena, "ex"),
        ExecTy::new(ExecTyKind::CpuThread),
    );
    let exec_expr = exec_ident(arena, ident_exec.ident.clone());

    FnTy::new(
        arena,
        [], // no kinded generics
        Some(ident_exec),
        [ParamSig::new(
            exec_expr.clone(),
            ty_data_ref(arena, d_scalar(ScalarTy::I32, arena)),
        )],
        exec_expr,
        ty_data_ref(arena, d_scalar(ScalarTy::Gpu, arena)),
        [], // no nat constraints
    )
}

// to_atomic_array:
//  <r: prv, m: mem, n: nat>(ex: &r uniq m [u32; n]) -[ex: Any]-> &r uniq m [AtomicU32; n]
fn to_atomic_array_ty<'a>(arena: &'a Bump) -> FnTy<'a> {
    let r = Ident::new(arena, "r");
    let m = Ident::new(arena, "m");
    let n = Ident::new(arena, "n");

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

    let ident_exec =
        IdentExec::new_in(arena, Ident::new(arena, "ex"), ExecTy::new(ExecTyKind::Any));
    let exec_expr = exec_ident(arena, ident_exec.ident.clone());

    // &r uniq m [u32; n]
    let param_dty = d_ref(
        arena,
        Provenance::Ident(r.clone()),
        Ownership::Uniq,
        Memory::Ident(m.clone()),
        d_array(arena, d_scalar(ScalarTy::U32, arena), Nat::Ident(n.clone())),
    );

    // &r uniq m [AtomicU32; n]
    let ret_dty = d_ref(
        arena,
        Provenance::Ident(r),
        Ownership::Uniq,
        Memory::Ident(m),
        d_array(arena, d_atomic(AtomicTy::AtomicU32, arena), Nat::Ident(n)),
    );

    FnTy::new(
        arena,
        [r_prv, m_mem, n_nat],
        Some(ident_exec),
        [ParamSig::new(
            exec_expr.clone(),
            ty_data_ref(arena, param_dty),
        )],
        exec_expr,
        ty_data_ref(arena, ret_dty),
        [], // no nat constraints
    )
}

// to_atomic:
//  <r: prv, m: mem>(&r uniq m u32) -[ex: Any]-> &r uniq m AtomicU32
fn to_atomic_ty<'a>(arena: &'a Bump) -> FnTy<'a> {
    let r = Ident::new(arena, "r");
    let m = Ident::new(arena, "m");

    let r_prv = IdentKinded {
        ident: r.clone(),
        kind: Kind::Provenance,
    };
    let m_mem = IdentKinded {
        ident: m.clone(),
        kind: Kind::Memory,
    };

    let ident_exec =
        IdentExec::new_in(arena, Ident::new(arena, "ex"), ExecTy::new(ExecTyKind::Any));
    let exec_expr = exec_ident(arena, ident_exec.ident.clone());

    // &r uniq m u32
    let param_dty = d_ref(
        arena,
        Provenance::Ident(r.clone()),
        Ownership::Uniq,
        Memory::Ident(m.clone()),
        d_scalar(ScalarTy::U32, arena),
    );

    // &r uniq m AtomicU32
    let ret_dty = d_ref(
        arena,
        Provenance::Ident(r),
        Ownership::Uniq,
        Memory::Ident(m),
        d_atomic(AtomicTy::AtomicU32, arena),
    );

    FnTy::new(
        arena,
        [r_prv, m_mem],
        Some(ident_exec),
        [ParamSig::new(
            exec_expr.clone(),
            ty_data_ref(arena, param_dty),
        )],
        exec_expr,
        ty_data_ref(arena, ret_dty),
        [],
    )
}

// atomic_store:
//  <r: prv, m: mem>(&r shrd m AtomicU32, u32) -[gpu.thread]-> ()
fn atomic_store_ty<'a>(arena: &'a Bump) -> FnTy<'a> {
    let r = Ident::new(arena, "r");
    let m = Ident::new(arena, "m");

    let r_prv = IdentKinded {
        ident: r.clone(),
        kind: Kind::Provenance,
    };
    let m_mem = IdentKinded {
        ident: m.clone(),
        kind: Kind::Memory,
    };

    let ident_exec = IdentExec::new_in(
        arena,
        Ident::new(arena, "ex"),
        ExecTy::new(ExecTyKind::GpuThread),
    );
    let exec_expr = exec_ident(arena, ident_exec.ident.clone());

    // &r shrd m AtomicU32
    let ptr_arg = d_ref(
        arena,
        Provenance::Ident(r),
        Ownership::Shrd,
        Memory::Ident(m),
        d_atomic(AtomicTy::AtomicU32, arena),
    );

    FnTy::new(
        arena,
        [r_prv, m_mem],
        Some(ident_exec),
        [
            ParamSig::new(exec_expr.clone(), ty_data_ref(arena, ptr_arg)),
            ParamSig::new(
                exec_expr.clone(),
                ty_data_ref(arena, d_scalar(ScalarTy::U32, arena)),
            ),
        ],
        exec_expr,
        ty_data_ref(arena, d_scalar(ScalarTy::Unit, arena)),
        [],
    )
}

// atomic_fetch_or:
//  <r: prv, m: mem>(&r shrd m AtomicU32, u32) -[gpu.thread]-> u32
fn atomic_fetch_or_ty<'a>(arena: &'a Bump) -> FnTy<'a> {
    let r = Ident::new(arena, "r");
    let m = Ident::new(arena, "m");

    let r_prv = IdentKinded {
        ident: r.clone(),
        kind: Kind::Provenance,
    };
    let m_mem = IdentKinded {
        ident: m.clone(),
        kind: Kind::Memory,
    };

    let ident_exec = IdentExec::new_in(
        arena,
        Ident::new(arena, "ex"),
        ExecTy::new(ExecTyKind::GpuThread),
    );
    let exec_expr = exec_ident(arena, ident_exec.ident.clone());

    // &r shrd m AtomicU32
    let ptr_arg = d_ref(
        arena,
        Provenance::Ident(r),
        Ownership::Shrd,
        Memory::Ident(m),
        d_atomic(AtomicTy::AtomicU32, arena),
    );

    FnTy::new(
        arena,
        [r_prv, m_mem],
        Some(ident_exec),
        [
            ParamSig::new(exec_expr.clone(), ty_data_ref(arena, ptr_arg)),
            ParamSig::new(
                exec_expr.clone(),
                ty_data_ref(arena, d_scalar(ScalarTy::U32, arena)),
            ),
        ],
        exec_expr,
        ty_data_ref(arena, d_scalar(ScalarTy::U32, arena)),
        [],
    )
}

// atomic_min:
//  <r: prv, m: mem>(&r shrd m AtomicI32, i32) -[gpu.thread]-> i32
fn atomic_min_ty<'a>(arena: &'a Bump) -> FnTy<'a> {
    let r = Ident::new(arena, "r");
    let m = Ident::new(arena, "m");

    let r_prv = IdentKinded {
        ident: r.clone(),
        kind: Kind::Provenance,
    };
    let m_mem = IdentKinded {
        ident: m.clone(),
        kind: Kind::Memory,
    };

    let ident_exec = IdentExec::new_in(
        arena,
        Ident::new(arena, "t"),
        ExecTy::new(ExecTyKind::GpuThread),
    );
    let exec_expr = exec_ident(arena, ident_exec.ident.clone());

    // &r shrd m AtomicI32
    let ptr_arg = d_ref(
        arena,
        Provenance::Ident(r),
        Ownership::Shrd,
        Memory::Ident(m),
        d_atomic(AtomicTy::AtomicI32, arena),
    );

    FnTy::new(
        arena,
        [r_prv, m_mem],
        Some(ident_exec),
        [
            ParamSig::new(exec_expr.clone(), ty_data_ref(arena, ptr_arg)),
            ParamSig::new(
                exec_expr.clone(),
                ty_data_ref(arena, d_scalar(ScalarTy::I32, arena)),
            ),
        ],
        exec_expr,
        ty_data_ref(arena, d_scalar(ScalarTy::I32, arena)),
        [],
    )
}

// atomic_fetch_add:
//  <r: prv, m: mem>(&r shrd m AtomicU32, u32) -[gpu.thread]-> u32
fn atomic_fetch_add_ty<'a>(arena: &'a Bump) -> FnTy<'a> {
    let r = Ident::new(arena, "r");
    let m = Ident::new(arena, "m");

    let r_prv = IdentKinded {
        ident: r.clone(),
        kind: Kind::Provenance,
    };
    let m_mem = IdentKinded {
        ident: m.clone(),
        kind: Kind::Memory,
    };

    let ident_exec = IdentExec::new_in(
        arena,
        Ident::new(arena, "ex"),
        ExecTy::new(ExecTyKind::GpuThread),
    );
    let exec_expr = exec_ident(arena, ident_exec.ident.clone());

    // &r shrd m AtomicU32
    let ptr_arg = d_ref(
        arena,
        Provenance::Ident(r),
        Ownership::Shrd,
        Memory::Ident(m),
        d_atomic(AtomicTy::AtomicU32, arena),
    );

    FnTy::new(
        arena,
        [r_prv, m_mem],
        Some(ident_exec),
        [
            ParamSig::new(exec_expr.clone(), ty_data_ref(arena, ptr_arg)),
            ParamSig::new(
                exec_expr.clone(),
                ty_data_ref(arena, d_scalar(ScalarTy::U32, arena)),
            ),
        ],
        exec_expr.clone(),
        ty_data_ref(arena, d_scalar(ScalarTy::U32, arena)),
        [],
    )
}

// atomic_load:
//  <r: prv, m: mem>(&r shrd m AtomicU32) -[gpu.thread]-> u32
fn atomic_load_ty<'a>(arena: &'a Bump) -> FnTy<'a> {
    let r = Ident::new(arena, "r");
    let m = Ident::new(arena, "m");

    let r_prv = IdentKinded {
        ident: r.clone(),
        kind: Kind::Provenance,
    };
    let m_mem = IdentKinded {
        ident: m.clone(),
        kind: Kind::Memory,
    };

    let ident_exec = IdentExec::new_in(
        arena,
        Ident::new(arena, "ex"),
        ExecTy::new(ExecTyKind::GpuThread),
    );
    let exec_expr = exec_ident(arena, ident_exec.ident.clone());

    // &r shrd m AtomicU32
    let ptr_arg = d_ref(
        arena,
        Provenance::Ident(r),
        Ownership::Shrd,
        Memory::Ident(m),
        d_atomic(AtomicTy::AtomicU32, arena),
    );

    FnTy::new(
        arena,
        [r_prv, m_mem],
        Some(ident_exec),
        [ParamSig::new(
            exec_expr.clone(),
            ty_data_ref(arena, ptr_arg),
        )],
        exec_expr,
        ty_data_ref(arena, d_scalar(ScalarTy::U32, arena)),
        [],
    )
}

// gpu_alloc_copy:
//   <r1: prv, r2: prv, d: dty>(
//      &r1 uniq cpu.mem Gpu, &r2 shrd cpu.mem d
//   ) -[cpu.thread]-> d @ gpu.global
fn gpu_alloc_copy_ty<'a>(arena: &'a Bump) -> FnTy<'a> {
    let r1 = Ident::new(arena, "r1");
    let r2 = Ident::new(arena, "r2");
    let d = Ident::new(arena, "d");

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

    let exec_expr = ExecExpr::new(arena, ExecExprKind::new(arena, BaseExec::CpuThread));

    // &r1 uniq cpu.mem Gpu
    let arg0 = d_ref(
        arena,
        Provenance::Ident(r1),
        Ownership::Uniq,
        Memory::CpuMem,
        d_scalar(ScalarTy::Gpu, arena),
    );

    // &r2 shrd cpu.mem d
    let arg1 = d_ref(
        arena,
        Provenance::Ident(r2),
        Ownership::Shrd,
        Memory::CpuMem,
        d_ident(d.clone(), arena),
    );

    // d @ gpu.global
    let ret_inner = d_ident(d, arena);
    let ret_dty_ref = arena.alloc(ret_inner);
    let ret_at = DataTy::new(arena, DataTyKind::At(ret_dty_ref, Memory::GpuGlobal));

    FnTy::new(
        arena,
        [r1_prv, r2_prv, d_dty],
        None,
        [
            ParamSig::new(exec_expr.clone(), ty_data_ref(arena, arg0)),
            ParamSig::new(exec_expr.clone(), ty_data_ref(arena, arg1)),
        ],
        exec_expr,
        ty_data_ref(arena, ret_at),
        [],
    )
}

// copy_to_host:
//   <r1: prv, r2: prv, d: dty>(
//      &r1 shrd gpu.global d, &r2 uniq cpu.mem d
//   ) -[cpu.thread]-> ()
fn copy_to_host_ty<'a>(arena: &'a Bump) -> FnTy<'a> {
    let r1 = Ident::new(arena, "r1");
    let r2 = Ident::new(arena, "r2");
    let d = Ident::new(arena, "d");

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

    let exec_expr = ExecExpr::new(arena, ExecExprKind::new(arena, BaseExec::CpuThread));

    // &r1 shrd gpu.global d
    let arg0 = d_ref(
        arena,
        Provenance::Ident(r1),
        Ownership::Shrd,
        Memory::GpuGlobal,
        d_ident(d.clone(), arena),
    );

    // &r2 uniq cpu.mem d
    let arg1 = d_ref(
        arena,
        Provenance::Ident(r2),
        Ownership::Uniq,
        Memory::CpuMem,
        d_ident(d, arena),
    );

    FnTy::new(
        arena,
        [r1_prv, r2_prv, d_dty],
        None,
        [
            ParamSig::new(exec_expr.clone(), ty_data_ref(arena, arg0)),
            ParamSig::new(exec_expr.clone(), ty_data_ref(arena, arg1)),
        ],
        exec_expr,
        ty_data_ref(arena, d_scalar(ScalarTy::Unit, arena)),
        [],
    )
}

// copy_to_gpu:
//  <r1: prv, r2: prv, d: dty>(&r1 uniq gpu.global d, &r2 shrd cpu.mem d)
//    -[cpu.thread]-> ()
fn copy_to_gpu_ty<'a>(arena: &'a Bump) -> FnTy<'a> {
    let r1 = Ident::new(arena, "r1");
    let r2 = Ident::new(arena, "r2");
    let d = Ident::new(arena, "d");

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

    let exec_expr = ExecExpr::new(arena, ExecExprKind::new(arena, BaseExec::CpuThread));

    // &r1 uniq gpu.global d
    let arg0 = d_ref(
        arena,
        Provenance::Ident(r1),
        Ownership::Uniq,
        Memory::GpuGlobal,
        d_ident(d.clone(), arena),
    );

    // &r2 shrd cpu.mem d
    let arg1 = d_ref(
        arena,
        Provenance::Ident(r2),
        Ownership::Shrd,
        Memory::CpuMem,
        d_ident(d, arena),
    );

    FnTy::new(
        arena,
        [r1_prv, r2_prv, d_dty],
        None,
        [
            ParamSig::new(exec_expr.clone(), ty_data_ref(arena, arg0)),
            ParamSig::new(exec_expr.clone(), ty_data_ref(arena, arg1)),
        ],
        exec_expr,
        ty_data_ref(arena, d_scalar(ScalarTy::Unit, arena)),
        [],
    )
}

// to_view:
//  <n: nat, d: dty>([d; n]) -[Any]-> [[d; n]]
fn to_view_ty<'a>(arena: &'a Bump) -> FnTy<'a> {
    let n = Ident::new(arena, "n");
    let d = Ident::new(arena, "d");

    let n_nat = IdentKinded {
        ident: n.clone(),
        kind: Kind::Nat,
    };
    let d_dty = IdentKinded {
        ident: d.clone(),
        kind: Kind::DataTy,
    };

    let ident_exec =
        IdentExec::new_in(arena, Ident::new(arena, "ex"), ExecTy::new(ExecTyKind::Any));
    let exec_expr = ExecExpr::new(
        arena,
        ExecExprKind::new(arena, BaseExec::Ident(ident_exec.ident.clone())),
    );

    // param: [d; n]
    let param_dty = d_array(arena, d_ident(d.clone(), arena), Nat::Ident(n.clone()));

    // return: [[d; n]]
    let ret_dty = d_array_shape(arena, d_ident(d, arena), Nat::Ident(n));

    FnTy::new(
        arena,
        [n_nat, d_dty],
        Some(ident_exec),
        [ParamSig::new(
            exec_expr.clone(),
            ty_data_ref(arena, param_dty),
        )],
        exec_expr,
        ty_data_ref(arena, ret_dty),
        [],
    )
}

// rev / rev_mut
// <n: nat, d: dty>([[d; n]]) -[Any]-> [[d; n]]
fn reverse_ty<'a>(arena: &'a Bump) -> FnTy<'a> {
    let n = Ident::new(arena, "n");
    let d = Ident::new(arena, "d");

    let n_nat = IdentKinded {
        ident: n.clone(),
        kind: Kind::Nat,
    };
    let d_dty = IdentKinded {
        ident: d.clone(),
        kind: Kind::DataTy,
    };

    let ident_exec =
        IdentExec::new_in(arena, Ident::new(arena, "ex"), ExecTy::new(ExecTyKind::Any));
    let exec_expr = ExecExpr::new(
        arena,
        ExecExprKind::new(arena, BaseExec::Ident(ident_exec.ident.clone())),
    );

    // param: [[d; n]]
    let param = d_array_shape(arena, d_ident(d.clone(), arena), Nat::Ident(n.clone()));
    // return: [[d; n]]
    let ret = d_array_shape(arena, d_ident(d, arena), Nat::Ident(n));

    FnTy::new(
        arena,
        [n_nat, d_dty],
        Some(ident_exec),
        [ParamSig::new(exec_expr.clone(), ty_data_ref(arena, param))],
        exec_expr,
        ty_data_ref(arena, ret),
        [],
    )
}

// map_mut:
// <d: dty, d2: dty, n: nat>(|d| -[ex]-> d2, [[d; n]]) -[ex: Any]-> [[d2; n]]
fn map_ty<'a>(arena: &'a Bump) -> FnTy<'a> {
    let d = Ident::new(arena, "d");
    let d2 = Ident::new(arena, "d2");
    let n = Ident::new(arena, "n");

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

    let ident_exec =
        IdentExec::new_in(arena, Ident::new(arena, "ex"), ExecTy::new(ExecTyKind::Any));
    let exec_expr = ExecExpr::new(
        arena,
        ExecExprKind::new(arena, BaseExec::Ident(ident_exec.ident.clone())),
    );

    // Build the inner function type: (d) -[ex]-> d2
    let inner_param_ty = ty_data_ref(arena, d_ident(d.clone(), arena));
    let inner_ret_ty = ty_data_ref(arena, d_ident(d2.clone(), arena));

    let inner_fn = FnTy::new(
        arena,
        [],   // no generics
        None, // no generic exec
        [ParamSig::new(exec_expr.clone(), inner_param_ty)],
        exec_expr.clone(),
        inner_ret_ty,
        [], // no nat constraints
    );
    let inner_fn_ref: &'a FnTy<'a> = arena.alloc(inner_fn);
    let inner_fn_ty_ref: &'a Ty<'a> = arena.alloc(Ty {
        ty: TyKind::FnTy(inner_fn_ref),
        span: None,
    });

    // Second param: [[d; n]]
    let arr_param = d_array_shape(arena, d_ident(d, arena), Nat::Ident(n.clone()));

    // Return type: [[d2; n]]
    let ret = d_array_shape(arena, d_ident(d2, arena), Nat::Ident(n));

    FnTy::new(
        arena,
        [d_dty, d2_dty, n_nat],
        Some(ident_exec),
        [
            ParamSig::new(exec_expr.clone(), inner_fn_ty_ref),
            ParamSig::new(exec_expr.clone(), ty_data_ref(arena, arr_param)),
        ],
        exec_expr,
        ty_data_ref(arena, ret),
        [],
    )
}

// Small Nat helper (arena-allocates both operands)
#[inline]
fn n_binop<'a>(arena: &'a Bump, op: BinOpNat, l: Nat<'a>, r: Nat<'a>) -> Nat<'a> {
    let l_ref = arena.alloc(l);
    let r_ref = arena.alloc(r);
    Nat::BinOp(op, l_ref, r_ref)
}

// group/group_mut:
// <s: nat, n: nat, d: dty>([[d; n]]) -[Any]-> [[ [[d; s]]; n/s ]]
fn group_ty<'a>(arena: &'a Bump) -> FnTy<'a> {
    // generics
    let s = Ident::new(arena, "s");
    let n = Ident::new(arena, "n");
    let d = Ident::new(arena, "d");

    let s_nat = IdentKinded {
        ident: s.clone(),
        kind: Kind::Nat,
    };
    let n_nat = IdentKinded {
        ident: n.clone(),
        kind: Kind::Nat,
    };
    let d_dty = IdentKinded {
        ident: d.clone(),
        kind: Kind::DataTy,
    };

    // exec
    let ident_exec =
        IdentExec::new_in(arena, Ident::new(arena, "ex"), ExecTy::new(ExecTyKind::Any));
    let exec_expr = ExecExpr::new(
        arena,
        ExecExprKind::new(arena, BaseExec::Ident(ident_exec.ident.clone())),
    );

    // param: [[d; n]]
    let param = d_array_shape(arena, d_ident(d.clone(), arena), Nat::Ident(n.clone()));

    // inner element: [[d; s]]
    let inner = d_array_shape(arena, d_ident(d, arena), Nat::Ident(s.clone()));

    // outer size: n / s   (arena-allocated operands)
    let n_div_s = n_binop(
        arena,
        BinOpNat::Div,
        Nat::Ident(n.clone()),
        Nat::Ident(s.clone()),
    );

    // return: [[ [[d; s]]; n/s ]]
    let ret = d_array_shape(arena, inner, n_div_s);

    // constraint: (n % s) == 0  (all pieces arena-allocated)
    let n_mod_s = n_binop(arena, BinOpNat::Mod, Nat::Ident(n), Nat::Ident(s));
    let constr = NatConstr::Eq(arena.alloc(n_mod_s), arena.alloc(Nat::Lit(0)));

    FnTy::new(
        arena,
        [s_nat, n_nat, d_dty],
        Some(ident_exec),
        [ParamSig::new(exec_expr.clone(), ty_data_ref(arena, param))],
        exec_expr,
        ty_data_ref(arena, ret),
        [constr],
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
fn select_range_ty<'a>(arena: &'a Bump) -> FnTy<'a> {
    // generics
    let l = Ident::new(arena, "l");
    let u = Ident::new(arena, "u");
    let n = Ident::new(arena, "n");
    let d = Ident::new(arena, "d");

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
    let d_dty = IdentKinded {
        ident: d.clone(),
        kind: Kind::DataTy,
    };

    // exec
    let ident_exec =
        IdentExec::new_in(arena, Ident::new(arena, "ex"), ExecTy::new(ExecTyKind::Any));
    let exec_expr = ExecExpr::new(
        arena,
        ExecExprKind::new(arena, BaseExec::Ident(ident_exec.ident.clone())),
    );

    // param: [[d; n]]
    let param = d_array_shape(arena, d_ident(d.clone(), arena), Nat::Ident(n.clone()));

    // return: [[d; u - l]]
    let u_minus_l = n_binop(
        arena,
        BinOpNat::Sub,
        Nat::Ident(u.clone()),
        Nat::Ident(l.clone()),
    );
    let ret = d_array_shape(arena, d_ident(d, arena), u_minus_l);

    // constraints: l < u  AND  (u < n OR u == n)
    let c_lt_lu = NatConstr::Lt(
        arena.alloc(Nat::Ident(l.clone())),
        arena.alloc(Nat::Ident(u.clone())),
    );
    let c_lt_un = NatConstr::Lt(
        arena.alloc(Nat::Ident(u.clone())),
        arena.alloc(Nat::Ident(n.clone())),
    );
    let c_eq_un = NatConstr::Eq(arena.alloc(Nat::Ident(u)), arena.alloc(Nat::Ident(n)));
    let c_or = NatConstr::Or(arena.alloc(c_lt_un), arena.alloc(c_eq_un));
    let constr = NatConstr::And(arena.alloc(c_lt_lu), arena.alloc(c_or));

    FnTy::new(
        arena,
        [l_nat, u_nat, n_nat, d_dty],
        Some(ident_exec),
        [ParamSig::new(exec_expr.clone(), ty_data_ref(arena, param))],
        exec_expr,
        ty_data_ref(arena, ret),
        [constr],
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
fn join_ty<'a>(arena: &'a Bump) -> FnTy<'a> {
    // generics
    let n = Ident::new(arena, "n");
    let o = Ident::new(arena, "o");
    let d = Ident::new(arena, "d");

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

    // exec
    let ident_exec =
        IdentExec::new_in(arena, Ident::new(arena, "ex"), ExecTy::new(ExecTyKind::Any));
    let exec_expr = ExecExpr::new(
        arena,
        ExecExprKind::new(arena, BaseExec::Ident(ident_exec.ident.clone())),
    );

    // param: [[ [[d; n]]; o ]]
    let inner = d_array_shape(arena, d_ident(d.clone(), arena), Nat::Ident(n.clone()));
    let param = d_array_shape(arena, inner, Nat::Ident(o.clone()));

    // return: [[d; n * o]]
    let n_mul_o = n_binop(arena, BinOpNat::Mul, Nat::Ident(n), Nat::Ident(o));
    let ret = d_array_shape(arena, d_ident(d, arena), n_mul_o);

    FnTy::new(
        arena,
        [o_nat, n_nat, d_dty],
        Some(ident_exec),
        [ParamSig::new(exec_expr.clone(), ty_data_ref(arena, param))],
        exec_expr,
        ty_data_ref(arena, ret),
        [],
    )
}

// transpose:
//  <r: prv, m: mem, n: nat, o: nat, d: dty>(&r W m [[ [[d; n]]; o]]) -> &r W m [[ [[d; o]]; n]]
fn transpose_ty<'a>(arena: &'a Bump) -> FnTy<'a> {
    // generics
    let n = Ident::new(arena, "n");
    let o = Ident::new(arena, "o");
    let d = Ident::new(arena, "d");

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

    // exec
    let ident_exec =
        IdentExec::new_in(arena, Ident::new(arena, "ex"), ExecTy::new(ExecTyKind::Any));
    let exec_expr = ExecExpr::new(
        arena,
        ExecExprKind::new(arena, BaseExec::Ident(ident_exec.ident.clone())),
    );

    // param: [[ [[d; n]]; o ]]
    let inner_param = d_array_shape(arena, d_ident(d.clone(), arena), Nat::Ident(n.clone()));
    let param = d_array_shape(arena, inner_param, Nat::Ident(o.clone()));

    // return: [[ [[d; o]]; n ]]
    let inner_ret = d_array_shape(arena, d_ident(d, arena), Nat::Ident(o));
    let ret = d_array_shape(arena, inner_ret, Nat::Ident(n));

    FnTy::new(
        arena,
        [n_nat, o_nat, d_dty],
        Some(ident_exec),
        [ParamSig::new(exec_expr.clone(), ty_data_ref(arena, param))],
        exec_expr,
        ty_data_ref(arena, ret),
        [],
    )
}
