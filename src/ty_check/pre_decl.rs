use crate::ast::DataTy::Scalar;
use crate::ast::{
    internal, BinOpNat, DataTy, ExecLoc, Ident, IdentKinded, Kind, Memory, Nat, Ownership,
    Provenance, ScalarTy, Ty, ViewTy,
};

pub static GPU: &str = "gpu";
pub static GPU_ALLOC: &str = "gpu_alloc";
pub static COPY_TO_HOST: &str = "copy_to_host";
pub static EXEC: &str = "exec";

pub static TO_VIEW: &str = "to_view";
pub static TO_VIEW_MUT: &str = "to_view_mut";
pub static SPLIT_AT: &str = "split_at";
pub static GROUP: &str = "group";
pub static JOIN: &str = "join";
pub static ZIP: &str = "zip";
pub static TRANSPOSE: &str = "transpose";

pub static SPLIT: &str = "split";

pub fn fun_decls() -> Vec<(&'static str, DataTy)> {
    let decls = [
        // Built-in functions
        (GPU, gpu_ty()),
        (GPU_ALLOC, gpu_alloc_ty()),
        (COPY_TO_HOST, copy_to_host_ty()),
        (EXEC, exec_ty()),
        // View constructors
        (TO_VIEW, to_view_ty(Ownership::Shrd)),
        (TO_VIEW_MUT, to_view_ty(Ownership::Uniq)),
        (SPLIT_AT, split_at_ty()),
        (ZIP, zip_ty()),
        (GROUP, group_ty()),
        (SPLIT, split_ty()),
    ];

    decls.to_vec()
}

// split:
//  <k: nat, n: nat>(Block<Thread, n>) -> (Block<Thread, k>, Block<Thread, n-k>)
// TODO add t: ty for inner part (i.e., Thread/Warp), or do it even more correctly right away...
fn split_ty() -> DataTy {
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
    DataTy::Fn(
        vec![k_nat, n_nat],
        vec![Ty::Data(DataTy::Block(
            Box::new(DataTy::Scalar(ScalarTy::Thread)),
            Nat::Ident(n.clone()),
        ))],
        Box::new(internal::FrameExpr::Empty),
        ExecLoc::View,
        Box::new(Ty::Data(DataTy::Tuple(vec![
            DataTy::Block(
                Box::new(DataTy::Scalar(ScalarTy::Thread)),
                Nat::Ident(k.clone()),
            ),
            DataTy::Block(
                Box::new(DataTy::Scalar(ScalarTy::Thread)),
                Nat::BinOp(
                    BinOpNat::Sub,
                    Box::new(Nat::Ident(n)),
                    Box::new(Nat::Ident(k)),
                ),
            ),
        ]))),
    )
}

// gpu:
//   <>(i32) -[cpu.thread]-> Gpu
fn gpu_ty() -> DataTy {
    DataTy::Fn(
        vec![],
        vec![Ty::Data(DataTy::Scalar(ScalarTy::I32))],
        Box::new(internal::FrameExpr::Empty),
        ExecLoc::CpuThread,
        Box::new(Ty::Data(DataTy::Scalar(ScalarTy::Gpu))),
    )
}

// gpu_alloc:
//   <r1: prv, r2: prv, m1: mem, m2: mem, t: ty>(
//      &r1 uniq m1 Gpu, &r2 shrd m2 t
//   ) -[cpu.thread]-> t @ gpu.global
fn gpu_alloc_ty() -> DataTy {
    let r1 = Ident::new("r1");
    let r2 = Ident::new("r2");
    let m1 = Ident::new("m1");
    let m2 = Ident::new("m2");
    let t = Ident::new("t");
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
    let t_ty = IdentKinded {
        ident: t.clone(),
        kind: Kind::Ty,
    };
    DataTy::Fn(
        vec![r1_prv, r2_prv, m1_mem, m2_mem, t_ty],
        vec![
            Ty::Data(DataTy::Ref(
                Provenance::Ident(r1),
                Ownership::Uniq,
                Memory::Ident(m1),
                Box::new(DataTy::Scalar(ScalarTy::Gpu)),
            )),
            Ty::Data(DataTy::Ref(
                Provenance::Ident(r2),
                Ownership::Shrd,
                Memory::Ident(m2),
                Box::new(DataTy::Ident(t.clone())),
            )),
        ],
        Box::new(internal::FrameExpr::Empty),
        ExecLoc::CpuThread,
        Box::new(Ty::Data(DataTy::At(
            Box::new(DataTy::Ident(t)),
            Memory::GpuGlobal,
        ))),
    )
}

// copy_to_host:
//   <r1: prv, r2: prv, t: ty>(&r1 shrd gpu.global ty, &r2 uniq cpu.heap ty)
//      -[cpu.thread]-> ()
fn copy_to_host_ty() -> DataTy {
    let r1 = Ident::new("r1");
    let r2 = Ident::new("r2");
    let t = Ident::new("t");
    let r1_prv = IdentKinded {
        ident: r1.clone(),
        kind: Kind::Provenance,
    };
    let r2_prv = IdentKinded {
        ident: r2.clone(),
        kind: Kind::Provenance,
    };
    let t_ty = IdentKinded {
        ident: t.clone(),
        kind: Kind::Ty,
    };
    DataTy::Fn(
        vec![r1_prv, r2_prv, t_ty],
        vec![
            Ty::Data(DataTy::Ref(
                Provenance::Ident(r1),
                Ownership::Shrd,
                Memory::GpuGlobal,
                Box::new(DataTy::Ident(t.clone())),
            )),
            Ty::Data(DataTy::Ref(
                Provenance::Ident(r2),
                Ownership::Uniq,
                Memory::CpuHeap,
                Box::new(DataTy::Ident(t)),
            )),
        ],
        Box::new(internal::FrameExpr::Empty),
        ExecLoc::CpuThread,
        Box::new(Ty::Data(DataTy::Scalar(ScalarTy::Unit))),
    )
}

// exec: <blocks: nat, threads: nat, r: prv, m: mem, elem: ty, n: nat>(
//        &r uniq m Gpu,
//        [[elem; n]],
//        (Grid<Block<Thread, threads>, blocks>, [[elem; n]]) -[gpu]-> ())
// -> ()
fn exec_ty() -> DataTy {
    let blocks = Ident::new("blocks");
    let threads = Ident::new("threads");
    let r = Ident::new("r");
    let m = Ident::new("m");
    let elem = Ident::new("elem");
    let n = Ident::new("n");
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
    let elem_ty = IdentKinded {
        ident: elem.clone(),
        kind: Kind::Ty,
    };
    let n_nat = IdentKinded {
        ident: n.clone(),
        kind: Kind::Nat,
    };
    DataTy::Fn(
        vec![blocks_nat, threads_nat, r_prv, m_mem, elem_ty, n_nat],
        vec![
            Ty::Data(DataTy::Ref(
                Provenance::Ident(r),
                Ownership::Uniq,
                Memory::Ident(m),
                Box::new(DataTy::Scalar(ScalarTy::Gpu)),
            )),
            Ty::View(ViewTy::Array(
                Box::new(Ty::Ident(elem.clone())),
                Nat::Ident(n.clone()),
            )),
            Ty::Data(DataTy::Fn(
                vec![],
                vec![
                    // Ty::View(ViewTy::Array(
                    //     Box::new(Ty::View(ViewTy::Array(
                    //         Box::new(Ty::Data(DataTy::Scalar(ScalarTy::Thread))),
                    //         Nat::Ident(threads),
                    //     ))),
                    //     Nat::Ident(blocks),
                    // )),
                    Ty::Data(DataTy::Grid(
                        Box::new(DataTy::Block(
                            Box::new(DataTy::Scalar(ScalarTy::Thread)),
                            Nat::Ident(threads),
                        )),
                        Nat::Ident(blocks),
                    )),
                    Ty::View(ViewTy::Array(Box::new(Ty::Ident(elem)), Nat::Ident(n))),
                ],
                Box::new(internal::FrameExpr::Empty),
                ExecLoc::Gpu,
                Box::new(Ty::Data(DataTy::Scalar(ScalarTy::Unit))),
            )),
        ],
        Box::new(internal::FrameExpr::Empty),
        ExecLoc::CpuThread,
        Box::new(Ty::Data(DataTy::Scalar(ScalarTy::Unit))),
    )
}

// TODO FIX Error: t: ty is too general. This means [t; n] could contain a view
//  (which is not well-kinded).
// to_view:
//  <r: prv, m: mem, n: nat, t: ty>(&r shrd m [t; n]) -[view]-> [[&r shrd m t; n]]
// to_view_mut:
//  <r: prv, m: mem, n: nat, t: ty>(&r uniq m [t; n]) -[view]-> [[&r uniq m t; n]]
fn to_view_ty(own: Ownership) -> DataTy {
    let r = Ident::new("r");
    let m = Ident::new("m");
    let n = Ident::new("n");
    let t = Ident::new("t");
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
    let t_ty = IdentKinded {
        ident: t.clone(),
        kind: Kind::Ty,
    };
    DataTy::Fn(
        vec![r_prv, m_mem, n_nat, t_ty],
        vec![Ty::Data(DataTy::Ref(
            Provenance::Ident(r.clone()),
            own,
            Memory::Ident(m.clone()),
            Box::new(DataTy::Array(
                Box::new(DataTy::Ident(t.clone())),
                Nat::Ident(n.clone()),
            )),
        ))],
        Box::new(internal::FrameExpr::Empty),
        ExecLoc::View,
        Box::new(Ty::View(ViewTy::Array(
            Box::new(Ty::Data(DataTy::Ref(
                Provenance::Ident(r),
                own,
                Memory::Ident(m),
                Box::new(DataTy::Ident(t)),
            ))),
            Nat::Ident(n),
        ))),
    )
}

// group:
//  <size: nat, n: nat, t: ty>([[t; n]]) -> [[ [[t; size]]; n/size ]]
fn group_ty() -> DataTy {
    let s = Ident::new("s");
    let n = Ident::new("n");
    let t = Ident::new("t");
    let s_nat = IdentKinded {
        ident: s.clone(),
        kind: Kind::Nat,
    };
    let n_nat = IdentKinded {
        ident: n.clone(),
        kind: Kind::Nat,
    };
    let t_ty = IdentKinded {
        ident: t.clone(),
        kind: Kind::Ty,
    };
    DataTy::Fn(
        vec![s_nat, n_nat, t_ty],
        vec![Ty::View(ViewTy::Array(
            Box::new(Ty::Ident(t.clone())),
            Nat::Ident(n.clone()),
        ))],
        Box::new(internal::FrameExpr::Empty),
        ExecLoc::View,
        Box::new(Ty::View(ViewTy::Array(
            Box::new(Ty::View(ViewTy::Array(
                Box::new(Ty::Ident(t.clone())),
                Nat::Ident(s.clone()),
            ))),
            Nat::BinOp(
                BinOpNat::Div,
                Box::new(Nat::Ident(n)),
                Box::new(Nat::Ident(s)),
            ),
        ))),
    )
}

// join:
//  <m: nat, n: nat, t: ty>([[ [[t; n]]; m]]) -> [[t; m*n]]
fn join_ty() -> DataTy {
    let m = Ident::new("m");
    let n = Ident::new("n");
    let t = Ident::new("t");
    let m_nat = IdentKinded {
        ident: m.clone(),
        kind: Kind::Nat,
    };
    let n_nat = IdentKinded {
        ident: n.clone(),
        kind: Kind::Nat,
    };
    let t_ty = IdentKinded {
        ident: t.clone(),
        kind: Kind::Ty,
    };
    DataTy::Fn(
        vec![m_nat, n_nat, t_ty],
        vec![Ty::View(ViewTy::Array(
            Box::new(Ty::View(ViewTy::Array(
                Box::new(Ty::Ident(t.clone())),
                Nat::Ident(n.clone()),
            ))),
            Nat::Ident(m.clone()),
        ))],
        Box::new(internal::FrameExpr::Empty),
        ExecLoc::View,
        Box::new(Ty::View(ViewTy::Array(
            Box::new(Ty::Ident(t)),
            Nat::BinOp(
                BinOpNat::Mul,
                Box::new(Nat::Ident(m)),
                Box::new(Nat::Ident(n)),
            ),
        ))),
    )
}

// transpose:
//  <m: nat, n: nat, t: ty>([[ [[t; n]]; m]]) -> [[ [[t; m]]; n]]
fn transpose_ty() -> DataTy {
    let m = Ident::new("m");
    let n = Ident::new("n");
    let t = Ident::new("t");
    let m_nat = IdentKinded {
        ident: m.clone(),
        kind: Kind::Nat,
    };
    let n_nat = IdentKinded {
        ident: n.clone(),
        kind: Kind::Nat,
    };
    let t_ty = IdentKinded {
        ident: t.clone(),
        kind: Kind::Ty,
    };
    DataTy::Fn(
        vec![m_nat, n_nat, t_ty],
        vec![Ty::View(ViewTy::Array(
            Box::new(Ty::View(ViewTy::Array(
                Box::new(Ty::Ident(t.clone())),
                Nat::Ident(n.clone()),
            ))),
            Nat::Ident(m.clone()),
        ))],
        Box::new(internal::FrameExpr::Empty),
        ExecLoc::View,
        Box::new(Ty::View(ViewTy::Array(
            Box::new(Ty::View(ViewTy::Array(
                Box::new(Ty::Ident(t)),
                Nat::Ident(m),
            ))),
            Nat::Ident(n),
        ))),
    )
}

// zip:
//  <n: nat, t1: ty, t2:ty>([[t1; n]], [[t2; n]]) -> [[{t1, t2}; n]]
fn zip_ty() -> DataTy {
    let n = Ident::new("n");
    let t1 = Ident::new("t1");
    let t2 = Ident::new("t2");
    let n_nat = IdentKinded {
        ident: n.clone(),
        kind: Kind::Nat,
    };
    let t1_ty = IdentKinded {
        ident: t1.clone(),
        kind: Kind::Ty,
    };
    let t2_ty = IdentKinded {
        ident: t2.clone(),
        kind: Kind::Ty,
    };
    DataTy::Fn(
        vec![n_nat, t1_ty, t2_ty],
        vec![
            Ty::View(ViewTy::Array(
                Box::new(Ty::Ident(t1.clone())),
                Nat::Ident(n.clone()),
            )),
            Ty::View(ViewTy::Array(
                Box::new(Ty::Ident(t2.clone())),
                Nat::Ident(n.clone()),
            )),
        ],
        Box::new(internal::FrameExpr::Empty),
        ExecLoc::View,
        Box::new(Ty::View(ViewTy::Array(
            Box::new(Ty::View(ViewTy::Tuple(vec![Ty::Ident(t1), Ty::Ident(t2)]))),
            Nat::Ident(n),
        ))),
    )
}

// split:
//  <s: nat, n: nat, t: ty>([[t; n]]) -> {[[t; s]], [[t; n-s]]}
fn split_at_ty() -> DataTy {
    let s = Ident::new("s");
    let n = Ident::new("n");
    let t = Ident::new("t");
    let s_nat = IdentKinded {
        ident: s.clone(),
        kind: Kind::Nat,
    };
    let n_nat = IdentKinded {
        ident: n.clone(),
        kind: Kind::Nat,
    };
    let t_ty = IdentKinded {
        ident: t.clone(),
        kind: Kind::Ty,
    };
    DataTy::Fn(
        vec![s_nat, n_nat, t_ty],
        vec![Ty::View(ViewTy::Array(
            Box::new(Ty::Ident(t.clone())),
            Nat::Ident(n.clone()),
        ))],
        Box::new(internal::FrameExpr::Empty),
        ExecLoc::View,
        Box::new(Ty::View(ViewTy::Tuple(vec![
            Ty::View(ViewTy::Array(
                Box::new(Ty::Ident(t.clone())),
                Nat::Ident(s.clone()),
            )),
            Ty::View(ViewTy::Array(
                Box::new(Ty::Ident(t)),
                Nat::BinOp(
                    BinOpNat::Sub,
                    Box::new(Nat::Ident(n)),
                    Box::new(Nat::Ident(s)),
                ),
            )),
        ]))),
    )
}
