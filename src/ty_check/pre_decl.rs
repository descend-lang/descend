use crate::ast::{
    internal, ExecLoc, Ident, IdentKinded, Kind, Memory, Nat, Ownership, Provenance, Ty,
};

pub static GPU_ALLOC: &str = "gpu_alloc";
pub static COPY_TO_HOST: &str = "copy_to_host";
pub static GPU: &str = "gpu";

pub static TO_VIEW: &str = "to_view";

pub struct FunDecl {
    pub name: String,
    pub ty: Ty,
}

// TODO add correct predeclared functions with their types
pub(super) fn fun_decls() -> Vec<FunDecl> {
    let decls: [(&str, Ty); 1] = [(TO_VIEW, to_view_ty())];

    decls
        .iter()
        .map(|(name, ty)| FunDecl {
            name: name.to_string(),
            ty: ty.clone(),
        })
        .collect()
}

// gpu_alloc:
//   <r1: prv, r2: prv, m1: mem, m2: mem, t: ty>(
//      &r1 uniq m1 Gpu, &r2 shrd m2 t
//   ) -[cpu.thread]-> t @ gpu.global
fn gpu_alloc_ty() -> Ty {
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
    Ty::Fn(
        vec![r1_prv, r2_prv, m1_mem, m2_mem, t_ty],
        vec![
            Ty::Ref(
                Provenance::Ident(r1),
                Ownership::Uniq,
                Memory::Ident(m1),
                Box::new(Ty::Gpu),
            ),
            Ty::Ref(
                Provenance::Ident(r2),
                Ownership::Shrd,
                Memory::Ident(m2),
                Box::new(Ty::Ident(t.clone())),
            ),
        ],
        Box::new(internal::FrameExpr::Empty),
        ExecLoc::CpuThread,
        Box::new(Ty::At(Box::new(Ty::Ident(t)), Memory::GpuGlobal)),
    )
}

// to_view:
//  <r: prv, m: mem, n: nat, t: ty>(&r shrd m [t; n]) -[view]-> [[&r shrd m t; n]]
fn to_view_ty() -> Ty {
    let r = Ident::new("r");
    let m = Ident::new("m");
    let n = Ident::new("n");
    let t = Ident::new("t");
    let ex = Ident::new("ex");
    let r_prv = IdentKinded {
        ident: r.clone(),
        kind: Kind::Provenance,
    };
    let m_mem = IdentKinded {
        ident: m.clone(),
        kind: Kind::Memory,
    };
    let ex_exec = IdentKinded {
        ident: ex.clone(),
        kind: Kind::Exec,
    };
    let n_nat = IdentKinded {
        ident: n.clone(),
        kind: Kind::Nat,
    };
    let t_ty = IdentKinded {
        ident: t.clone(),
        kind: Kind::Ty,
    };
    Ty::Fn(
        vec![r_prv, m_mem, ex_exec, n_nat, t_ty],
        vec![Ty::Ref(
            Provenance::Ident(r.clone()),
            Ownership::Shrd,
            Memory::Ident(m.clone()),
            Box::new(Ty::Array(
                Box::new(Ty::Ident(t.clone())),
                Nat::Ident(n.clone()),
            )),
        )],
        Box::new(internal::FrameExpr::Empty),
        ExecLoc::View,
        Box::new(Ty::ArrayView(
            Box::new(Ty::Ref(
                Provenance::Ident(r),
                Ownership::Shrd,
                Memory::Ident(m),
                Box::new(Ty::Ident(t)),
            )),
            Nat::Ident(n),
        )),
    )
}
