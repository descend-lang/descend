// Constructs in this module are part of the AST but not part of the user facing syntax.
// These are also used in typechecking and ty_check::ctxs

// TODO specific access modifiers

use super::{Ident, Ownership, PlaceExpr, Ty};
use crate::ast::{ExecExpr, Mutability, PlaceExprKind};
use std::collections::HashSet;

pub type Frame = Vec<FrameEntry>;
pub fn append_idents_typed(frm: &Frame, idents_typed: Vec<IdentTyped>) -> Frame {
    let mut new_frm = frm.clone();
    new_frm.append(
        &mut idents_typed
            .into_iter()
            .map(FrameEntry::Var)
            .collect::<Vec<_>>(),
    );
    new_frm
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub enum FrameEntry {
    Var(IdentTyped),
    PrvMapping(PrvMapping),
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub struct IdentTyped {
    pub ident: Ident,
    pub ty: Ty,
    pub mutbl: Mutability,
    pub exec: ExecExpr,
}

impl IdentTyped {
    pub fn new(ident: Ident, ty: Ty, mutbl: Mutability, exec: ExecExpr) -> Self {
        IdentTyped {
            ident,
            ty,
            mutbl,
            exec,
        }
    }
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub struct PrvMapping {
    pub prv: String,
    pub loans: HashSet<Loan>,
}

impl PrvMapping {
    pub fn new(name: &str) -> Self {
        PrvMapping {
            prv: name.to_string(),
            loans: HashSet::new(),
        }
    }
}

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub struct Loan {
    pub place_expr: PlaceExpr,
    pub own: Ownership,
}

pub type Path = Vec<usize>;
#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub struct Place {
    pub ident: Ident,
    pub path: Path,
}
impl Place {
    pub fn new(ident: Ident, path: Path) -> Self {
        Place { ident, path }
    }

    pub fn to_place_expr(&self) -> PlaceExpr {
        self.path.iter().fold(
            PlaceExpr::new(PlaceExprKind::Ident(self.ident.clone())),
            |pl_expr, path_entry| {
                PlaceExpr::new(PlaceExprKind::Proj(Box::new(pl_expr), *path_entry))
            },
        )
    }
}

pub enum PlaceCtx {
    Proj(Box<PlaceCtx>, usize),
    Deref(Box<PlaceCtx>),
    Hole,
}

impl PlaceCtx {
    pub fn insert_pl_expr(&self, pl_expr: PlaceExpr) -> PlaceExpr {
        match self {
            Self::Hole => pl_expr,
            Self::Proj(pl_ctx, n) => PlaceExpr::new(PlaceExprKind::Proj(
                Box::new(pl_ctx.insert_pl_expr(pl_expr)),
                n.clone(),
            )),
            Self::Deref(pl_ctx) => PlaceExpr::new(PlaceExprKind::Deref(Box::new(
                pl_ctx.insert_pl_expr(pl_expr),
            ))),
        }
    }

    // Assumes the PlaceCtx HAS an innermost deref, meaning the Hole is wrapped by a Deref.
    // This is always true for PlaceCtxs created by PlaceExpr.to_pl_ctx_and_most_specif_pl
    pub fn without_innermost_deref(&self) -> Self {
        match self {
            Self::Hole => Self::Hole,
            Self::Proj(pl_ctx, _) => {
                if let Self::Hole = **pl_ctx {
                    panic!("There must an innermost deref context as created by PlaceExpr.to_pl_ctx_and_most_specif_pl.")
                } else {
                    pl_ctx.without_innermost_deref()
                }
            }
            Self::Deref(pl_ctx) => {
                if let Self::Hole = **pl_ctx {
                    Self::Hole
                } else {
                    pl_ctx.without_innermost_deref()
                }
            }
        }
    }
}
