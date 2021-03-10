// Constructs in this module are part of the AST but not part of the user facing syntax.
// These are also used in typechecking and ty_check::ctxs

// TODO specific access modifiers

use super::{Ident, Nat, Ownership, PlaceExpr, Ty};
use std::collections::HashSet;

#[derive(PartialEq, Eq, Debug, Clone)]
pub enum FrameExpr {
    FrTy(FrameTyping),
    Ident(Ident),
    Empty,
}

pub type FrameTyping = Vec<FrameEntry>;
pub fn append_idents_typed(frm: &FrameTyping, idents_typed: Vec<IdentTyped>) -> FrameTyping {
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
}

impl IdentTyped {
    pub fn new(ident: Ident, ty: Ty) -> Self {
        IdentTyped { ident, ty }
    }
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub struct PrvMapping {
    pub prv: String,
    pub loans: HashSet<Loan>,
}

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub struct Loan {
    pub place_expr: PlaceExpr,
    pub own: Ownership,
}

pub enum PlaceCtx {
    Proj(Box<PlaceCtx>, Nat),
    Deref(Box<PlaceCtx>),
    Hole,
}

impl PlaceCtx {
    pub fn insert_pl_expr(&self, pl_expr: PlaceExpr) -> PlaceExpr {
        match self {
            Self::Hole => pl_expr,
            Self::Proj(pl_ctx, n) => {
                PlaceExpr::Proj(Box::new(pl_ctx.insert_pl_expr(pl_expr)), n.clone())
            }
            Self::Deref(pl_ctx) => PlaceExpr::Deref(Box::new(pl_ctx.insert_pl_expr(pl_expr))),
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
