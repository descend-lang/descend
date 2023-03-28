// Constructs in this module are part of the AST but not part of the user facing syntax.
// These are also used in typechecking and ty_check::ctxs

// TODO specific access modifiers

use super::{Ident, Ownership, PlaceExpr, Ty};
use crate::ast::{ExecExpr, Mutability, Nat, PlaceExprKind, View};
use std::collections::HashSet;

#[derive(Default, Clone, Debug, PartialEq, Eq)]
pub struct Frame {
    pub bindings: Vec<FrameEntry>,
}

impl Frame {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn append_idents_typed(&mut self, idents_typed: Vec<IdentTyped>) -> &mut Frame {
        self.bindings.append(
            &mut idents_typed
                .into_iter()
                .map(FrameEntry::Var)
                .collect::<Vec<_>>(),
        );
        self
    }
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub enum FrameEntry {
    Var(IdentTyped),
    ExecMapping(ExecMapping),
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
pub struct ExecMapping {
    pub ident: Ident,
    pub exec_expr: ExecExpr,
}

impl ExecMapping {
    pub fn new(ident: Ident, exec_expr: ExecExpr) -> Self {
        ExecMapping { ident, exec_expr }
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

    pub fn prefix_of(&self, other: &Self) -> bool {
        if self.path.len() > other.path.len() {
            return false;
        }
        self.ident == other.ident && &self.path == &other.path[..self.path.len()]
    }
}

pub enum PlaceCtx {
    Proj(Box<PlaceCtx>, usize),
    Deref(Box<PlaceCtx>),
    Select(Box<PlaceCtx>, Box<ExecExpr>),
    View(Box<PlaceCtx>, Vec<View>),
    SplitAt(Box<Nat>, Box<PlaceCtx>),
    Idx(Box<PlaceCtx>, Box<Nat>),
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
            Self::SplitAt(split_pos, pl_ctx) => PlaceExpr::new(PlaceExprKind::SplitAt(
                split_pos.clone(),
                Box::new(pl_ctx.insert_pl_expr(pl_expr)),
            )),
            Self::Select(pl_ctx, exec) => PlaceExpr::new(PlaceExprKind::Select(
                Box::new(pl_ctx.insert_pl_expr(pl_expr)),
                exec.clone(),
            )),
            Self::Idx(pl_ctx, idx) => PlaceExpr::new(PlaceExprKind::Idx(
                Box::new(pl_ctx.insert_pl_expr(pl_expr)),
                idx.clone(),
            )),
            Self::View(pl_ctx, view) => PlaceExpr::new(PlaceExprKind::View(
                Box::new(pl_ctx.insert_pl_expr(pl_expr)),
                view.clone(),
            )),
        }
    }

    // Assumes the PlaceCtx HAS an innermost deref, meaning the Hole is wrapped by a Deref.
    // This is always true for PlaceCtxs created by PlaceExpr.to_pl_ctx_and_most_specif_pl
    pub fn without_innermost_deref(&self) -> Self {
        match self {
            PlaceCtx::Hole => PlaceCtx::Hole,
            PlaceCtx::Proj(pl_ctx, i) => {
                if let PlaceCtx::Hole = **pl_ctx {
                    panic!("There must an innermost deref context as created by PlaceExpr.to_pl_ctx_and_most_specif_pl.")
                } else {
                    let inner_ctx = pl_ctx.without_innermost_deref();
                    PlaceCtx::Proj(Box::new(inner_ctx), *i)
                }
            }
            PlaceCtx::Deref(pl_ctx) => {
                if let PlaceCtx::Hole = **pl_ctx {
                    PlaceCtx::Hole
                } else {
                    let inner_ctx = pl_ctx.without_innermost_deref();
                    PlaceCtx::Deref(Box::new(inner_ctx))
                }
            }
            PlaceCtx::SplitAt(split_pos, pl_ctx) => {
                let inner_ctx = pl_ctx.without_innermost_deref();
                PlaceCtx::SplitAt(split_pos.clone(), Box::new(inner_ctx))
            }
            PlaceCtx::Select(pl_ctx, exec_idents) => {
                let inner_ctx = pl_ctx.without_innermost_deref();
                PlaceCtx::Select(Box::new(inner_ctx), exec_idents.clone())
            }
            PlaceCtx::View(pl_ctx, view) => {
                let inner_ctx = pl_ctx.without_innermost_deref();
                PlaceCtx::View(Box::new(inner_ctx), view.clone())
            }

            PlaceCtx::Idx(pl_ctx, idx) => {
                let inner_ctx = pl_ctx.without_innermost_deref();
                PlaceCtx::Idx(Box::new(inner_ctx), idx.clone())
            }
        }
    }
}
