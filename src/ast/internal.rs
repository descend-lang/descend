// Constructs in this module are part of the AST but not part of the user facing syntax.
// These are also used in typechecking and ty_check::ctxs

// TODO specific access modifiers

use super::{Ident, Ownership, PlaceExpr, Ty};
use crate::ast::{ExecExpr, Mutability, Nat, PlaceExprKind, View};
use bumpalo::collections::Vec as BumpVec;
use std::collections::HashSet;

// TODO: Removed the Default trait here, see what kind of consequences has this later
// Otherwise implement the trait
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Frame<'a> {
    pub bindings: BumpVec<'a, FrameEntry<'a>>,
}

impl<'a> Frame<'a> {
    pub fn new_in(bump: &'a bumpalo::Bump) -> Self {
        Self {
            bindings: BumpVec::new_in(bump),
        }
    }

    pub fn append_idents_typed<I>(&mut self, idents_typed: I)
    where
        I: IntoIterator<Item = IdentTyped<'a>>,
    {
        for ident in idents_typed {
            self.bindings.push(FrameEntry::Var(ident));
        }
    }
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub enum FrameEntry<'a> {
    Var(IdentTyped<'a>),
    ExecMapping(ExecMapping<'a>),
    PrvMapping(PrvMapping<'a>),
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub struct IdentTyped<'a> {
    pub ident: Ident<'a>,
    pub ty: Ty<'a>,
    pub mutbl: Mutability,
    pub exec: ExecExpr<'a>,
}

impl<'a> IdentTyped<'a> {
    pub fn new_in(
        arena: &'a bumpalo::Bump,
        ident: &'a str,
        ty: Ty<'a>,
        mutbl: Mutability,
        exec: ExecExpr<'a>,
    ) -> Self {
        IdentTyped {
            ident: Ident::new(arena, ident),
            ty,
            mutbl,
            exec,
        }
    }
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub struct ExecMapping<'a> {
    pub ident: Ident<'a>,
    pub exec_expr: ExecExpr<'a>,
}

impl<'a> ExecMapping<'a> {
    pub fn new(ident: Ident<'a>, exec_expr: ExecExpr<'a>) -> Self {
        ExecMapping { ident, exec_expr }
    }
}

// TODO: Problems with HashSet and String in the Arena implementation --> Find a work
#[derive(PartialEq, Eq, Debug, Clone)]
pub struct PrvMapping<'a> {
    pub prv: String,
    pub loans: HashSet<Loan<'a>>,
}

impl<'a> PrvMapping<'a> {
    pub fn new(name: &str) -> Self {
        PrvMapping {
            prv: name.to_string(),
            loans: HashSet::new(),
        }
    }
}

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub struct Loan<'a> {
    pub place_expr: PlaceExpr<'a>,
    pub own: Ownership,
}

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub enum PathElem<'a> {
    Proj(usize),
    FieldProj(&'a Ident<'a>),
}
pub type Path<'a> = BumpVec<'a, PathElem<'a>>;

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub struct Place<'a> {
    pub ident: Ident<'a>,
    pub path: Path<'a>,
}
impl<'a> Place<'a> {
    pub fn new(ident: Ident<'a>, path: Path<'a>) -> Self {
        Place { ident, path }
    }

    pub fn to_place_expr(&self, arena: &'a bumpalo::Bump) -> PlaceExpr {
        self.path.iter().fold(
            PlaceExpr::new(PlaceExprKind::Ident(self.ident.clone())),
            |pl_expr, path_entry| match path_entry {
                PathElem::Proj(n) => PlaceExpr::new(PlaceExprKind::Proj(arena.alloc(pl_expr), *n)),
                PathElem::FieldProj(field) => {
                    PlaceExpr::new(PlaceExprKind::FieldProj(arena.alloc(pl_expr), field))
                }
            },
        )
    }

    /**
    pub fn prefix_of(&self, other: &Self) -> bool {
        if self.path.len() > other.path.len() {
            return false;
        }
        self.ident == other.ident && &self.path == &other.path[..self.path.len()]
    }*/

    pub fn prefix_of(&self, other: &Self) -> bool {
        if self.ident != other.ident || self.path.len() > other.path.len() {
            return false;
        }

        other.path.iter().zip(&self.path).all(|(a, b)| a == b)
    }
}

pub enum PlaceCtx<'a> {
    Proj(&'a PlaceCtx<'a>, usize),
    FieldProj(&'a PlaceCtx<'a>, Ident<'a>),
    Deref(&'a PlaceCtx<'a>),
    Select(&'a PlaceCtx<'a>, &'a ExecExpr<'a>),
    View(&'a PlaceCtx<'a>, &'a View<'a>),
    Idx(&'a PlaceCtx<'a>, &'a Nat<'a>),
    Hole,
}

impl<'a> PlaceCtx<'a> {
    pub fn insert_pl_expr(
        &'a self,
        arena: &'a bumpalo::Bump,
        pl_expr: PlaceExpr<'a>,
    ) -> PlaceExpr<'a> {
        match self {
            Self::Hole => pl_expr,
            Self::Proj(pl_ctx, n) => PlaceExpr::new(PlaceExprKind::Proj(
                arena.alloc(pl_ctx.insert_pl_expr(arena, pl_expr)),
                *n,
            )),
            Self::FieldProj(pl_ctx, field) => PlaceExpr::new(PlaceExprKind::FieldProj(
                arena.alloc(pl_ctx.insert_pl_expr(arena, pl_expr)),
                field,
            )),
            Self::Deref(pl_ctx) => PlaceExpr::new(PlaceExprKind::Deref(
                arena.alloc(pl_ctx.insert_pl_expr(arena, pl_expr)),
            )),
            Self::Select(pl_ctx, exec) => PlaceExpr::new(PlaceExprKind::Select(
                arena.alloc(pl_ctx.insert_pl_expr(arena, pl_expr)),
                exec.clone(),
            )),
            Self::View(pl_ctx, view) => PlaceExpr::new(PlaceExprKind::View(
                arena.alloc(pl_ctx.insert_pl_expr(arena, pl_expr)),
                view.clone(),
            )),
            Self::Idx(pl_ctx, idx) => PlaceExpr::new(PlaceExprKind::Idx(
                arena.alloc(pl_ctx.insert_pl_expr(arena, pl_expr)),
                idx.clone(),
            )),
        }
    }

    pub fn without_innermost_deref(&'a self, arena: &'a bumpalo::Bump) -> &'a PlaceCtx<'a> {
        match self {
            PlaceCtx::Hole => self,
            PlaceCtx::Proj(pl_ctx, idx) => {
                arena.alloc(PlaceCtx::Proj(pl_ctx.without_innermost_deref(arena), *idx))
            }
            PlaceCtx::FieldProj(pl_ctx, ident) => arena.alloc(PlaceCtx::FieldProj(
                pl_ctx.without_innermost_deref(arena),
                ident.clone(),
            )),
            PlaceCtx::Deref(pl_ctx) => match **pl_ctx {
                PlaceCtx::Hole => arena.alloc(PlaceCtx::Hole),
                _ => arena.alloc(PlaceCtx::Deref(pl_ctx.without_innermost_deref(arena))),
            },
            PlaceCtx::Select(pl_ctx, exec) => arena.alloc(PlaceCtx::Select(
                pl_ctx.without_innermost_deref(arena),
                exec.clone(),
            )),
            PlaceCtx::View(pl_ctx, view) => arena.alloc(PlaceCtx::View(
                pl_ctx.without_innermost_deref(arena),
                view.clone(),
            )),
            PlaceCtx::Idx(pl_ctx, idx) => arena.alloc(PlaceCtx::Idx(
                pl_ctx.without_innermost_deref(arena),
                idx.clone(),
            )),
        }
    }
}
