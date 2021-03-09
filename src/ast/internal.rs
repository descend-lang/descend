// Constructs in this module are part of the AST but not part of the user facing syntax.
// These are also used in typechecking and ty_check::ctxs

// TODO specific access modifiers

use super::{Ident, Ownership, PlaceExpr, Ty};
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
