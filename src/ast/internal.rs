// Constructs in this module are part of the AST but not part of the user facing syntax.

use crate::ast::Ident;
use crate::ty_check::ctxs::{IdentTyped, TyEntry};

// TODO do provenance relations have to be part of the frame typing?
pub type FrameTyping = Vec<TyEntry>;

pub fn append_idents_typed(frm: &FrameTyping, idents_typed: Vec<IdentTyped>) -> FrameTyping {
    let mut new_frm = frm.clone();
    new_frm.append(
        &mut idents_typed
            .into_iter()
            .map(TyEntry::Var)
            .collect::<Vec<_>>(),
    );
    new_frm
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub enum FrameExpr {
    FrTy(FrameTyping),
    Ident(Ident),
}
