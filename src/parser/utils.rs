//! Helper functions for parsing
use crate::ast::{BinOp, BinOpNat, DataTy, DataTyKind, Expr, ExprKind, Lit, Nat, ScalarTy, UnOp};
use bumpalo::Bump;

pub fn type_from_lit<'a>(bump: &'a Bump, lit: &Lit) -> DataTy<'a> {
    DataTy::new(
        bump,
        DataTyKind::Scalar(match lit {
            Lit::Bool(_) => ScalarTy::Bool,
            Lit::Unit => ScalarTy::Unit,
            Lit::I32(_) => ScalarTy::I32,
            Lit::U8(_) => ScalarTy::U8,
            Lit::U32(_) => ScalarTy::U32,
            Lit::U64(_) => ScalarTy::U64,
            Lit::F32(_) => ScalarTy::F32,
            Lit::F64(_) => ScalarTy::F64,
        }),
    )
}

pub fn make_binary<'a>(bump: &'a Bump, op: BinOp, lhs: Expr<'a>, rhs: Expr<'a>) -> Expr<'a> {
    // TODO make operators functions? How do we deal with execution resources?
    // Expr::new(ExprKind::App(
    //     Box::new(Expr::new(ExprKind::PlaceExpr(PlaceExpr::new(
    //         PlaceExprKind::Ident(Ident::new(op.to_string().as_str())),
    //     )))),
    //     vec![],
    //     vec![lhs, rhs],
    // ))
    Expr {
        expr: ExprKind::BinOp(op, bump.alloc(lhs), bump.alloc(rhs)),
        ty: None,
        span: None,
    }
}

pub fn make_binary_nat<'a>(op: BinOpNat, lhs: Nat<'a>, rhs: Nat<'a>) -> Nat<'a> {
    Nat::BinOp(op, Box::new(lhs), Box::new(rhs))
}

pub fn make_unary<'a>(bump: &'a Bump, op: UnOp, rhs: Expr<'a>) -> Expr<'a> {
    // TODO see above
    // Expr::new(ExprKind::App(
    //     Box::new(Expr::new(ExprKind::PlaceExpr(PlaceExpr::new(
    //         PlaceExprKind::Ident(Ident::new(op.to_string().as_str())),
    //     )))),
    //     vec![],
    //     vec![rhs],
    // ))
    Expr {
        expr: ExprKind::UnOp(op, bump.alloc(rhs)),
        ty: None,
        span: None,
    }
}
