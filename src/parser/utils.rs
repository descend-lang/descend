//! Helper functions for parsing

use crate::ast::{
    BinOp, BinOpNat, DataTy, DataTyKind, Expr, ExprKind, Ident, Lit, Nat, PlaceExpr, PlaceExprKind,
    ScalarTy, UnOp,
};

pub fn type_from_lit(lit: &Lit) -> DataTy {
    DataTy::new(DataTyKind::Scalar(match lit {
        Lit::Bool(_) => ScalarTy::Bool,
        Lit::Unit => ScalarTy::Unit,
        Lit::I32(_) => ScalarTy::I32,
        Lit::U32(_) => ScalarTy::U32,
        Lit::F32(_) => ScalarTy::F32,
    }))
}

pub fn make_binary(op: BinOp, lhs: Expr, rhs: Expr) -> Expr {
    // TODO make operators functions? How do we deal with execution resources?
    // Expr::new(ExprKind::App(
    //     Box::new(Expr::new(ExprKind::PlaceExpr(PlaceExpr::new(
    //         PlaceExprKind::Ident(Ident::new(op.to_string().as_str())),
    //     )))),
    //     vec![],
    //     vec![lhs, rhs],
    // ))
    Expr {
        expr: ExprKind::BinOp(op, Box::new(lhs), Box::new(rhs)),
        ty: None,
        span: None,
    }
}

pub fn make_binary_nat(op: BinOpNat, lhs: Nat, rhs: Nat) -> Nat {
    Nat::BinOp(op, Box::new(lhs), Box::new(rhs))
}

pub fn make_unary(op: UnOp, rhs: Expr) -> Expr {
    // TODO see above
    // Expr::new(ExprKind::App(
    //     Box::new(Expr::new(ExprKind::PlaceExpr(PlaceExpr::new(
    //         PlaceExprKind::Ident(Ident::new(op.to_string().as_str())),
    //     )))),
    //     vec![],
    //     vec![rhs],
    // ))
    Expr {
        expr: ExprKind::UnOp(op, Box::new(rhs)),
        ty: None,
        span: None,
    }
}
