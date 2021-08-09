//! Helper functions for parsing

use crate::ast::{BinOp, BinOpNat, DataTy, Expr, ExprKind, Lit, Nat, ScalarTy, UnOp};

pub fn type_from_lit(lit: &Lit) -> DataTy {
    DataTy::Scalar(match lit {
        Lit::Bool(_) => ScalarTy::Bool,
        Lit::Unit => ScalarTy::Unit,
        Lit::I32(_) => ScalarTy::I32,
        Lit::F32(_) => ScalarTy::F32,
    })
}

pub fn make_binary(op: BinOp, lhs: Expr, rhs: Expr) -> Expr {
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
    Expr {
        expr: ExprKind::UnOp(op, Box::new(rhs)),
        ty: None,
        span: None,
    }
}
