//! Helper functions for parsing

use crate::ast::{BinOp, Expr, ExprKind, Lit, UnOp, ty::{ScalarData, Ty, KindedArg}};

pub fn type_from_lit(lit: &Lit) -> Ty {
    Ty::Scalar(match lit {
        Lit::Bool(_) => ScalarData::Bool,
        Lit::Unit => ScalarData::Unit,
        Lit::Int(_) => ScalarData::I32,
        Lit::Float(_) => ScalarData::F32
    })
}

pub fn make_binary(op:BinOp, lhs: Expr, rhs:Expr) -> Expr {
    Expr {
        expr: ExprKind::Binary(op, Box::new(lhs), Box::new(rhs)),
        ty: None,   /*match op {
            BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div => if let (Some(left_type), Some(right_type)) = (lhs.ty, rhs.ty) {
                if left_type == right_type {
                    Some(left_type)
                } else {None}
            } else {None},
            BinOp::Mod => Some(Ty::Scalar(ScalarData::I32)),
            BinOp::And | BinOp::Or | BinOp::Eq | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge | BinOp::Neq  => Some(Ty::Scalar(ScalarData::Bool)),
        }*/
        // tried to insert expression_Ty from the lhs and rhs of the operation
    }
}

pub fn make_unary(op:UnOp, rhs:Expr) -> Expr {
    Expr {
        expr: ExprKind::Unary(op, Box::new(rhs)),
        ty: None
    }
}

pub fn make_function_application(func: Expr, kind_args: Option<Vec<KindedArg>>, args: Vec<Expr>) -> Expr {
    match kind_args {
        Some(mut kind_args) if !kind_args.is_empty() => {
            let first_arg = kind_args.remove(0);
            Expr {
                expr: ExprKind::DepApp(Box::new(
                    make_function_application(func, Some(kind_args), args)),
                    first_arg),
                ty: None
            }
        }
        _ => {
            Expr {
                expr: ExprKind::App(Box::new(func), args),
                ty: None
            }
        }
    }
}