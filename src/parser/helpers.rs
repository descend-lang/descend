//! Helper functions for parsing

use crate::ast::{BinOp, DataTy, Expr, ExprKind, Lit, ScalarTy, UnOp};

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

pub fn make_unary(op: UnOp, rhs: Expr) -> Expr {
    Expr {
        expr: ExprKind::UnOp(op, Box::new(rhs)),
        ty: None,
        span: None,
    }
}

// pub fn make_function_application(func: Expr, kind_args: Option<Vec<ArgKinded>>, args: Vec<Expr>, span: Span) -> Expr {
//     match kind_args {
//         Some(mut kind_args) if !kind_args.is_empty() => {
//             let first_arg = kind_args.remove(0);
//             Expr {
//                 expr: ExprKind::DepApp(Box::new(
//                     make_function_application(func, Some(kind_args), args, span)),
//                     first_arg),
//                 ty: None,
//                 span: Some(span)
//             }
//         }
//         _ => {
//             Expr {
//                 expr: ExprKind::App(Box::new(func), args),
//                 ty: None,
//                 span: Some(span)
//             }
//         }
//     }
// }
