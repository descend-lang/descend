use crate::ast::Lit::Unit;
use crate::ast::*;

//
// Syntax
//
// Mutability Qualifiers
#[allow(non_upper_case_globals)]
pub static constant: Mutability = Mutability::Const;
#[allow(non_upper_case_globals)]
pub static mutable: Mutability = Mutability::Mut;

// Provenance
pub fn prv(name: &str) -> Provenance {
    Provenance::Value(String::from(name))
}

pub fn prv_id(name: &str) -> Provenance {
    Provenance::Ident(Ident::new(name))
}

// #[allow(non_upper_case_globals)]
// pub static static_l: Provenance = Provenance::Static;

// Nat

pub fn nat_id(name: &str) -> Nat {
    Nat::Ident(Ident::new(name))
}

// Variable
pub fn ident(name: &str) -> Expr {
    Expr::new(ExprKind::PlaceExpr(PlaceExpr::Ident(Ident::new(name))))
}

pub fn fun_name(name: &str) -> Expr {
    Expr::new(ExprKind::FunIdent(Ident::new(name)))
}

pub fn deref(pl_expr: Expr) -> Expr {
    Expr::new(ExprKind::PlaceExpr(PlaceExpr::Deref(Box::new(
        expr_to_plexpr(pl_expr),
    ))))
}

// Function Declaration
pub fn fdef(
    name: &str,
    generic_params: Vec<(&str, Kind)>,
    params: Vec<(Mutability, &str, &Ty)>,
    ret_ty: &DataTy,
    exec: Exec,
    prv_rels: Vec<PrvRel>,
    body: Expr,
) -> FunDef {
    let generic_idents: Vec<_> = generic_params
        .iter()
        .map(|(name, kind)| IdentKinded::new(&Ident::new(name), *kind))
        .collect();

    FunDef {
        name: String::from(name),
        generic_params: generic_idents,
        params: param_list(params),
        ret_dty: ret_ty.clone(),
        exec,
        prv_rels,
        body_expr: body,
    }
}

// creates a list of identifier expressions; every expression has a set type and
// mutability qualifier
fn param_list(params: Vec<(Mutability, &str, &Ty)>) -> Vec<ParamDecl> {
    params
        .into_iter()
        .map(|(mutbl, ident_name, ty)| ParamDecl {
            ident: Ident::new(ident_name),
            ty: ty.clone(),
            mutbl,
        })
        .collect()
}

// Compound Expressions
pub fn seq(e1: Expr, e2: Expr) -> Expr {
    Expr::new(ExprKind::Seq(Box::new(e1), Box::new(e2)))
}

pub fn app(f: Expr, args: Vec<Expr>) -> Expr {
    dep_app(f, vec![], args)
}

pub fn dep_app(f: Expr, kinded_args: Vec<ArgKinded>, args: Vec<Expr>) -> Expr {
    Expr::new(ExprKind::App(Box::new(f), kinded_args, args))
}

pub fn add(lhs: Expr, rhs: Expr) -> Expr {
    bin_op(BinOp::Add, lhs, rhs)
}
pub fn sub(lhs: Expr, rhs: Expr) -> Expr {
    bin_op(BinOp::Sub, lhs, rhs)
}
pub fn mul(lhs: Expr, rhs: Expr) -> Expr {
    bin_op(BinOp::Mul, lhs, rhs)
}
pub fn div(lhs: Expr, rhs: Expr) -> Expr {
    bin_op(BinOp::Div, lhs, rhs)
}
pub fn bin_op(op: BinOp, lhs: Expr, rhs: Expr) -> Expr {
    Expr::new(ExprKind::BinOp(op, Box::new(lhs), Box::new(rhs)))
}

// Array constructor
#[macro_export]
macro_rules! arr {
    ($($v:literal),*) => {
        {
            // Hack to test for same types.
            // vec![$($v),*];
            $crate::ast::Expr::new(
                $crate::ast::ExprKind::Array(
                    vec![$(lit(& $v)),*]
                )
            )
        }
    };
    ($($v:expr),*) => {
        $crate::ast::Expr {
            expr: $crate::ast::ExprKind::Array(
                vec![$($v),*]
            ),
            ty: None,
        }
    }
}

// Tuple constructor
#[macro_export]
macro_rules! tuple {
    ($) => {
         {
             $crate::ast::Expr {
                expr: $crate::ast::ExprKind::Tuple(
                    vec![]
                ),
                ty: None,
            }
        }
    };
    ($($v:literal),*) => {
        {
            $crate::ast::Expr::new(
                $crate::ast::ExprKind::Tuple(
                    vec![$(lit(& $v)),*]
                )
            )
        }
    };
    ($($v:expr),*) => {
        $crate::ast::Expr {
            expr: $crate::ast::ExprKind::Tuple(
                vec![$($v),*]
            ),
            ty: None,
        }
    }
}

pub fn index(arr: Expr, i: Nat) -> Expr {
    let pl_expr = expr_to_plexpr(arr);
    Expr::new(ExprKind::Index(pl_expr, i))
}

// TODO let with optional type declaration
pub fn r#let(m: Mutability, id_name: &str, ident_ty: &Ty, value: Expr, body: Expr) -> Expr {
    Expr::new(ExprKind::Let(
        m,
        Ident::new(id_name),
        Some(ident_ty.clone()),
        Box::new(value),
        Box::new(body),
    ))
}

pub fn let_const(id_name: &str, ident_ty: &Ty, value: Expr, body: Expr) -> Expr {
    r#let(constant, id_name, ident_ty, value, body)
}

pub fn let_mut(id_name: &str, ident_ty: &Ty, value: Expr, body: Expr) -> Expr {
    r#let(mutable, id_name, ident_ty, value, body)
}

pub fn assign(lhs: Expr, rhs: Expr) -> Expr {
    let pl_expr = expr_to_plexpr(lhs);
    Expr::new(ExprKind::Assign(pl_expr, Box::new(rhs)))
}

pub fn borr(prv: &Provenance, own: Ownership, expr: Expr) -> Expr {
    Expr::new(match expr.expr {
        ExprKind::Index(pl_expr, idx) => ExprKind::BorrowIndex(prv.clone(), own, pl_expr, idx),
        ExprKind::PlaceExpr(pl_expr) => ExprKind::Ref(prv.clone(), own, pl_expr),
        _ => panic!("Cannot borrow from this expression: ${:?}", expr.expr),
    })
}

fn expr_to_plexpr(e: Expr) -> PlaceExpr {
    match e {
        Expr {
            expr: ExprKind::PlaceExpr(pl),
            ..
        } => pl,
        _ => panic!("Not a place expression."),
    }
}

// Literals
#[inline]
pub fn unit() -> Expr {
    Expr::new(ExprKind::Lit(Unit))
}

pub fn lit<T: DescendLiteral>(l: &T) -> Expr {
    Expr::new(l.as_lit())
}

pub trait DescendLiteral {
    fn as_lit(&self) -> ExprKind;
}

impl DescendLiteral for i32 {
    fn as_lit(&self) -> ExprKind {
        ExprKind::Lit(Lit::I32(*self))
    }
}

impl DescendLiteral for f32 {
    fn as_lit(&self) -> ExprKind {
        ExprKind::Lit(Lit::F32(*self))
    }
}

impl DescendLiteral for bool {
    fn as_lit(&self) -> ExprKind {
        ExprKind::Lit(Lit::Bool(*self))
    }
}

impl DescendLiteral for () {
    fn as_lit(&self) -> ExprKind {
        ExprKind::Lit(Lit::Unit)
    }
}

pub fn prov_ident(name: &str) -> IdentKinded {
    IdentKinded::new(&Ident::new(name), Kind::Provenance)
}

pub fn ref_ty(prv: &Provenance, own: Ownership, mem: &Memory, dt: &DataTy) -> DataTy {
    DataTy::Ref(prv.clone(), own, mem.clone(), Box::new(dt.clone()))
}

pub fn arr_ty(size: Nat, ty: &DataTy) -> DataTy {
    DataTy::Array(Box::new(ty.clone()), size)
}

pub fn at_ty(ty: &DataTy, mem: &Memory) -> DataTy {
    DataTy::At(Box::new(ty.clone()), mem.clone())
}

//
// pub fn extract_ty(ty: &Ty) -> DataTy {
//     match ty {
//         Ty::Data(ty) => ty.clone(),
//         Ty::QualFnTy(_, _) => {
//             panic!("Extracting data type failed. Function type is not a data type.");
//         }
//     }
// }

#[macro_export]
macro_rules! tuple_ty {
    ($($v:expr),*) => {
        $crate::ast::Ty::Tuple(
            vec![$($v.clone()),*]
        )
    }
}

pub fn fun_ty(
    generic_param: Vec<IdentKinded>,
    param_tys: Vec<Ty>,
    frame_expr: &internal::FrameExpr,
    exec: Exec,
    ret_ty: &Ty,
) -> DataTy {
    DataTy::Fn(
        generic_param,
        param_tys,
        Box::new(frame_expr.clone()),
        exec,
        Box::new(ret_ty.clone()),
    )
}

// Scalar Types
#[allow(non_upper_case_globals)]
pub static i32: DataTy = DataTy::Scalar(ScalarTy::I32);
#[allow(non_upper_case_globals)]
pub static f32: DataTy = DataTy::Scalar(ScalarTy::F32);
#[allow(non_upper_case_globals)]
pub static bool: DataTy = DataTy::Scalar(ScalarTy::Bool);
#[allow(non_upper_case_globals)]
pub static unit_ty: DataTy = DataTy::Scalar(ScalarTy::Unit);
