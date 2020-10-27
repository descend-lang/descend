use crate::ast::Lit::Unit;
use crate::ast::*;
use crate::nat::*;
use crate::ty::*;
use crate::utils::fresh_name;

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
    Provenance::Ident(Provenance::new_ident(name))
}

// #[allow(non_upper_case_globals)]
// pub static static_l: Provenance = Provenance::Static;

// Variable
pub fn var(name: &str) -> Expr {
    Expr::new(ExprKind::PlaceExpr(PlaceExpr::Var(Ident::new(name))))
}

pub fn deref(pl_expr: Expr) -> Expr {
    Expr::new(ExprKind::PlaceExpr(PlaceExpr::Deref(Box::new(
        expr_to_plexpr(pl_expr),
    ))))
}

// Function Declaration
pub fn fdecl(
    name: &str,
    ty_params: Vec<TyIdent>,
    params: Vec<(&str, &DataTy)>,
    ret_ty: &DataTy,
    frame: &FrameExpr,
    exec: ExecLoc,
    prv_rels: Vec<PrvRel>,
    body: Expr,
) -> GlobalFunDef {
    let f_ty = fn_dty(
        params
            .iter()
            .map(|p: &(&str, &DataTy)| -> DataTy { p.1.clone() })
            .collect(),
        frame.clone(),
        exec.clone(),
        ret_ty,
    );
    let genf_ty = multi_arg_genfn_ty(ty_params.as_slice(), frame, exec, &f_ty);

    GlobalFunDef {
        name: String::from(name),
        ty_idents: ty_params,
        params: param_list(params),
        ret_ty: ret_ty.clone(),
        exec,
        prv_rels,
        body_expr: body,
        fun_ty: genf_ty,
    }
}

// creates a list of identifier expressions; every expression has a set type
fn param_list(params: Vec<(&str, &DataTy)>) -> Vec<(Ident, DataTy)> {
    params
        .into_iter()
        .map(|p: (&str, &DataTy)| -> (Ident, DataTy) { (Ident::new(p.0), p.1.clone()) })
        .collect()
}

// Compound Expressions
pub fn seq(e1: Expr, e2: Expr) -> Expr {
    Expr::new(ExprKind::Seq(Box::new(e1), Box::new(e2)))
}

pub fn app(f: Expr, arg: Vec<Expr>) -> Expr {
    Expr::new(ExprKind::App(Box::new(f), arg))
}

pub fn ddep_app(f: Expr, dt: &DataTy) -> Expr {
    Expr::new(ExprKind::DepApp(Box::new(f), KindValue::Data(dt.clone())))
}
pub fn ndep_app(f: Expr, nat: &Nat) -> Expr {
    Expr::new(ExprKind::DepApp(Box::new(f), KindValue::Nat(nat.clone())))
}
pub fn mdep_app(f: Expr, mem: &Memory) -> Expr {
    Expr::new(ExprKind::DepApp(
        Box::new(f),
        KindValue::Memory(mem.clone()),
    ))
}
pub fn pdep_app(f: Expr, prv: &Provenance) -> Expr {
    Expr::new(ExprKind::DepApp(
        Box::new(f),
        KindValue::Provenance(prv.clone()),
    ))
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
    Expr::new(ExprKind::Binary(op, Box::new(lhs), Box::new(rhs)))
}

// Array constructor
#[macro_export]
macro_rules! arr {
    ($($v:literal),*) => {
        {
             // Hack to test for same types.
             // vec![$($v),*];
             $crate::ast::Expr {
                expr: $crate::ast::ExprKind::Array(
                    vec![$(lit(& $v)),*]
                ),
                ty: None,
            }
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
             $crate::ast::Expr {
                expr: $crate::ast::ExprKind::Tuple(
                    vec![$(lit(& $v)),*]
                ),
                ty: None,
            }
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

pub fn r#let(m: Mutability, id_name: &str, ident_type: &DataTy, value: Expr, body: Expr) -> Expr {
    Expr::new(ExprKind::Let(
        m,
        Ident::new(id_name),
        ident_type.clone(),
        Box::new(value),
        Box::new(body),
    ))
}

pub fn let_const(id_name: &str, ident_type: &DataTy, value: Expr, body: Expr) -> Expr {
    r#let(constant, id_name, ident_type, value, body)
}

pub fn let_mut(id_name: &str, ident_type: &DataTy, value: Expr, body: Expr) -> Expr {
    r#let(mutable, id_name, ident_type, value, body)
}

pub fn assign(lhs: Expr, rhs: Expr) -> Expr {
    let pl_expr = expr_to_plexpr(lhs);
    Expr::new(ExprKind::Assign(pl_expr, Box::new(rhs)))
}

pub fn borr(prv: &Provenance, own: Ownership, expr: Expr) -> Expr {
    Expr::new(match expr.expr {
        ExprKind::Index(pl_expr, idx) => ExprKind::RefIndex(prv.clone(), own, pl_expr, idx),
        ExprKind::PlaceExpr(pl_expr) => ExprKind::Ref(prv.clone(), own, pl_expr),
        _ => panic!("Cannot borrow from this expression: ${:?}", expr.expr),
    })
}

pub fn fun<F: DescendLambda>(f: F, exec: &ExecLoc, ret_ty: &DataTy) -> Expr {
    let (param_idents, body) = f.as_params_and_body();
    Expr::new(ExprKind::Lambda(
        param_idents,
        exec.clone(),
        ret_ty.clone(),
        Box::new(body),
    ))
}

fn expr_to_plexpr(e: Expr) -> PlaceExpr {
    let pl_expr = match e {
        Expr {
            expr: ExprKind::PlaceExpr(pl),
            ..
        } => pl,
        _ => panic!("Not a place expression."),
    };
    pl_expr
}

pub fn dt_fun<F>(df: F, exec: ExecLoc) -> Expr
where
    F: Fn(DataTy) -> Expr,
{
    let ty_id = DataTy::new_ident(&fresh_name("dt"));
    let expr = df(DataTy::Ident(ty_id.clone()));
    Expr::new(ExprKind::DepLambda(ty_id, exec, Box::new(expr)))
}

// TODO: Specify types for parameters.
pub trait DescendLambda {
    fn as_params_and_body(&self) -> (Vec<Ident>, Expr);
}

impl DescendLambda for dyn Fn(Expr) -> Expr {
    fn as_params_and_body(&self) -> (Vec<Ident>, Expr) {
        let name = &fresh_name("p");
        //TODO: Add mutable paramters.
        let param_ident = var(name);
        let param_idents = vec![Ident::new(name)];
        let body = self(param_ident);
        (param_idents, body)
    }
}

impl DescendLambda for dyn Fn(Expr, Expr) -> Expr {
    fn as_params_and_body(&self) -> (Vec<Ident>, Expr) {
        let (name1, name2) = (&fresh_name("p"), &fresh_name("p"));
        let (param_ident1, param_ident2) = (var(name1), var(name2));
        let param_idents = vec![Ident::new(name1), Ident::new(name2)];
        let body = self(param_ident1, param_ident2);
        (param_idents, body)
    }
}

impl DescendLambda for dyn Fn(Expr, Expr, Expr) -> Expr {
    fn as_params_and_body(&self) -> (Vec<Ident>, Expr) {
        let (name1, name2, name3) = (&fresh_name("p"), &fresh_name("p"), &fresh_name("p"));
        let (param_ident1, param_ident2, param_ident3) = (var(name1), var(name2), var(name3));
        let param_idents = vec![Ident::new(name1), Ident::new(name2), Ident::new(name3)];
        let body = self(param_ident1, param_ident2, param_ident3);
        (param_idents, body)
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
        ExprKind::Lit(Lit::Int(*self))
    }
}

impl DescendLiteral for f32 {
    fn as_lit(&self) -> ExprKind {
        ExprKind::Lit(Lit::Float(*self))
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

pub fn dt_ident(name: &str) -> TyIdent {
    DataTy::new_ident(name)
}

pub fn prov_ident(name: &str) -> TyIdent {
    Provenance::new_ident(name)
}

pub fn ref_dty(prv: &Provenance, own: Ownership, mem: &Memory, dt: &DataTy) -> DataTy {
    DataTy::Ref(prv.clone(), own, mem.clone(), Box::new(dt.clone()))
}

pub fn arr_dty(size: usize, dt: &DataTy) -> DataTy {
    DataTy::Array(Nat::Lit(size), Box::new(dt.clone()))
}

pub fn at_dty(dt: &DataTy, mem: &Memory) -> DataTy {
    DataTy::At(Box::new(dt.clone()), mem.clone())
}

//
// pub fn extract_dty(ty: &Ty) -> DataTy {
//     match ty {
//         Ty::Data(dty) => dty.clone(),
//         Ty::QualFnTy(_, _) => {
//             panic!("Extracting data type failed. Function type is not a data type.");
//         }
//     }
// }

#[macro_export]
macro_rules! tuple_dty {
    ($($v:expr),*) => {
        $crate::ty::DataTy::Tuple(
            vec![$($v.clone()),*]
        )
    }
}

pub fn fn_dty(
    param_tys: Vec<DataTy>,
    frame_expr: FrameExpr,
    exec: ExecLoc,
    ret_ty: &DataTy,
) -> DataTy {
    DataTy::Fn(
        param_tys,
        Box::new(frame_expr),
        exec,
        Box::new(ret_ty.clone()),
    )
}

pub fn genfn_dty(param: &TyIdent, frame: &FrameExpr, exec: ExecLoc, ret_ty: &DataTy) -> DataTy {
    DataTy::GenFn(
        param.clone(),
        Box::new(frame.clone()),
        exec,
        Box::new(ret_ty.clone()),
    )
}

pub fn multi_arg_genfn_ty(
    params: &[TyIdent],
    frame: &FrameExpr,
    exec: ExecLoc,
    ret_ty: &DataTy,
) -> DataTy {
    match params.split_first() {
        None => {
            panic!("To create a generic function type, at least one parameter must be provided")
        }
        Some((head, &[])) => genfn_dty(head, frame, exec, ret_ty),
        Some((head, tail)) => genfn_dty(
            head,
            frame,
            exec,
            &multi_arg_genfn_ty(tail, frame, exec, ret_ty),
        ),
    }
}

//
// Types
//
#[allow(non_upper_case_globals)]
pub static i32_ty: Ty = Ty::Data(DataTy::Scalar(ScalarData::I32));
#[allow(non_upper_case_globals)]
pub static f32_ty: Ty = Ty::Data(DataTy::Scalar(ScalarData::F32));
#[allow(non_upper_case_globals)]
pub static bool_ty: Ty = Ty::Data(DataTy::Scalar(ScalarData::Bool));
#[allow(non_upper_case_globals)]
pub static unit_ty: Ty = Ty::Data(DataTy::Scalar(ScalarData::Unit));

// Data Types
#[allow(non_upper_case_globals)]
pub static i32: DataTy = DataTy::Scalar(ScalarData::I32);
#[allow(non_upper_case_globals)]
pub static f32: DataTy = DataTy::Scalar(ScalarData::F32);
#[allow(non_upper_case_globals)]
pub static bool: DataTy = DataTy::Scalar(ScalarData::Bool);
#[allow(non_upper_case_globals)]
pub static unit_dty: DataTy = DataTy::Scalar(ScalarData::Unit);
