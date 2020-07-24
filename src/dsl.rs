use crate::ast::*;
use crate::nat::*;
use crate::types::CopyData::Scalar;
use crate::types::*;
use crate::utils::fresh_name;

//
// Syntax
//
// Mutability Qualifiers
#[allow(non_upper_case_globals)]
pub static constant: Mutability = Mutability::Const;
#[allow(non_upper_case_globals)]
pub static mutable: Mutability = Mutability::Mut;

// Lifetime
pub fn life(name: &str) -> Lifetime {
    Lifetime::L(String::from(name))
}

pub fn life_id(name: &str) -> Lifetime {
    Lifetime::Ident(Lifetime::new_ident(name))
}

// Identifier
pub fn ident(name: &str, life: &Lifetime) -> Expr {
    exprn(ExprKind::Ident(Ident::new(name, life)))
}

// Compound Expressions
pub fn seq(e1: Expr, e2: Expr) -> Expr {
    exprn(ExprKind::Seq(Box::new(e1), Box::new(e2)))
}

pub fn app(f: Expr, arg: Expr) -> Expr {
    exprn(ExprKind::App(Box::new(f), Box::new(arg)))
}

pub fn ddep_app(f: Expr, dt: &DataTy) -> Expr {
    exprn(ExprKind::DDepApp(Box::new(f), dt.clone()))
}
pub fn ndep_app(f: Expr, nat: &Nat) -> Expr {
    exprn(ExprKind::NDepApp(Box::new(f), nat.clone()))
}
pub fn adep_app(f: Expr, aff: &AffQual) -> Expr {
    exprn(ExprKind::ADepApp(Box::new(f), aff.clone()))
}
pub fn mdep_app(f: Expr, mem: &Memory) -> Expr {
    exprn(ExprKind::MDepApp(Box::new(f), mem.clone()))
}
pub fn fdep_app(f: Expr, fty: &FnTy) -> Expr {
    exprn(ExprKind::FDepApp(Box::new(f), fty.clone()))
}
pub fn ldep_app(f: Expr, l: &Lifetime) -> Expr {
    exprn(ExprKind::LDepApp(Box::new(f), l.clone()))
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

pub fn at(i: Expr, arr: Expr) -> Expr {
    exprn(ExprKind::At(Box::new(i), Box::new(arr)))
}

pub fn r#let(
    m: Mutability,
    id_name: &str,
    life: &Lifetime,
    ident_type: &Ty,
    value: Expr,
    r#in: Expr,
) -> Expr {
    exprn(ExprKind::Let(
        m,
        Ident::new(id_name, life),
        ident_type.clone(),
        Box::new(value),
        Box::new(r#in),
    ))
}

pub fn let_const(id_name: &str, life: &Lifetime, ident_type: &Ty, value: Expr, r#in: Expr) -> Expr {
    r#let(constant, id_name, life, ident_type, value, r#in)
}

pub fn let_mut(id_name: &str, life: &Lifetime, ident_type: &Ty, value: Expr, r#in: Expr) -> Expr {
    r#let(mutable, id_name, life, ident_type, value, r#in)
}

pub fn assign(lhs: Expr, rhs: Expr) -> Expr {
    exprn(ExprKind::Assign(Box::new(lhs), Box::new(rhs)))
}

pub fn borr(m: Mutability, expr: Expr) -> Expr {
    exprn(ExprKind::Ref(m, Box::new(expr)))
}

pub fn fun<F: DescendLambda>(life: &Lifetime, f: F, exec: &ExecLoc) -> Expr {
    let (param_idents, body) = f.as_params_and_body(life);
    exprn(ExprKind::Lambda(param_idents, exec.clone(), Box::new(body)))
}

pub fn dt_fun<F>(df: F, exec: ExecLoc) -> Expr
where
    F: Fn(DataTy) -> Expr,
{
    let ty_id = DataTy::new_ident(&fresh_name("dt"));
    let expr = df(DataTy::Ident(ty_id.clone()));
    exprn(ExprKind::DepLambda(ty_id, exec, Box::new(expr)))
}

pub trait DescendLambda {
    fn as_params_and_body(&self, life: &Lifetime) -> (Vec<Ident>, Expr);
}

impl DescendLambda for dyn Fn(Expr) -> Expr {
    fn as_params_and_body(&self, life: &Lifetime) -> (Vec<Ident>, Expr) {
        let name = &fresh_name("p");
        let param_ident = ident(name, life);
        let param_idents = vec![Ident::new(name, life)];
        let body = self(param_ident);
        (param_idents, body)
    }
}

impl DescendLambda for dyn Fn(Expr, Expr) -> Expr {
    fn as_params_and_body(&self, life: &Lifetime) -> (Vec<Ident>, Expr) {
        let (name1, name2) = (&fresh_name("p"), &fresh_name("p"));
        let (param_ident1, param_ident2) = (ident(name1, life), ident(name2, life));
        let param_idents = vec![Ident::new(name1, life), Ident::new(name2, life)];
        let body = self(param_ident1, param_ident2);
        (param_idents, body)
    }
}

impl DescendLambda for dyn Fn(Expr, Expr, Expr) -> Expr {
    fn as_params_and_body(&self, life: &Lifetime) -> (Vec<Ident>, Expr) {
        let (name1, name2, name3) = (&fresh_name("p"), &fresh_name("p"), &fresh_name("p"));
        let (param_ident1, param_ident2, param_ident3) =
            (ident(name1, life), ident(name2, life), ident(name3, life));
        let param_idents = vec![
            Ident::new(name1, life),
            Ident::new(name2, life),
            Ident::new(name3, life),
        ];
        let body = self(param_ident1, param_ident2, param_ident3);
        (param_idents, body)
    }
}

fn exprn(expr: ExprKind) -> Expr {
    Expr { expr, ty: None }
}

// Literals
#[inline]
pub fn unit() -> Expr {
    tuple!()
}

pub fn lit<T: DescendLiteral>(l: &T) -> Expr {
    exprn(l.as_lit())
}

pub trait DescendLiteral {
    fn as_lit(&self) -> ExprKind;
}

impl DescendLiteral for i32 {
    fn as_lit(&self) -> ExprKind {
        ExprKind::Lit(Lit::Integer(*self))
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

impl DescendLiteral for String {
    fn as_lit(&self) -> ExprKind {
        ExprKind::Lit(Lit::String(self.clone()))
    }
}

//
// Types
//
#[allow(non_upper_case_globals)]
pub static i32: Ty = Ty::Data(DataTy::Un(CopyData::Scalar(ScalarData::I32)));
#[allow(non_upper_case_globals)]
pub static f32: Ty = Ty::Data(DataTy::Un(CopyData::Scalar(ScalarData::F32)));
#[allow(non_upper_case_globals)]
pub static bool: Ty = Ty::Data(DataTy::Un(CopyData::Scalar(ScalarData::Bool)));
#[allow(non_upper_case_globals)]
pub static unit_ty: Ty = Ty::Data(DataTy::Un(CopyData::Scalar(ScalarData::Unit)));

pub fn refc_ty(lf: &Lifetime, mem: Memory, dt: &Ty) -> Ty {
    let dty = extract_dty(dt);
    Ty::Data(DataTy::Un(CopyData::RefConst(
        lf.clone(),
        mem,
        Box::new(dty),
    )))
}

pub fn refm_ty(lf: &Lifetime, mem: Memory, dt: &Ty) -> Ty {
    let dty = extract_dty(dt);
    Ty::Data(DataTy::Aff(MoveData::RefMut(
        lf.clone(),
        mem,
        Box::new(dty),
    )))
}

pub fn arr_ty(size: u32, dt: &Ty) -> Ty {
    let dty = extract_dty(dt);
    Ty::Data(DataTy::Aff(MoveData::Array(Nat::Lit(size), Box::new(dty))))
}

pub fn own_ty(dt: &Ty, mem: Memory) -> Ty {
    let dty = extract_dty(dt);
    Ty::Data(DataTy::Aff(MoveData::Own(Box::new(dty), mem)))
}

pub fn extract_dty(ty: &Ty) -> DataTy {
    match ty {
        Ty::Data(dty) => dty.clone(),
        Ty::QualFnTy(_, _) => {
            panic!("Extracting data type failed. Function type is not a data type.");
        }
    }
}

#[macro_export]
macro_rules! tuple_ty {
    ($($v:expr),*) => {
        $crate::types::Ty::Data(
            $crate::types::DataTy::Aff(
                $crate::types::MoveData::Tuple(
                    vec![$($crate::dsl::extract_dty(& $v)),*]
                )
            )
        )
    }
}

// Affinity Qualifiers
// pub static un: AffQual = AffQual::Un;
// pub static aff: AffQual = AffQual::Aff;

// Data Types
// TODO move data types
#[allow(non_upper_case_globals)]
pub static i32_dt: DataTy = DataTy::Un(Scalar(ScalarData::I32));
#[allow(non_upper_case_globals)]
pub static f32_dt: DataTy = DataTy::Un(Scalar(ScalarData::F32));
#[allow(non_upper_case_globals)]
pub static bool_dt: DataTy = DataTy::Un(Scalar(ScalarData::Bool));
#[allow(non_upper_case_globals)]
pub static unit_dt: DataTy = DataTy::Un(Scalar(ScalarData::Unit));
