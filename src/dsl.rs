use crate::ast::*;
use crate::nat::*;
use crate::types::*;
use crate::utils::fresh_name;

pub fn lit<T: DescendLiteral>(l: &T) -> ExprNode {
    exprn(l.as_lit())
}

pub trait DescendLiteral {
    fn as_lit(&self) -> Expr;
}

impl DescendLiteral for i32 {
    fn as_lit(&self) -> Expr {
        Expr::Lit(Lit::Integer(*self))
    }
}

impl DescendLiteral for f32 {
    fn as_lit(&self) -> Expr {
        Expr::Lit(Lit::Float(*self))
    }
}

impl DescendLiteral for bool {
    fn as_lit(&self) -> Expr {
        Expr::Lit(Lit::Bool(*self))
    }
}

impl DescendLiteral for () {
    fn as_lit(&self) -> Expr {
        Expr::Lit(Lit::Unit)
    }
}

impl DescendLiteral for String {
    fn as_lit(&self) -> Expr {
        Expr::Lit(Lit::String(self.clone()))
    }
}

pub fn ident(name: &str) -> ExprNode {
    exprn(Expr::Ident(Ident::new(name)))
}

pub fn array(arr: Vec<ExprNode>) {
    exprn(Expr::Array(arr));
}

pub fn at(i: ExprNode, arr: ExprNode) -> ExprNode {
    exprn(Expr::At(Box::new(i), Box::new(arr)))
}

pub fn tuple(t: Vec<ExprNode>) -> ExprNode {
    exprn(Expr::Tuple(t))
}

pub fn r#let(
    id_name: &str,
    ident_type: Ty,
    m: Mutability,
    value: ExprNode,
    r#in: ExprNode,
) -> ExprNode {
    exprn(Expr::Let(
        Ident::new(id_name),
        ident_type,
        m,
        Box::new(value),
        Box::new(r#in),
    ))
}

pub fn assign(lhs: ExprNode, rhs: ExprNode) -> ExprNode {
    exprn(Expr::Assign(Box::new(lhs), Box::new(rhs)))
}

pub fn borr(expr: ExprNode, m: Mutability, l: Lifetime, mem: Memory) -> ExprNode {
    exprn(Expr::Ref(Box::new(expr), m, l, mem))
}

pub fn fun<F: DescendLambda>(exec: ExecLoc, f: F) -> ExprNode {
    let (param_idents, body) = f.as_args_and_body();
    exprn(Expr::Lambda(exec, param_idents, Box::new(body)))
}

pub trait DescendLambda {
    fn as_args_and_body(&self) -> (Vec<Ident>, ExprNode);
}

// TODO look up what dyn stands for
impl DescendLambda for dyn Fn(ExprNode) -> ExprNode {
    fn as_args_and_body(&self) -> (Vec<Ident>, ExprNode) {
        let name = &fresh_name("p");
        let param_ident = ident(name);
        let param_idents = vec![Ident::new(name)];
        let body = self(param_ident);
        (param_idents, body)
    }
}

impl DescendLambda for dyn Fn(ExprNode, ExprNode) -> ExprNode {
    fn as_args_and_body(&self) -> (Vec<Ident>, ExprNode) {
        let (name1, name2) = (&fresh_name("p"), &fresh_name("p"));
        let (param_ident1, param_ident2) = (ident(name1), ident(name2));
        let param_idents = vec![Ident::new(name1), Ident::new(name2)];
        let body = self(param_ident1, param_ident2);
        (param_idents, body)
    }
}

impl DescendLambda for dyn Fn(ExprNode, ExprNode, ExprNode) -> ExprNode {
    fn as_args_and_body(&self) -> (Vec<Ident>, ExprNode) {
        let (name1, name2, name3) = (&fresh_name("p"), &fresh_name("p"), &fresh_name("p"));
        let (param_ident1, param_ident2, param_ident3) = (ident(name1), ident(name2), ident(name3));
        let param_idents = vec![Ident::new(name1), Ident::new(name2), Ident::new(name3)];
        let body = self(param_ident1, param_ident2, param_ident3);
        (param_idents, body)
    }
}

fn exprn(expr: Expr) -> ExprNode {
    ExprNode { expr, ty: None }
}
