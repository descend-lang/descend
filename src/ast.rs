use super::nat::*;
use super::types::*;

#[derive(Debug, Clone)]
pub struct Expr {
    pub expr: ExprKind,
    pub ty: Option<Ty>,
}

impl Expr {
    pub fn typed_expr(expr: ExprKind, ty: &Ty) -> Expr {
        Expr {
            expr,
            ty: Some(ty.clone()),
        }
    }

    pub fn new(expr: ExprKind) -> Expr {
        Expr { expr, ty: None }
    }
}

#[derive(Debug, Clone)]
pub enum PlaceExpr {
    Proj(Box<PlaceExpr>, Nat),
    Deref(Box<PlaceExpr>),
    Var(Ident),
}

#[derive(Debug, Clone)]
pub enum Place {
    Proj(Box<Place>, Nat),
    Var(Ident),
}

pub enum PlaceContext {
    Proj(Box<PlaceContext>, Nat),
    Deref(Box<PlaceContext>),
    Hole,
}

impl PlaceExpr {
    pub fn is_place(&self) -> bool {
        match self {
            PlaceExpr::Proj(ple, _) => ple.is_place(),
            PlaceExpr::Var(_) => true,
            PlaceExpr::Deref(_) => false,
        }
    }

    pub fn to_place_context_and_largest_place(&self) -> (PlaceContext, Place) {
        match self {
            PlaceExpr::Deref(inner_ple) => {
                let (pl_ctx, pl) = inner_ple.to_place_context_and_largest_place();
                (PlaceContext::Deref(Box::new(pl_ctx)), pl)
            }
            PlaceExpr::Proj(inner_ple, n) => {
                let (pl_ctx, pl) = inner_ple.to_place_context_and_largest_place();
                match pl_ctx {
                    PlaceContext::Hole => (pl_ctx, Place::Proj(Box::new(pl), n.clone())),
                    _ => (PlaceContext::Proj(Box::new(pl_ctx), n.clone()), pl),
                }
            }
            PlaceExpr::Var(ident) => (PlaceContext::Hole, Place::Var(ident.clone())),
        }
    }
}

#[derive(Debug, Clone)]
pub enum ExprKind {
    Lit(Lit),
    // An l-value equivalent: *p, p.n, x
    PlaceExpr(PlaceExpr),
    // Index into array, e.g., arr[i]
    Index(PlaceExpr, Nat),
    Ref(Provenance, Ownership, PlaceExpr),
    RefIndex(Provenance, Ownership, PlaceExpr, Nat),
    // Assignment to existing place [expression]
    Assign(PlaceExpr, Box<Expr>),
    // Variable declaration and assignment
    Let(Mutability, Ident, DataTy, Box<Expr>, Box<Expr>),
    // e1 ; e2
    Seq(Box<Expr>, Box<Expr>),
    // Anonymous function which can capture its surrounding context
    // | x_n: d_1, ..., x_n: d_n | [exec]-> d_r { e }
    // TODO: Add types for parameters.
    Lambda(Vec<Ident>, ExecLoc, DataTy, Box<Expr>),
    // A function that accepts something of the specified kind as an argument.
    // (x : kind) [exec]-> { e }
    DepLambda(TyIdent, ExecLoc, Box<Expr>),
    // Function application
    // e_f(e_1, ..., e_n)
    App(Box<Expr>, Vec<Expr>),
    DepApp(Box<Expr>, KindValue),
    IfElse(Box<Expr>, Box<Expr>, Box<Expr>),
    // e.g., [1, 2 + 3, 4]
    Array(Vec<Expr>),
    Tuple(Vec<Expr>),
    // For-each loop.
    // for x in e_1 { e_2 }
    For(Ident, Box<Expr>, Box<Expr>),
    Binary(BinOp, Box<Expr>, Box<Expr>),
    Unary(UnOp, Box<Expr>),
}

#[derive(Debug, Clone)]
pub struct Ident {
    pub name: String,
}

impl Ident {
    pub fn new(name: &str) -> Ident {
        Ident {
            name: String::from(name),
        }
    }
}

#[derive(Debug, Clone)]
pub enum Lit {
    Unit,
    Bool(bool),
    Integer(i32),
    Float(f32),
    String(String),
}

#[derive(Debug, Copy, Clone)]
pub enum Mutability {
    Mut,
    Const,
}

#[derive(Debug, Copy, Clone)]
pub enum Ownership {
    Shrd,
    Uniq,
}

#[derive(Debug, Copy, Clone)]
pub enum UnOp {
    Deref,
    Not,
    Neg,
}

#[derive(Debug, Copy, Clone)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    And,
    Or,
    Eq,
    Lt,
    Le,
    Gt,
    Ge,
    Neq,
}
