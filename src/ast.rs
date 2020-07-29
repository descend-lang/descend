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
pub enum ExprKind {
    // function declaration
    // Identifer, Type parameter, Function parameter, execution location, body
    FunDecl(
        Lifetime,
        Ident,
        Vec<TyIdent>,
        Vec<Expr>,
        ExecLoc,
        Ty,
        Box<Expr>,
    ),
    Ident(Ident),
    Lit(Lit),
    // e.g., [1, 2 + 3, 4]
    Array(Vec<Expr>),
    // Index into array, e.g., arr[i]
    Index(Box<Expr>, Box<Expr>),
    Tuple(Vec<Expr>),
    // Variable declaration and assignment
    Let(Mutability, Ident, Ty, Box<Expr>, Box<Expr>),
    // Assignment to existing variable
    Assign(Box<Expr>, Box<Expr>),
    // Reference to memory underlying Ident
    Ref(Mutability, Box<Expr>),
    // Anonymous function which can capture its surrounding context
    Lambda(Vec<Ident>, ExecLoc, Box<Expr>),
    DepLambda(TyIdent, ExecLoc, Box<Expr>),
    App(Box<Expr>, Box<Expr>),
    DDepApp(Box<Expr>, DataTy),
    NDepApp(Box<Expr>, Nat),
    ADepApp(Box<Expr>, AffQual),
    MDepApp(Box<Expr>, Memory),
    FDepApp(Box<Expr>, FnTy),
    LDepApp(Box<Expr>, Lifetime),
    Unary(UnOp, Box<Expr>),
    Binary(BinOp, Box<Expr>, Box<Expr>),
    IfElse(Box<Expr>, Box<Expr>, Box<Expr>),
    // e1 ; e2
    Seq(Box<Expr>, Box<Expr>),
}

#[derive(Debug, Clone)]
pub struct Ident {
    pub name: String,
    pub life: Lifetime,
}

impl Ident {
    pub fn new(name: &str, life: &Lifetime) -> Ident {
        Ident {
            name: String::from(name),
            life: life.clone(),
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
