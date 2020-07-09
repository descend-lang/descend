use super::types::*;

pub struct ExprNode {
    pub expr: Expr,
    pub ty: Option<Ty>,
}

pub enum Expr {
    Ident(Ident),
    Lit(Lit),
    // e.g., [1, 2 + 3, 4]
    Array(Vec<ExprNode>),
    // Index into array, e.g., arr[i]
    At(Box<ExprNode>, Box<ExprNode>),
    Tuple(Vec<ExprNode>),
    // Variable declaration and assignment
    Let(Ident, Ty, Mutability, Box<ExprNode>, Box<ExprNode>),
    // Assignment to existing variable
    Assign(Box<ExprNode>, Box<ExprNode>),
    // Reference to memory underlying Ident
    Ref(Box<ExprNode>, Mutability, Lifetime, Memory),
    // Anonymous function which can capture its surrounding context
    Lambda(ExecLoc, Vec<Ident>, Box<ExprNode>),
    App(Box<ExprNode>, Box<ExprNode>),
    Unary(UnOp, Box<ExprNode>),
    Binary(BinOp, Box<ExprNode>),
    IfElse(Box<ExprNode>, Box<ExprNode>, Box<ExprNode>),
}

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

pub enum Lit {
    Unit,
    Bool(bool),
    Integer(i32),
    Float(f32),
    String(String),
}

pub enum Mutability {
    Mut,
    Const,
}

pub enum UnOp {
    Deref,
    Not,
    Neg,
}

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
