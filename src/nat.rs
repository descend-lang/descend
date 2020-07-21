#[derive(Debug, Clone)]
pub enum Nat {
    Ident(String),
    Lit(u32),
    Binary(BinOp, Box<Nat>, Box<Nat>),
}

#[derive(Debug, Clone)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
}
