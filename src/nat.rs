pub enum Nat {
    Ident(String),
    Lit(i32),
    Binary(BinOp, Box<Nat>, Box<Nat>),
}

pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
}
