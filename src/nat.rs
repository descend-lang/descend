#[derive(Debug, Clone)]
pub enum Nat {
    Ident(String),
    Lit(u32),
    Binary(BinOpNat, Box<Nat>, Box<Nat>),
}

#[derive(Debug, Clone)]
pub enum BinOpNat {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
}
