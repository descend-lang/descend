use core::fmt;

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub enum Nat {
    Ident(String),
    Lit(usize),
    //    Binary(BinOpNat, Box<Nat>, Box<Nat>),
}

impl Nat {
    pub fn eval(&self) -> usize {
        panic!("not implemented yet")
    }
}

impl fmt::Display for Nat {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let str = match self {
            Self::Ident(ident) => format!("{}", ident),
            Self::Lit(n) => format!("{}", n),
            //Self::Binary(ident) => format!("{}", ident),
        };
        write!(f, "{}", str)
    }
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub enum BinOpNat {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
}
