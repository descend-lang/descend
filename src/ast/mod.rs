pub mod nat;
pub mod ty;
pub mod utils;

use nat::*;
use std::fmt;
use ty::*;

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

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", format!("{}", self.expr))
    }
}

pub type Path = Vec<Nat>;
#[derive(PartialEq, Eq, Debug, Clone)]
pub struct Place {
    pub ident: Ident,
    pub path: Path,
}
impl Place {
    pub fn new(ident: Ident, path: Path) -> Self {
        Place { ident, path }
    }

    pub fn prefix_of(&self, other: &Self) -> bool {
        if self.ident == other.ident {
            self.path
                .iter()
                .zip(other.path.iter())
                .all(|(pe, peo)| pe == peo)
        } else {
            false
        }
    }
}
pub type TypedPlace = (Place, Ty);

pub enum PlaceCtx {
    Proj(Box<PlaceCtx>, Nat),
    Deref(Box<PlaceCtx>),
    Hole,
}

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub enum PlaceExpr {
    Proj(Box<PlaceExpr>, Nat),
    Deref(Box<PlaceExpr>),
    Var(Ident),
}

impl PlaceExpr {
    pub fn is_place(&self) -> bool {
        match self {
            PlaceExpr::Proj(ple, _) => ple.is_place(),
            PlaceExpr::Var(_) => true,
            PlaceExpr::Deref(_) => false,
        }
    }

    pub fn to_pl_ctx_and_most_specif_pl(&self) -> (PlaceCtx, Place) {
        match self {
            PlaceExpr::Deref(inner_ple) => {
                let (pl_ctx, pl) = inner_ple.to_pl_ctx_and_most_specif_pl();
                (PlaceCtx::Deref(Box::new(pl_ctx)), pl)
            }
            PlaceExpr::Proj(inner_ple, n) => {
                let (pl_ctx, pl) = inner_ple.to_pl_ctx_and_most_specif_pl();
                match pl_ctx {
                    PlaceCtx::Hole => (pl_ctx, Place::new(pl.ident, vec![n.clone()])),
                    _ => (PlaceCtx::Proj(Box::new(pl_ctx), n.clone()), pl),
                }
            }
            PlaceExpr::Var(ident) => (PlaceCtx::Hole, Place::new(ident.clone(), vec![])),
        }
    }

    pub fn to_place(&self) -> Option<Place> {
        if self.is_place() {
            Some(self.to_pl_ctx_and_most_specif_pl().1)
        } else {
            None
        }
    }

    pub fn equiv(&self, place: &Place) -> bool {
        if let (PlaceCtx::Hole, pl) = self.to_pl_ctx_and_most_specif_pl() {
            &pl == place
        } else {
            false
        }
    }
}

impl fmt::Display for PlaceExpr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let str = match self {
            Self::Proj(pl_expr, n) => format!("{}.{}", pl_expr, n),
            Self::Deref(pl_expr) => format!("{}", pl_expr),
            Self::Var(ident) => format!("{}", ident),
        };
        write!(f, "{}", str)
    }
}

#[derive(Debug, Clone)]
pub enum ExprKind {
    GlobalFunIdent(String),
    Lit(Lit),
    // An l-value equivalent: *p, p.n, x
    PlaceExpr(PlaceExpr),
    // Index into array, e.g., arr[i]
    Index(PlaceExpr, Nat),
    Ref(Provenance, Ownership, PlaceExpr),
    RefIndex(Provenance, Ownership, PlaceExpr, Nat),
    // Assignment to existing place [expression]
    Assign(PlaceExpr, Box<Expr>),
    // Variable declaration, assignment and sequencing
    // let x: ty = e1; e2
    Let(Mutability, Ident, Ty, Box<Expr>, Box<Expr>),
    // e1 ; e2
    Seq(Box<Expr>, Box<Expr>),
    // Anonymous function which can capture its surrounding context
    // | x_n: d_1, ..., x_n: d_n | [exec]-> d_r { e }
    // TODO: Add types for parameters.
    Lambda(Vec<Ident>, ExecLoc, Ty, Box<Expr>),
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

impl fmt::Display for ExprKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let str = match self {
            Self::Lit(l) => format!("{}", l),
            Self::PlaceExpr(pl_expr) => format!("{}", pl_expr),
            Self::Index(pl_expr, n) => format!("{}[{}]", pl_expr, n),
            Self::Ref(prv, own, pl_expr) => format!("&{} {} {}", prv, own, pl_expr),
            Self::RefIndex(prv, own, pl_expr, n) => format!("&{} {} {}[{}]", prv, own, pl_expr, n),
            Self::Assign(pl_expr, e) => format!("{} = {}", pl_expr, e),
            Self::Let(mutab, ident, ty, e1, e2) => {
                format!("let {} {}: {} = {}; {}", mutab, ident, ty, e1, e2)
            }
            Self::Seq(e1, e2) => format!("{}; {}", e1, e2),
            /*            Self::Lambda(params, exec, ty, e) => {
                format!("|{}| [{}]-> {} {{ {} }}", params, exec, ty, e)
            }
            Self::DepLambda(ty_ident, exec, e) => {
                format!("<{}> [{}]-> {{ {} }}", ty_ident, exec, e)
            }
            Self::App(f, arg) => format!("{}({})", f, arg),*/
            _ => panic!("not yet implemented"),
        };
        write!(f, "{}", str)
    }
}

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
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

impl fmt::Display for Ident {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.name)
    }
}

#[derive(Debug, Clone)]
pub enum Lit {
    Unit,
    Bool(bool),
    Int(i32),
    Float(f32),
}

impl fmt::Display for Lit {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let str = match self {
            Self::Unit => String::from("()"),
            Self::Bool(b) => format!("{}", b),
            Self::Int(i) => format!("{}", i),
            Self::Float(f) => format!("{}", f),
        };
        write!(f, "{}", str)
    }
}

#[derive(Debug, Copy, Clone)]
pub enum Mutability {
    Const,
    Mut,
}

impl fmt::Display for Mutability {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let str = match self {
            Self::Const => "const",
            Self::Mut => "mut",
        };
        write!(f, "{}", str)
    }
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Debug, Copy, Clone)]
pub enum Ownership {
    Shrd,
    Uniq,
}

#[test]
fn test_ownership_ordering() {
    use Ownership::*;
    assert!(Shrd <= Shrd);
    assert!(Shrd <= Uniq);
    assert!(Uniq <= Uniq);
    assert!(!(Uniq <= Shrd))
}

impl fmt::Display for Ownership {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let str = match self {
            Self::Shrd => "shrd",
            Self::Uniq => "uniq",
        };
        write!(f, "{}", str)
    }
}

#[derive(Debug, Copy, Clone)]
pub enum UnOp {
    Deref,
    Not,
    Neg,
}

impl fmt::Display for UnOp {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let str = match self {
            Self::Deref => "*",
            Self::Not => "!",
            Self::Neg => "-",
        };
        write!(f, "{}", str)
    }
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

impl fmt::Display for BinOp {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let str = match self {
            Self::Add => "+",
            Self::Sub => "-",
            Self::Mul => "*",
            Self::Div => "/",
            Self::Mod => "%",
            Self::And => "&&",
            Self::Or => "||",
            Self::Eq => "=",
            Self::Lt => "<",
            Self::Le => "<=",
            Self::Gt => ">",
            Self::Ge => ">=",
            Self::Neq => "!=",
        };
        write!(f, "{}", str)
    }
}
