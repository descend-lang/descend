pub mod internal;

use std::fmt;

pub type CompilUnit = Vec<GlobalFunDef>;

#[derive(Debug, Clone)]
pub struct GlobalFunDef {
    pub name: String,
    pub generic_params: Vec<IdentKinded>,
    pub params: Vec<ParamDecl>,
    pub ret_ty: Ty,
    pub exec: ExecLoc,
    pub prv_rels: Vec<PrvRel>,
    pub body_expr: Expr,
    pub fun_ty: Ty,
}

#[derive(Debug, Clone)]
pub struct ParamDecl {
    pub ident: Ident,
    pub ty: Ty,
    pub mutbl: Mutability,
}

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
        write!(f, "{}", self.expr)
    }
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub enum ParIndex {
    GroupId,
    ThreadId,
}

#[derive(Debug, Clone)]
pub enum ExprKind {
    // TODO remove GlobalFunIdent
    //  instead? Maybe differentiate between FunctionCall where function is Ident
    //  and Function call where function is expression (so must be lambda)
    //  This is currently wrong, because an global fun ident is not an Expr (has no value).
    //  Or we say it has the value of a function pointer type (like C or Rust) which may be better.
    GlobalFunIdent(String),
    Lit(Lit),
    // An l-value equivalent: *p, p.n, x
    PlaceExpr(PlaceExpr),
    // Index into array, e.g., arr[i]
    Index(PlaceExpr, Nat),
    // Borrow Expressions
    Ref(Provenance, Ownership, PlaceExpr),
    BorrowIndex(Provenance, Ownership, PlaceExpr, Nat),
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
    Lambda(Vec<ParamDecl>, ExecLoc, Ty, Box<Expr>),
    // Function application
    // e_f(e_1, ..., e_n)
    // Todo make this the only apply and use template params
    App(Box<Expr>, Vec<KindedArg>, Vec<Expr>),
    // TODO If
    IfElse(Box<Expr>, Box<Expr>, Box<Expr>),
    // e.g., [1, 2 + 3, 4]
    Array(Vec<Expr>),
    Tuple(Vec<Expr>),
    // For-each loop.
    // for x in e_1 { e_2 }
    For(Ident, Box<Expr>, Box<Expr>),
    // TODO for-each is probably not a good term, at least if we stick to the notion that amount of
    //  elements and amount of threads need to be equal.
    // Parallel for (global) thread with input, syncing at the end.
    // for x in view-expr across parallelism-config-expr { body }
    ParForSync(Ident, Box<Expr>, Box<Expr>, Box<Expr>),
    Binary(BinOp, Box<Expr>, Box<Expr>),
    Unary(UnOp, Box<Expr>),
}

impl fmt::Display for ExprKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Lit(l) => write!(f, "{}", l),
            Self::PlaceExpr(pl_expr) => write!(f, "{}", pl_expr),
            Self::Index(pl_expr, n) => write!(f, "{}[{}]", pl_expr, n),
            // TODO display kind
            Self::Ref(prv, own, pl_expr) => write!(f, "&{} {} {}", prv, own, pl_expr),
            Self::BorrowIndex(prv, own, pl_expr, n) => {
                write!(f, "&{} {} {}[{}]", prv, own, pl_expr, n)
            }
            Self::Assign(pl_expr, e) => write!(f, "{} = {}", pl_expr, e),
            Self::Let(mutab, ident, ty, e1, e2) => {
                write!(f, "let {} {}: {} = {}; {}", mutab, ident, ty, e1, e2)
            }
            Self::Seq(e1, e2) => write!(f, "{}; {}", e1, e2),
            /*            Self::Lambda(params, exec, ty, e) => {
                write!(f, "|{}| [{}]-> {} {{ {} }}", params, exec, ty, e)
            }
            Self::DepLambda(ty_ident, exec, e) => {
                write!(f, "<{}> [{}]-> {{ {} }}", ty_ident, exec, e)
            }
            Self::App(f, arg) => write!(f, "{}({})", f, arg),*/
            _ => panic!("not yet implemented"),
        }
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

#[derive(Debug, Copy, Clone)]
pub enum Lit {
    Unit,
    Bool(bool),
    I32(i32),
    F32(f32),
}

impl fmt::Display for Lit {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Unit => write!(f, "()"),
            Self::Bool(b) => write!(f, "{}", b),
            Self::I32(i) => write!(f, "{}", i),
            Self::F32(fl) => write!(f, "{}", fl),
        }
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

#[derive(PartialEq, Eq, Hash, Debug, Copy, Clone)]
pub enum Kind {
    Nat,
    Memory,
    Ty,
    Provenance,
    Frame,
    Own,
}

impl fmt::Display for Kind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let str = match self {
            Kind::Nat => "nat",
            Kind::Memory => "mem",
            Kind::Ty => "type",
            Kind::Provenance => "prv",
            Kind::Frame => "frm",
            Kind::Own => "own",
        };
        write!(f, "{}", str)
    }
}

#[derive(Debug, Clone)]
pub enum KindedArg {
    // TODO this exists only for the parser?
    //  talk to parser group to figure out how to do this properly
    Ident(Ident),
    Nat(Nat),
    Memory(Memory),
    Ty(Ty),
    Provenance(Provenance),
    // TODO is Frame needed? probably.
    //    Frame(FrameExpr),
    // TODO remove ownership?
    //    Own(Ownership),
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

    pub fn prefix_of(&self, other: &Self) -> bool {
        if self != other {
            match other {
                Self::Proj(pl_expr, _) => self.prefix_of(pl_expr),
                Self::Deref(pl_expr) => self.prefix_of(pl_expr),
                Self::Var(_) => false,
            }
        } else {
            true
        }
    }
}

impl fmt::Display for PlaceExpr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Proj(pl_expr, n) => write!(f, "{}.{}", pl_expr, n),
            Self::Deref(pl_expr) => write!(f, "*{}", pl_expr),
            Self::Var(ident) => write!(f, "{}", ident),
        }
    }
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub enum Ty {
    Scalar(ScalarTy),
    Tuple(Vec<Ty>),
    Array(Box<Ty>, Nat),
    ArrayView(Box<Ty>, Nat),
    At(Box<Ty>, Memory),
    Fn(
        Vec<IdentKinded>,
        Vec<Ty>,
        Box<internal::FrameExpr>,
        ExecLoc,
        Box<Ty>,
    ),
    // TODO better syntactical support for dead and maybe dead types would maybe be safer for prgramming,
    //  but this requires a better understanding of where a type can be dead in order to be done
    //  without too much boilerplate.
    Dead(Box<Ty>),
    Ref(Provenance, Ownership, Memory, Box<Ty>),
    Gpu,
    Ident(Ident),
}

impl Ty {
    pub fn non_copyable(&self) -> bool {
        use Ty::*;
        match self {
            Scalar(_) => false,
            Ident(_) => true,
            Ref(_, Ownership::Uniq, _, _) => true,
            Ref(_, Ownership::Shrd, _, _) => false,
            Fn(_, _, _, _, _) => false,
            At(_, _) => true,
            Tuple(elem_tys) => elem_tys.iter().any(|ty| ty.non_copyable()),
            Array(ty, _) => ty.non_copyable(),
            ArrayView(ty, _) => ty.non_copyable(),
            Gpu => true,
            Dead(_) => panic!("This case is not expected to mean anything. The type is dead. There is nothign we can do with it."),
        }
    }

    pub fn copyable(&self) -> bool {
        !self.non_copyable()
    }

    pub fn is_fully_alive(&self) -> bool {
        use Ty::*;
        match self {
            Scalar(_)
            | Ident(_)
            | Ref(_, _, _, _)
            | Fn(_, _, _, _, _)
            | At(_, _)
            | Array(_, _)
            | ArrayView(_, _)
            | Gpu => true,
            Tuple(elem_tys) => elem_tys
                .iter()
                .fold(true, |acc, ty| acc & ty.is_fully_alive()),
            Dead(_) => false,
        }
    }

    pub fn contains_ref_to_prv(&self, prv_val_name: &str) -> bool {
        use Ty::*;
        match self {
            Scalar(_) | Ident(_) | Gpu | Dead(_) => false,
            Ref(prv, _, _, ty) => {
                let found_reference = if let Provenance::Value(prv_val_n) = prv {
                    prv_val_name == prv_val_n
                } else {
                    false
                };
                found_reference || ty.contains_ref_to_prv(prv_val_name)
            }
            // TODO Probably need to scan frame_expr as well
            Fn(_, param_tys, frame_expr, _, ret_ty) => {
                param_tys
                    .iter()
                    .any(|param_ty| param_ty.contains_ref_to_prv(prv_val_name))
                    || ret_ty.contains_ref_to_prv(prv_val_name)
            }
            At(ty, _) => ty.contains_ref_to_prv(prv_val_name),
            Array(ty, _) => ty.contains_ref_to_prv(prv_val_name),
            ArrayView(ty, _) => ty.contains_ref_to_prv(prv_val_name),
            Tuple(elem_tys) => elem_tys
                .iter()
                .any(|ty| ty.contains_ref_to_prv(prv_val_name)),
        }
    }
}

impl fmt::Display for Ty {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        panic!("not yet implemented")
        //        write!(f, "{}:{}", self.name, self.kind)
    }
}

#[derive(PartialEq, Eq, Debug, Copy, Clone)]
pub enum ScalarTy {
    Unit,
    I32,
    F32,
    Bool,
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub enum Provenance {
    Value(String),
    Ident(Ident),
}

impl fmt::Display for Provenance {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Value(name) => write!(f, "{}", name),
            Self::Ident(ty_ident) => write!(f, "{}", ty_ident),
        }
    }
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub enum Memory {
    CpuHeap,
    GpuGlobal,
    GpuShared,
    Ident(Ident),
    // TODO refactor?
    // only exists for pointers to the stack. Must not be used for At types.
    CpuStack,
}

#[derive(PartialEq, Eq, Debug, Copy, Clone)]
pub enum ExecLoc {
    CpuThread,
    GpuGroup,
    GpuThread,
}

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub struct Loan {
    pub place_expr: PlaceExpr,
    pub own: Ownership,
}

// Provenance Relation: varrho_1:varrho_2
#[derive(PartialEq, Eq, Debug, Clone)]
pub struct PrvRel {
    pub longer: Ident,
    pub shorter: Ident,
}

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub struct IdentKinded {
    pub ident: Ident,
    pub kind: Kind,
}

impl IdentKinded {
    pub fn new(ident: &Ident, kind: Kind) -> Self {
        IdentKinded {
            ident: ident.clone(),
            kind: kind.clone(),
        }
    }
}

// TODO should this really be part of the AST? Nats are also part of the Cuda-AST. Separate module.
#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub enum Nat {
    Ident(Ident),
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
        match self {
            Self::Ident(ident) => write!(f, "{}", ident),
            Self::Lit(n) => write!(f, "{}", n),
            //Self::Binary(ident) => write!(f, "{}", ident),
        }
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

#[test]
fn test_ownership_ordering() {
    use Ownership::*;
    assert!(Shrd <= Shrd);
    assert!(Shrd <= Uniq);
    assert!(Uniq <= Uniq);
    assert!(!(Uniq <= Shrd))
}
