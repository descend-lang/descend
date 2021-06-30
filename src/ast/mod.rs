pub mod internal;

mod span;
#[macro_use]
pub mod visit;

pub use span::*;
use std::fmt;

use descend_derive::span_derive;
use internal::FrameExpr;
use std::fmt::Formatter;

pub type CompilUnit = Vec<FunDef>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FunDef {
    pub name: String,
    pub generic_params: Vec<IdentKinded>,
    pub params: Vec<ParamDecl>,
    pub ret_dty: DataTy,
    pub exec: Exec,
    pub prv_rels: Vec<PrvRel>,
    pub body_expr: Expr,
}

impl FunDef {
    pub fn ty(&self) -> Ty {
        let param_tys: Vec<_> = self.params.iter().map(|p_decl| p_decl.ty.clone()).collect();
        Ty::Fn(
            self.generic_params.clone(),
            param_tys,
            self.exec,
            Box::new(Ty::Data(self.ret_dty.clone())),
        )
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParamDecl {
    pub ident: Ident,
    pub ty: Ty,
    pub mutbl: Mutability,
}

#[span_derive(PartialEq, Eq)]
#[derive(Debug, Clone)]
pub struct Expr {
    pub expr: ExprKind,
    pub ty: Option<Ty>,
    #[span_derive_ignore]
    pub span: Option<Span>,
}

impl Expr {
    pub fn new(expr: ExprKind) -> Expr {
        Expr {
            expr,
            ty: None,
            span: None,
        }
    }

    pub fn with_span(expr: ExprKind, span: Span) -> Expr {
        Expr {
            expr,
            ty: None,
            span: Some(span),
        }
    }

    pub fn with_type(expr: ExprKind, ty: Ty) -> Expr {
        Expr {
            expr,
            ty: Some(ty),
            span: None,
        }
    }
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.expr)
    }
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub enum ExprKind {
    Lit(Lit),
    // An l-value equivalent: *p, p.n, x
    PlaceExpr(PlaceExpr),
    // Index into array, e.g., arr[i]
    Index(PlaceExpr, Nat),
    // e.g., [1, 2 + 3, 4]
    Array(Vec<Expr>),
    Tuple(Vec<Expr>),
    // Projection, e.g. e.1, for non place expressions, e.g. f(x).1
    Proj(Box<Expr>, usize),
    // Borrow Expressions
    Ref(Provenance, Ownership, PlaceExpr),
    BorrowIndex(Provenance, Ownership, PlaceExpr, Nat),
    LetProv(Vec<String>, Box<Expr>),
    // Variable declaration
    // let mut x: ty;
    LetUninit(Ident, Box<Ty>, Box<Expr>),
    // Variable declaration, assignment and sequencing
    // let w x: ty = e1; e2
    Let(Mutability, Ident, Box<Option<Ty>>, Box<Expr>, Box<Expr>),
    // Assignment to existing place [expression]
    Assign(PlaceExpr, Box<Expr>),
    // e1 ; e2
    Seq(Box<Expr>, Box<Expr>),
    // Anonymous function which can capture its surrounding context
    // | x_n: d_1, ..., x_n: d_n | [exec]-> d_r { e }
    Lambda(Vec<ParamDecl>, Exec, Box<DataTy>, Box<Expr>),
    // Function application
    // e_f(e_1, ..., e_n)
    App(Box<Expr>, Vec<ArgKinded>, Vec<Expr>),
    IfElse(Box<Expr>, Box<Expr>, Box<Expr>),
    // For-each loop.
    // for x in e_1 { e_2 }
    For(Ident, Box<Expr>, Box<Expr>),
    // for n in range(..) { e }
    ForNat(Ident, Nat, Box<Expr>),
    BinOp(BinOp, Box<Expr>, Box<Expr>),
    UnOp(UnOp, Box<Expr>),
    ParFor(Box<Expr>, Box<Expr>, Box<Expr>),
    TupleView(Vec<Expr>),
}

impl fmt::Display for ExprKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Lit(l) => write!(f, "{}", l),
            Self::PlaceExpr(pl_expr) => write!(f, "{}", pl_expr),
            Self::Index(pl_expr, n) => write!(f, "{}[{}]", pl_expr, n),
            Self::Ref(prv, own, pl_expr) => write!(f, "&{} {} {}", prv, own, pl_expr),
            Self::BorrowIndex(prv, own, pl_expr, n) => {
                write!(f, "&{} {} {}[{}]", prv, own, pl_expr, n)
            }
            Self::Assign(pl_expr, e) => write!(f, "{} = {}", pl_expr, e),
            Self::Let(mutab, ident, ty, e1, e2) => {
                if let Some(ty) = ty.as_ref() {
                    write!(f, "let {} {}: {} = {}; {}", mutab, ident, ty, e1, e2)
                } else {
                    write!(f, "let {} {} = {}; {}", mutab, ident, e1, e2)
                }
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

#[span_derive(PartialEq, Eq, Hash)]
#[derive(Debug, Clone)]
pub struct Ident {
    pub name: String,
    #[span_derive_ignore]
    pub span: Option<Span>,
}

impl Ident {
    pub fn new(name: &str) -> Self {
        Self {
            name: String::from(name),
            span: None,
        }
    }

    pub fn with_span(name: String, span: Span) -> Self {
        Self {
            name,
            span: Some(span),
        }
    }
}

impl fmt::Display for Ident {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.name)
    }
}

#[derive(Debug, Copy, Clone, PartialEq)]
pub enum Lit {
    Unit,
    Bool(bool),
    I32(i32),
    F32(f32),
}

// impl PartialEq for Lit{
//     fn eq(&self, other:&Self) -> bool {
//         let b = match (self, other) {
//             (Self::Unit, Self::Unit) => true,
//             (Self::Bool(x), Self::Bool(y)) => if x == y {true} else {false},
//             (Self::Int(x), Self::Int(y)) => if x == y {true} else {false},
//             (Self::Float(x), Self::Float(y)) => if x == y {true} else {false},
//             _ => false
//         };
//         b
//     }
// }

impl Eq for Lit {}

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

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
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

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
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

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
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
}

impl fmt::Display for Kind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let str = match self {
            Kind::Nat => "nat",
            Kind::Memory => "mem",
            Kind::Ty => "type",
            Kind::Provenance => "prv",
        };
        write!(f, "{}", str)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ArgKinded {
    Ident(Ident),
    Nat(Nat),
    Memory(Memory),
    Ty(Ty),
    Provenance(Provenance),
}

impl ArgKinded {
    fn kind(&self) -> Kind {
        use ArgKinded::*;
        match self {
            Ident(_) => panic!("Identifier's kind depends on the kinding context."),
            Nat(_) => Kind::Nat,
            Memory(_) => Kind::Memory,
            Ty(_) => Kind::Ty,
            Provenance(_) => Kind::Provenance,
        }
    }
}

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub enum PlaceExpr {
    Proj(Box<PlaceExpr>, usize),
    Deref(Box<PlaceExpr>),
    Ident(Ident),
}

impl PlaceExpr {
    pub fn is_place(&self) -> bool {
        match self {
            PlaceExpr::Proj(ple, _) => ple.is_place(),
            PlaceExpr::Ident(_) => true,
            PlaceExpr::Deref(_) => false,
        }
    }

    // The inner constructs are prefixes of the outer constructs.
    pub fn prefix_of(&self, other: &Self) -> bool {
        if self != other {
            match other {
                Self::Proj(pl_expr, _) => self.prefix_of(pl_expr),
                Self::Deref(pl_expr) => self.prefix_of(pl_expr),
                Self::Ident(_) => false,
            }
        } else {
            true
        }
    }

    // TODO refactor. Places are only needed during typechecking and codegen
    pub fn to_place(&self) -> Option<Place> {
        if self.is_place() {
            Some(self.to_pl_ctx_and_most_specif_pl().1)
        } else {
            None
        }
    }

    // TODO refactor see to_place
    pub fn to_pl_ctx_and_most_specif_pl(&self) -> (internal::PlaceCtx, Place) {
        match self {
            PlaceExpr::Deref(inner_ple) => {
                let (pl_ctx, pl) = inner_ple.to_pl_ctx_and_most_specif_pl();
                (internal::PlaceCtx::Deref(Box::new(pl_ctx)), pl)
            }
            PlaceExpr::Proj(inner_ple, n) => {
                let (pl_ctx, mut pl) = inner_ple.to_pl_ctx_and_most_specif_pl();
                match pl_ctx {
                    internal::PlaceCtx::Hole => {
                        pl.path.push(*n);
                        (pl_ctx, Place::new(pl.ident, pl.path))
                    }
                    _ => (internal::PlaceCtx::Proj(Box::new(pl_ctx), *n), pl),
                }
            }
            PlaceExpr::Ident(ident) => {
                (internal::PlaceCtx::Hole, Place::new(ident.clone(), vec![]))
            }
        }
    }

    pub fn equiv(&'_ self, place: &'_ Place) -> bool {
        if let (internal::PlaceCtx::Hole, pl) = self.to_pl_ctx_and_most_specif_pl() {
            &pl == place
        } else {
            false
        }
    }
}

impl fmt::Display for PlaceExpr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Proj(pl_expr, n) => write!(f, "{}.{}", pl_expr, n),
            Self::Deref(pl_expr) => write!(f, "*{}", pl_expr),
            Self::Ident(ident) => write!(f, "{}", ident),
        }
    }
}

// TODO refactor find proper location for this
pub type Path = Vec<usize>;
#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub struct Place {
    pub ident: Ident,
    pub path: Path,
}
impl Place {
    pub fn new(ident: Ident, path: Path) -> Self {
        Place { ident, path }
    }

    pub fn to_place_expr(&self) -> PlaceExpr {
        self.path.iter().fold(
            PlaceExpr::Ident(self.ident.clone()),
            |pl_expr, path_entry| PlaceExpr::Proj(Box::new(pl_expr), path_entry.clone()),
        )
    }
}

#[test]
fn test_path_eq() {
    let path1 = vec![Nat::Lit(0)];
    let path2 = vec![Nat::Lit(0)];
    assert!(path1 == path2)
}

#[test]
fn test_place_eq() {
    let pl1 = Place::new(Ident::new("inp"), vec![0]);
    let pl2 = Place::new(Ident::new("inp"), vec![0]);
    assert!(pl1 == pl2)
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub enum Ty {
    Data(DataTy),
    View(ViewTy),
    Fn(Vec<IdentKinded>, Vec<Ty>, Exec, Box<Ty>),
    Ident(Ident),
}

impl Ty {
    pub fn dty(&self) -> &DataTy {
        match self {
            Ty::Data(dty) => dty,
            _ => panic!("Expected data type but found {:?}", self),
        }
    }

    pub fn non_copyable(&self) -> bool {
        match self {
            Ty::Data(dty) => dty.non_copyable(),
            Ty::View(vty) => vty.non_copyable(),
            Ty::Fn(_, _, _, _) => false,
            Ty::Ident(_) => true,
        }
    }

    pub fn copyable(&self) -> bool {
        !self.non_copyable()
    }

    pub fn is_fully_alive(&self) -> bool {
        match self {
            Ty::Data(dty) => dty.is_fully_alive(),
            Ty::View(vty) => vty.is_fully_alive(),
            Ty::Ident(_) | Ty::Fn(_, _, _, _) => true,
        }
    }

    pub fn contains_ref_to_prv(&self, prv_val_name: &str) -> bool {
        match self {
            Ty::Data(dty) => dty.contains_ref_to_prv(prv_val_name),
            Ty::View(vty) => vty.contains_ref_to_prv(prv_val_name),
            Ty::Fn(_, param_tys, _, ret_ty) => {
                param_tys
                    .iter()
                    .any(|param_ty| param_ty.contains_ref_to_prv(prv_val_name))
                    || ret_ty.contains_ref_to_prv(prv_val_name)
            }
            Ty::Ident(_) => false,
        }
    }

    pub fn subst_ident_kinded(&self, ident_kinded: &IdentKinded, with: &ArgKinded) -> Self {
        match self {
            Ty::Data(dty) => Ty::Data(dty.subst_ident_kinded(ident_kinded, with)),
            Ty::View(vty) => Ty::View(vty.subst_ident_kinded(ident_kinded, with)),
            Ty::Fn(gen_params, params, exec, ret) => Ty::Fn(
                gen_params.clone(),
                params
                    .iter()
                    .map(|param| param.subst_ident_kinded(ident_kinded, with))
                    .collect(),
                exec.clone(),
                Box::new(ret.subst_ident_kinded(ident_kinded, with)),
            ),
            Ty::Ident(ident) => {
                if &ident_kinded.ident == ident && ident_kinded.kind == Kind::Ty {
                    match with {
                        ArgKinded::Ident(idk) => Ty::Ident(idk.clone()),
                        ArgKinded::Ty(ty) => ty.clone(),
                        _ => panic!("Trying to substitute type identifier with non-type value."),
                    }
                } else {
                    self.clone()
                }
            }
        }
    }
}

impl fmt::Display for Ty {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Ty::Data(dty) => write!(f, "{}", dty),
            Ty::View(vty) => write!(f, "{}", vty),
            Ty::Ident(ident) => write!(f, "{}", ident),
            Ty::Fn(_, _, _, _) => unimplemented!(),
        }
    }
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub enum ViewTy {
    //    Ident(Ident),
    Array(Box<Ty>, Nat),
    Tuple(Vec<Ty>),
    // Only for type checking purposes.
    Dead(Box<ViewTy>),
}

impl ViewTy {
    pub fn non_copyable(&self) -> bool {
        use ViewTy::*;
        match self {
            //Ident(_) => true,
            Array(ty, _) => ty.non_copyable(),
            Tuple(elem_tys) => elem_tys.iter().any(|ty| ty.non_copyable()),
            Dead(_) => panic!("This case is not expected to mean anything. The type is dead. There is nothign we can do with it."),
        }
    }

    pub fn copyable(&self) -> bool {
        !self.non_copyable()
    }

    pub fn is_fully_alive(&self) -> bool {
        use ViewTy::*;
        match self {
            //Ident(_) |
            Array(_, _) => true,
            Tuple(elem_tys) => elem_tys
                .iter()
                .fold(true, |acc, ty| acc & ty.is_fully_alive()),
            Dead(_) => false,
        }
    }

    pub fn contains_ref_to_prv(&self, prv_val_name: &str) -> bool {
        match self {
            //ViewTy::Ident(_) |
            ViewTy::Dead(_) => false,
            ViewTy::Array(ty, _) => ty.contains_ref_to_prv(prv_val_name),
            ViewTy::Tuple(elem_tys) => elem_tys
                .iter()
                .any(|ty| ty.contains_ref_to_prv(prv_val_name)),
        }
    }

    pub fn subst_ident_kinded(&self, ident_kinded: &IdentKinded, with: &ArgKinded) -> Self {
        use ViewTy::*;
        match self {
            // ViewTy::Ident(id) => {
            //     if &ident_kinded.ident == id && ident_kinded.kind == Kind::Ty {
            //         match with {
            //             ArgKinded::Ident(idk) => Ident(idk.clone()),
            //             ArgKinded::Ty(Ty::View(vty)) => vty.clone(),
            //             _ => panic!("Trying to substitute type identifier with non-type value."),
            //         }
            //     } else {
            //         self.clone()
            //     }
            // }
            Tuple(elem_tys) => Tuple(
                elem_tys
                    .iter()
                    .map(|ty| ty.subst_ident_kinded(ident_kinded, with))
                    .collect(),
            ),
            Array(ty, n) => Array(
                Box::new(ty.subst_ident_kinded(ident_kinded, with)),
                n.subst_ident_kinded(ident_kinded, with),
            ),
            Dead(dty) => dty.subst_ident_kinded(ident_kinded, with),
        }
    }
}

impl fmt::Display for ViewTy {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        unimplemented!()
    }
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub enum DataTy {
    Ident(Ident),
    Scalar(ScalarTy),
    Array(Box<DataTy>, Nat),
    Tuple(Vec<DataTy>),
    At(Box<DataTy>, Memory),
    Ref(Provenance, Ownership, Memory, Box<DataTy>),
    // TODO remove
    GridConfig(Nat, Nat),
    Grid(Box<DataTy>, Vec<Nat>),
    Block(Box<DataTy>, Vec<Nat>),
    // TODO should not be a data type because it contains views?
    DistribBorrow(ViewTy, ViewTy),
    // Only for type checking purposes.
    Dead(Box<DataTy>),
}

impl DataTy {
    pub fn non_copyable(&self) -> bool {
        use DataTy::*;

        match self {
            Scalar(_) => false,
            Ident(_) => true,
            Ref(_, Ownership::Uniq, _, _) => true,
            Ref(_, Ownership::Shrd, _, _) => false,
            At(_, _) => true,
            GridConfig(_, _) => false,
            Grid(_, _) => false,
            Block(_, _) => false,
            DistribBorrow(parall_exec_loc, input) =>
                parall_exec_loc.non_copyable() && input.non_copyable(),
            Tuple(elem_tys) => elem_tys.iter().any(|ty| ty.non_copyable()),
            Array(ty, _) => ty.non_copyable(),
            Dead(_) => panic!("This case is not expected to mean anything. The type is dead. There is nothign we can do with it."),
        }
    }

    pub fn copyable(&self) -> bool {
        !self.non_copyable()
    }

    pub fn is_fully_alive(&self) -> bool {
        use DataTy::*;
        match self {
            Scalar(_)
            | Ident(_)
            | Ref(_, _, _, _)
            | At(_, _)
            | Array(_, _)
            | GridConfig(_, _)
            | Grid(_, _)
            | Block(_, _)
            | DistribBorrow(_, _) => true,
            Tuple(elem_tys) => elem_tys
                .iter()
                .fold(true, |acc, ty| acc & ty.is_fully_alive()),
            Dead(_) => false,
        }
    }

    pub fn contains_ref_to_prv(&self, prv_val_name: &str) -> bool {
        use DataTy::*;
        match self {
            Scalar(_) | Ident(_) | GridConfig(_, _) | Grid(_, _) | Block(_, _) | Dead(_) => false,
            DistribBorrow(parall_exec_loc, data) => {
                parall_exec_loc.contains_ref_to_prv(prv_val_name)
                    || data.contains_ref_to_prv(prv_val_name)
            }
            Ref(prv, _, _, ty) => {
                let found_reference = if let Provenance::Value(prv_val_n) = prv {
                    prv_val_name == prv_val_n
                } else {
                    false
                };
                found_reference || ty.contains_ref_to_prv(prv_val_name)
            }

            At(ty, _) => ty.contains_ref_to_prv(prv_val_name),
            Array(ty, _) => ty.contains_ref_to_prv(prv_val_name),
            Tuple(elem_tys) => elem_tys
                .iter()
                .any(|ty| ty.contains_ref_to_prv(prv_val_name)),
        }
    }

    pub fn subst_ident_kinded(&self, ident_kinded: &IdentKinded, with: &ArgKinded) -> Self {
        use DataTy::*;
        match self {
            Scalar(_) => self.clone(),
            Ident(id) => {
                if &ident_kinded.ident == id && ident_kinded.kind == Kind::Ty {
                    match with {
                        ArgKinded::Ident(idk) => Ident(idk.clone()),
                        ArgKinded::Ty(Ty::Data(dty)) => dty.clone(),
                        _ => {
                            panic!("Trying to substitute data type identifier with non-type value.")
                        }
                    }
                } else {
                    self.clone()
                }
            }
            Ref(prv, own, mem, ty) => Ref(
                prv.subst_ident_kinded(ident_kinded, with),
                *own,
                mem.subst_ident_kinded(ident_kinded, with),
                Box::new(ty.subst_ident_kinded(ident_kinded, with)),
            ),

            At(ty, mem) => At(
                Box::new(ty.subst_ident_kinded(ident_kinded, with)),
                mem.subst_ident_kinded(ident_kinded, with),
            ),
            GridConfig(n1, n2) => GridConfig(
                n1.subst_ident_kinded(ident_kinded, with),
                n2.subst_ident_kinded(ident_kinded, with),
            ),
            Grid(elem, n) => Grid(
                Box::new(elem.subst_ident_kinded(ident_kinded, with)),
                n.iter()
                    .map(|n| n.subst_ident_kinded(ident_kinded, with))
                    .collect(),
            ),
            Block(elem, n) => Block(
                Box::new(elem.subst_ident_kinded(ident_kinded, with)),
                n.iter()
                    .map(|n| n.subst_ident_kinded(ident_kinded, with))
                    .collect(),
            ),
            DistribBorrow(parall_exec_loc, data) => DistribBorrow(
                parall_exec_loc.subst_ident_kinded(ident_kinded, with),
                data.subst_ident_kinded(ident_kinded, with),
            ),
            Tuple(elem_tys) => Tuple(
                elem_tys
                    .iter()
                    .map(|ty| ty.subst_ident_kinded(ident_kinded, with))
                    .collect(),
            ),
            Array(ty, n) => Array(
                Box::new(ty.subst_ident_kinded(ident_kinded, with)),
                n.subst_ident_kinded(ident_kinded, with),
            ),
            Dead(dty) => dty.subst_ident_kinded(ident_kinded, with),
        }
    }
}

impl fmt::Display for DataTy {
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
    Gpu,
    Thread,
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub enum Provenance {
    Value(String),
    Ident(Ident),
}

impl Provenance {
    fn subst_ident_kinded(&self, ident_kinded: &IdentKinded, with: &ArgKinded) -> Self {
        if ident_kinded.kind == Kind::Provenance {
            match self {
                Provenance::Ident(id) if id == &ident_kinded.ident => match with {
                    ArgKinded::Ident(idk) => Provenance::Ident(idk.clone()),
                    ArgKinded::Provenance(prv) => prv.clone(),
                    err => panic!(
                        "Trying to create provenance value from non-provenance `{:?}`",
                        err
                    ),
                },
                _ => self.clone(),
            }
        } else {
            self.clone()
        }
    }
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
    CpuStack,
    GpuGlobal,
    GpuShared,
    GpuLocal,
    None,
    Ident(Ident),
}

impl Memory {
    fn subst_ident_kinded(&self, ident_kinded: &IdentKinded, with: &ArgKinded) -> Memory {
        if ident_kinded.kind == Kind::Memory {
            match self {
                Memory::Ident(id) if id == &ident_kinded.ident => match with {
                    ArgKinded::Ident(kid) => Memory::Ident(kid.clone()),
                    ArgKinded::Memory(m) => m.clone(),
                    err => panic!("Trying to create Memory value from non-memory `{:?}`", err),
                },
                _ => self.clone(),
            }
        } else {
            self.clone()
        }
    }
}

impl fmt::Display for Memory {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Memory::CpuStack => write!(f, "cpu.stack"),
            Memory::CpuHeap => write!(f, "cpu.heap"),
            Memory::GpuGlobal => write!(f, "gpu.global"),
            Memory::GpuShared => write!(f, "gpu.shared"),
            Memory::GpuLocal => write!(f, "gpu.local"),
            Memory::None => write!(f, "none"),
            Memory::Ident(x) => write!(f, "{}", x),
        }
    }
}

#[derive(PartialEq, Eq, Debug, Copy, Clone)]
pub enum Exec {
    CpuThread,
    GpuGrid,
    GpuBlock,
    GpuWarp,
    GpuThread,
    View,
}

impl Exec {
    pub fn callable_in(self, exec: Self) -> bool {
        if self == Exec::View {
            true
        } else {
            self == exec
        }
    }
}

impl fmt::Display for Exec {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Exec::CpuThread => write!(f, "cpu.thread"),
            Exec::GpuGrid => write!(f, "gpu.grid"),
            Exec::GpuBlock => write!(f, "gpu.block"),
            Exec::GpuWarp => write!(f, "gpu.warp"),
            Exec::GpuThread => write!(f, "gpu.thread"),
            Exec::View => write!(f, "view"),
        }
    }
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
#[derive(Eq, Hash, Debug, Clone)]
pub enum Nat {
    Ident(Ident),
    Lit(usize),
    BinOp(BinOpNat, Box<Nat>, Box<Nat>),
    App(Ident, Vec<Nat>),
}

impl Nat {
    pub fn eval(&self) -> Result<usize, String> {
        match self {
            Nat::Ident(i) => Err(format!("Cannot evaluate identifier `{}`.", i)),
            Nat::Lit(n) => Ok(*n),
            Nat::BinOp(op, l, r) => match op {
                BinOpNat::Add => Ok(l.eval()? + r.eval()?),
                BinOpNat::Sub => Ok(l.eval()? - r.eval()?),
                BinOpNat::Mul => Ok(l.eval()? * r.eval()?),
                BinOpNat::Div => Ok(l.eval()? / r.eval()?),
                BinOpNat::Mod => Ok(l.eval()? % r.eval()?),
            },
            Nat::App(fun, args) => unimplemented!(),
        }
    }

    pub fn subst_ident_kinded(&self, ident_kinded: &IdentKinded, with: &ArgKinded) -> Nat {
        if ident_kinded.kind == Kind::Nat {
            match self {
                Nat::Ident(id) if id == &ident_kinded.ident => match with {
                    ArgKinded::Ident(idk) => Nat::Ident(idk.clone()),
                    ArgKinded::Nat(n) => n.clone(),
                    err => panic!("Trying to create nat value from non-nat `{:?}`", err),
                },
                Nat::BinOp(op, n1, n2) => Nat::BinOp(
                    op.clone(),
                    Box::new(n1.subst_ident_kinded(ident_kinded, with)),
                    Box::new(n2.subst_ident_kinded(ident_kinded, with)),
                ),
                _ => self.clone(),
            }
        } else {
            self.clone()
        }
    }
}

impl PartialEq for Nat {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Nat::Lit(l), Nat::Lit(o)) => l == o,
            (Nat::Ident(i), Nat::Ident(o)) => i == o,
            (Nat::BinOp(op, lhs, rhs), Nat::BinOp(oop, olhs, orhs))
                if op == oop && lhs == olhs && rhs == orhs =>
            {
                true
            }
            _ => match (self.eval(), other.eval()) {
                (Ok(n), Ok(o)) => n == o,
                _ => {
                    println!(
                        "WARNING: Not able to check equality of Nats `{}` and `{}`",
                        self, other
                    );
                    true
                }
            },
        }
    }
}

impl fmt::Display for Nat {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Ident(ident) => write!(f, "{}", ident),
            Self::Lit(n) => write!(f, "{}", n),
            Self::BinOp(op, lhs, rhs) => write!(f, "{} {} {}", lhs, op, rhs),
            Self::App(func, args) => write!(f, "{}(...)", func),
        }
    }
}

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub enum BinOpNat {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
}

impl fmt::Display for BinOpNat {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Add => write!(f, "+"),
            Self::Sub => write!(f, "-"),
            Self::Mul => write!(f, "*"),
            Self::Div => write!(f, "/"),
            Self::Mod => write!(f, "%"),
        }
    }
}

#[test]
fn test_ownership_ordering() {
    use Ownership::*;
    assert!(Shrd <= Shrd);
    assert!(Shrd <= Uniq);
    assert!(Uniq <= Uniq);
    assert!(!(Uniq <= Shrd))
}
