pub mod utils;

use crate::ty_check::ty_ctx::TyEntry;
use std::fmt;

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

pub type Path = Vec<Nat>;
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
        self.path
            .iter()
            .fold(PlaceExpr::Var(self.ident.clone()), |pl_expr, path_entry| {
                PlaceExpr::Proj(Box::new(pl_expr), path_entry.clone())
            })
    }
}
pub type TypedPlace = (Place, Ty);

pub enum PlaceCtx {
    Proj(Box<PlaceCtx>, Nat),
    Deref(Box<PlaceCtx>),
    Hole,
}

impl PlaceCtx {
    pub fn insert_pl_expr(&self, pl_expr: PlaceExpr) -> PlaceExpr {
        match self {
            Self::Hole => pl_expr,
            Self::Proj(pl_ctx, n) => {
                PlaceExpr::Proj(Box::new(pl_ctx.insert_pl_expr(pl_expr)), n.clone())
            }
            Self::Deref(pl_ctx) => PlaceExpr::Deref(Box::new(pl_ctx.insert_pl_expr(pl_expr))),
        }
    }

    // Assumes the PlaceCtx HAS an innermost deref, meaning the Hole is wrapped by a Deref.
    // This is always true for PlaceCtxs created by PlaceExpr.to_pl_ctx_and_most_specif_pl
    pub fn without_innermost_deref(&self) -> Self {
        match self {
            Self::Hole => Self::Hole,
            Self::Proj(pl_ctx, _) => {
                if let Self::Hole = **pl_ctx {
                    panic!("There must an innermost deref context as created by PlaceExpr.to_pl_ctx_and_most_specif_pl.")
                } else {
                    pl_ctx.without_innermost_deref()
                }
            }
            Self::Deref(pl_ctx) => {
                if let Self::Hole = **pl_ctx {
                    Self::Hole
                } else {
                    pl_ctx.without_innermost_deref()
                }
            }
        }
    }
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

    pub fn equiv(&'_ self, place: &'_ Place) -> bool {
        if let (PlaceCtx::Hole, pl) = self.to_pl_ctx_and_most_specif_pl() {
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
            Self::Var(ident) => write!(f, "{}", ident),
        }
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
    Lambda(Vec<Ident>, ExecLoc, Ty, Box<Expr>),
    // A function that accepts something of the specified kind as an argument.
    // (x : kind) [exec]-> { e }
    DepLambda(IdentKinded, ExecLoc, Box<Expr>),
    // Function application
    // e_f(e_1, ..., e_n)
    // Todo make this the only apply and use template params
    App(Box<Expr>, Vec<Expr>),
    DepApp(Box<Expr>, KindedArg),
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
    Ident(Ident),
    Nat(Nat),
    Memory(Memory),
    Ty(Ty),
    Provenance(Provenance),
    Frame(FrameExpr),
    Own(Ownership),
}

// TODO move this to type checking because it is not part of user facing syntax and is only needed
//  during type checking
pub type FrameTyping = Vec<TyEntry>;

pub fn append_idents_typed(frm: &FrameTyping, idents_typed: Vec<IdentTyped>) -> FrameTyping {
    let mut new_frm = frm.clone();
    new_frm.append(
        &mut idents_typed
            .into_iter()
            .map(TyEntry::Var)
            .collect::<Vec<_>>(),
    );
    new_frm
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub enum FrameExpr {
    FrTy(FrameTyping),
    Ident(Ident),
}

#[derive(PartialEq, Eq, Debug, Copy, Clone)]
pub enum ScalarData {
    I32,
    F32,
    Bool,
    Unit,
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
    CpuStack,
    CpuHeap,
    GpuGlobal,
    GpuShared,
    Ident(Ident),
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

#[derive(PartialEq, Eq, Debug, Clone)]
pub enum Ty {
    Scalar(ScalarData),
    Tuple(Vec<Ty>),
    Array(Box<Ty>, Nat),
    ArrayView(Box<Ty>, Nat),
    At(Box<Ty>, Memory),
    Fn(Vec<Ty>, Box<FrameExpr>, ExecLoc, Box<Ty>),
    DepFn(IdentKinded, Box<FrameExpr>, ExecLoc, Box<Ty>),
    Ident(Ident),
    // TODO better syntactical support for dead and maybe dead types would maybe be safer for prgramming,
    //  but this requires a better understanding of where a type can be dead in order to be done
    //  without too much boilerplate.
    Dead(Box<Ty>),
    Ref(Provenance, Ownership, Memory, Box<Ty>),
    GPU,
}

impl Ty {
    pub fn non_copyable(&self) -> bool {
        use Ty::*;
        match self {
            Scalar(_) => false,
            Ident(_) => true,
            Ref(_, Ownership::Uniq, _, _) => true,
            Ref(_, Ownership::Shrd, _, _) => false,
            Fn(_, _, _, _) => false,
            DepFn(_, _, _, _) => false,
            At(_, _) => true,
            Tuple(elem_tys) => elem_tys.iter().any(|ty| ty.non_copyable()),
            Array(ty, _) => ty.non_copyable(),
            ArrayView(ty, _) => ty.non_copyable(),
            GPU => true,
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
            | Fn(_, _, _, _)
            | DepFn(_, _, _, _)
            | At(_, _)
            | Array(_, _)
            | ArrayView(_, _)
            | GPU => true,
            Tuple(elem_tys) => elem_tys
                .iter()
                .fold(true, |acc, ty| acc & ty.is_fully_alive()),
            Dead(_) => false,
        }
    }

    pub fn contains_ref_to_prv(&self, prv_val_name: &str) -> bool {
        use Ty::*;
        match self {
            Scalar(_) | Ident(_) | GPU | Dead(_) => false,
            Ref(prv, _, _, ty) => {
                let found_reference = if let Provenance::Value(prv_val_n) = prv {
                    prv_val_name == prv_val_n
                } else {
                    false
                };
                found_reference || ty.contains_ref_to_prv(prv_val_name)
            }
            // TODO Probably need to scan frame_expr as well
            Fn(param_tys, frame_expr, _, ret_ty) => {
                param_tys
                    .iter()
                    .any(|param_ty| param_ty.contains_ref_to_prv(prv_val_name))
                    || ret_ty.contains_ref_to_prv(prv_val_name)
            }
            DepFn(_, frame_expr, _, ret_ty) => ret_ty.contains_ref_to_prv(prv_val_name),
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

// Provenance Relation: varrho_1:varrho_2
#[derive(PartialEq, Eq, Debug, Clone)]
pub struct PrvRel {
    longer: Ident,
    shorter: Ident,
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

#[derive(PartialEq, Eq, Debug, Clone)]
pub enum KindingCtxEntry {
    Ident(IdentKinded),
    PrvRel(PrvRel),
}

pub struct KindCtx {
    vec: Vec<KindingCtxEntry>,
}

impl KindCtx {
    pub fn new() -> Self {
        KindCtx { vec: Vec::new() }
    }

    pub fn from(idents: Vec<IdentKinded>, prv_rels: Vec<PrvRel>) -> Result<Self, String> {
        let kind_ctx: Self = Self::new().append_idents(idents);
        kind_ctx.well_kinded_prv_rels(&prv_rels)?;
        Ok(kind_ctx.append_prv_rels(prv_rels))
    }

    pub fn append_idents(mut self, idents: Vec<IdentKinded>) -> Self {
        let mut entries: Vec<_> = idents.into_iter().map(KindingCtxEntry::Ident).collect();
        self.vec.append(&mut entries);
        self
    }

    pub fn append_prv_rels(mut self, prv_rels: Vec<PrvRel>) -> Self {
        for prv_rel in prv_rels {
            self.vec.push(KindingCtxEntry::PrvRel(prv_rel));
        }
        self
    }

    pub fn get_idents(&self, kind: Kind) -> impl Iterator<Item = &Ident> {
        self.vec.iter().filter_map(move |entry| {
            if let KindingCtxEntry::Ident(IdentKinded { ident, kind: k }) = entry {
                if k == &kind {
                    Some(ident)
                } else {
                    None
                }
            } else {
                None
            }
        })
    }

    pub fn get_kind(&self, ident: &Ident) -> Result<&Kind, String> {
        let res = self.vec.iter().find_map(|entry| {
            if let KindingCtxEntry::Ident(IdentKinded { ident: id, kind }) = entry {
                if id == ident {
                    Some(kind)
                } else {
                    None
                }
            } else {
                None
            }
        });
        if let Some(kind) = res {
            Ok(kind)
        } else {
            Err(format!(
                "Cannot find identifier {} in kinding context",
                ident
            ))
        }
    }

    pub fn ident_of_kind_exists(&self, ident: &Ident, kind: Kind) -> bool {
        self.get_idents(kind).any(|id| ident == id)
    }

    pub fn well_kinded_prv_rels(&self, prv_rels: &[PrvRel]) -> Result<(), String> {
        let mut prv_idents = self.get_idents(Kind::Provenance);
        for prv_rel in prv_rels {
            if !prv_idents.any(|prv_ident| &prv_rel.longer == prv_ident) {
                return Err(format!("{} is not declared", prv_rel.longer));
            }
            if !prv_idents.any(|prv_ident| &prv_rel.shorter == prv_ident) {
                return Err(format!("{} is not declared", prv_rel.shorter));
            }
        }
        Ok(())
    }

    pub fn outlives(&self, l: &Ident, s: &Ident) -> Result<(), String> {
        if self.vec.iter().any(|entry| match entry {
            KindingCtxEntry::PrvRel(PrvRel { longer, shorter }) => longer == l && shorter == s,
            _ => false,
        }) {
            Ok(())
        } else {
            Err(format!("{} is not defined as outliving {}.", l, s))
        }
    }
}

#[derive(Debug, Clone)]
pub enum GlobalItem {
    PreDecl(Box<PreDeclaredGlobalFun>),
    Def(Box<GlobalFunDef>),
}

pub trait IntoProgramItem {
    fn into_item(self) -> GlobalItem;
}

#[derive(Debug, Clone)]
pub struct PreDeclaredGlobalFun {
    pub name: String,
    pub fun_ty: Ty,
}

impl IntoProgramItem for PreDeclaredGlobalFun {
    fn into_item(self) -> GlobalItem {
        GlobalItem::PreDecl(Box::new(self))
    }
}

#[derive(Debug, Clone)]
pub struct GlobalFunDef {
    pub name: String,
    pub ty_idents: Vec<IdentKinded>,
    pub params: Vec<IdentTyped>,
    pub ret_ty: Ty,
    pub exec: ExecLoc,
    pub prv_rels: Vec<PrvRel>,
    pub body_expr: Expr,
    pub fun_ty: Ty,
}

impl IntoProgramItem for GlobalFunDef {
    fn into_item(self) -> GlobalItem {
        GlobalItem::Def(Box::new(self))
    }
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub struct IdentTyped {
    pub ident: Ident,
    pub ty: Ty,
}

impl IdentTyped {
    pub fn new(ident: Ident, ty: Ty) -> Self {
        IdentTyped { ident, ty }
    }
}

#[derive(Debug, Clone)]
pub struct GlobalCtx {
    items: Vec<GlobalItem>,
}

impl GlobalCtx {
    pub fn new() -> Self {
        GlobalCtx { items: vec![] }
    }

    pub fn append_items<T, I>(mut self, new_items: I) -> Self
    where
        T: IntoProgramItem,
        I: IntoIterator<Item = T>,
    {
        self.items
            .extend(new_items.into_iter().map(IntoProgramItem::into_item));
        self
    }

    pub fn fun_defs_mut(&mut self) -> impl Iterator<Item = &mut GlobalFunDef> {
        self.items.iter_mut().filter_map(|item| match item {
            GlobalItem::PreDecl(_) => None,
            GlobalItem::Def(gl_fun_def) => Some(gl_fun_def.as_mut()),
        })
    }

    pub fn fun_defs(&self) -> impl Iterator<Item = &GlobalFunDef> {
        self.items.iter().filter_map(|item| match item {
            GlobalItem::PreDecl(_) => None,
            GlobalItem::Def(gl_fun_def) => Some(gl_fun_def.as_ref()),
        })
    }

    // pub fn pre_declared_funs(&self) -> impl Iterator<Item = &PreDeclaredGlobalFun> {
    //     panic!("todo")
    // }

    pub fn fun_ty_by_name(&self, name: &str) -> Result<&Ty, String> {
        let fun = self.items.iter().find(|item| match item {
            GlobalItem::PreDecl(fun_decl) => fun_decl.name == name,
            // TODO
            GlobalItem::Def(fun_def) => false,
        });
        match fun {
            Some(GlobalItem::PreDecl(fun_decl)) => Ok(&fun_decl.fun_ty),
            Some(GlobalItem::Def(fun_def)) => Ok(&fun_def.fun_ty),
            None => Err(format!(
                "Function `{}` does not exist in global environment.",
                name
            )),
        }
    }
}

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
