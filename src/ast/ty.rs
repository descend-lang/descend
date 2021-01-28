use crate::ast::*;
use crate::ty_check::ty_ctx::{IdentTyped, TyEntry};
use std::fmt;

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

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum KindedArg {
    Ident(Ident),
    Nat(Nat),
    Memory(Memory),
    Ty(Ty),
    Provenance(Provenance),
    Frame(FrameExpr),
    Own(Ownership),
}

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
        let str = match self {
            Self::Value(name) => name.clone(),
            Self::Ident(ty_ident) => format!("{}", ty_ident),
        };
        write!(f, "{}", str)
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

#[derive(PartialEq, Eq, Debug, Clone)]
pub enum GlobalItem {
    PreDecl(Box<PreDeclaredGlobalFun>),
    Def(Box<GlobalFunDef>),
}

pub trait IntoProgramItem {
    fn into_item(self) -> GlobalItem;
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub struct PreDeclaredGlobalFun {
    pub name: String,
    pub fun_ty: Ty,
}

impl IntoProgramItem for PreDeclaredGlobalFun {
    fn into_item(self) -> GlobalItem {
        GlobalItem::PreDecl(Box::new(self))
    }
}

#[derive(PartialEq, Eq, Debug, Clone)]
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
