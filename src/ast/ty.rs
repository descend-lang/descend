use crate::ast::nat::Nat;
use crate::ast::*;
use crate::ty_check::ty_ctx::{IdentTyped, TyEntry};
use std::fmt;

#[derive(PartialEq, Eq, Debug, Copy, Clone)]
pub enum Kind {
    Nat,
    Memory,
    Ty,
    Provenance,
    Frame,
}

impl fmt::Display for Kind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let str = match self {
            Kind::Nat => "nat",
            Kind::Memory => "mem",
            Kind::Ty => "type",
            Kind::Provenance => "prv",
            Kind::Frame => "frm",
        };
        write!(f, "{}", str)
    }
}

#[derive(Debug, Clone)]
pub enum KindValue {
    Nat(Nat),
    Memory(Memory),
    Data(Ty),
    Provenance(Provenance),
    Frame(FrameExpr),
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
    Ident(TyIdent),
}

impl Kinded for FrameExpr {
    fn get_kind(&self) -> Kind {
        Kind::Frame
    }

    fn new_ident(name: &str) -> TyIdent {
        TyIdent {
            name: String::from(name),
            kind: Kind::Frame,
        }
    }
}

#[derive(PartialEq, Eq, Debug, Clone)]
// A type identifier is uniquely identified by its name (every name has exactly one kind)
pub struct TyIdent {
    pub name: String,
    kind: Kind,
}

impl TyIdent {
    pub fn kind(&self) -> Kind {
        self.kind
    }
}

impl fmt::Display for TyIdent {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}", self.name, self.kind)
    }
}

pub trait Kinded {
    fn get_kind(&self) -> Kind;
    fn new_ident(name: &str) -> TyIdent;
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
    Ident(TyIdent),
}

impl Kinded for Provenance {
    fn get_kind(&self) -> Kind {
        Kind::Provenance
    }

    fn new_ident(name: &str) -> TyIdent {
        TyIdent {
            name: String::from(name),
            kind: Kind::Provenance,
        }
    }
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
    Ident(TyIdent),
}

impl Kinded for Memory {
    fn get_kind(&self) -> Kind {
        Kind::Memory
    }

    fn new_ident(name: &str) -> TyIdent {
        TyIdent {
            name: String::from(name),
            kind: Kind::Memory,
        }
    }
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
    pub own_qual: Ownership,
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub enum Ty {
    Scalar(ScalarData),
    Tuple(Vec<Ty>),
    Array(Nat, Box<Ty>),
    At(Box<Ty>, Memory),
    Ref(Provenance, Ownership, Memory, Box<Ty>),
    Fn(Vec<Ty>, Box<FrameExpr>, ExecLoc, Box<Ty>),
    DepFn(TyIdent, Box<FrameExpr>, ExecLoc, Box<Ty>),
    Ident(TyIdent),
    Dead(Box<Ty>),
}

impl Ty {
    pub fn non_copyable(&self) -> bool {
        use Ty::*;
        match self {
            Scalar(sc) => false,
            Ident(_) => true,
            Ref(_, Ownership::Uniq, _, _) => true,
            Ref(_, Ownership::Shrd, _, _) => false,
            Fn(_, _, _, _) => false,
            DepFn(_, _, _, _) => false,
            At(_, _) => true,
            Tuple(elem_tys) => elem_tys.iter().any(|ty| ty.non_copyable()),
            Array(_, ty) => ty.non_copyable(),
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
            | Array(_, _) => true,
            Tuple(elem_tys) => elem_tys
                .iter()
                .fold(true, |acc, ty| acc & ty.is_fully_alive()),
            Dead(_) => false,
        }
    }
}

impl Kinded for Ty {
    fn get_kind(&self) -> Kind {
        Kind::Ty
    }

    fn new_ident(name: &str) -> TyIdent {
        TyIdent {
            name: String::from(name),
            kind: Kind::Ty,
        }
    }
}

impl fmt::Display for Ty {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        panic!("not yet implemented")
        //        write!(f, "{}:{}", self.name, self.kind)
    }
}

// TODO: make sure TyIdent can only be of kind Provenance
// Provenance Relation: varrho_1:varrho_2
pub type PrvRel = (TyIdent, TyIdent);

#[derive(PartialEq, Eq, Debug, Clone)]
pub enum KindingCtxEntry {
    Ident(TyIdent),
    PrvRel(PrvRel),
}
// impl KindingCtxEntry {
//     fn is_prv_rel(entry: &KindingCtxEntry) -> bool {
//         match entry {
//             KindingCtxEntry::PrvRel(_) => true,
//             KindingCtxEntry::Ident(_) => false,
//         }
//     }
//
//     // fn is_ty_ident(&self) -> bool {
//     //     match self {
//     //         KindingCtxEntry::Ident(_) => true,
//     //         KindingCtxEntry::ProvRel(_) => false,
//     //     }
//     // }
// }

pub struct KindCtx {
    vec: Vec<KindingCtxEntry>,
}
impl KindCtx {
    pub fn new() -> Self {
        KindCtx { vec: Vec::new() }
    }

    pub fn append_ty_idents(mut self, ty_idents: Vec<TyIdent>) -> Self {
        let mut entries: Vec<_> = ty_idents
            .into_iter()
            .map(|tyi| KindingCtxEntry::Ident(tyi))
            .collect();
        self.vec.append(&mut entries);

        self
    }

    pub fn append_prv_rels(mut self, prv_rels: &Vec<PrvRel>) -> Self {
        for prv_rel in prv_rels {
            self.vec.push(KindingCtxEntry::PrvRel(prv_rel.clone()));
        }
        KindCtx { vec: self.vec }
    }

    pub fn get_ty_idents(&self, kind: Kind) -> Vec<TyIdent> {
        self.vec
            .iter()
            .filter_map(|entry| {
                if let KindingCtxEntry::Ident(ty_ident) = entry {
                    if ty_ident.kind == kind {
                        Some(ty_ident.clone())
                    } else {
                        None
                    }
                } else {
                    None
                }
            })
            .collect()
    }

    pub fn ident_of_kind_exists(&self, ident_name: &TyIdent, kind: Kind) -> bool {
        self.get_ty_idents(kind).iter().any(|id| ident_name == id)
    }

    pub fn outlives(&self, long: &TyIdent, short: &TyIdent) -> Result<(), String> {
        use KindingCtxEntry::PrvRel;

        if self.vec.iter().any(|entry| match entry {
            PrvRel((l, s)) => l == long && s == short,
            _ => false,
        }) {
            Ok(())
        } else {
            Err(format!("{} is not defined as outliving {}.", long, short))
        }
    }
}

#[derive(Debug, Clone)]
pub struct GlobalFunDef {
    pub name: String,
    pub ty_idents: Vec<TyIdent>,
    pub params: Vec<IdentTyped>,
    pub ret_ty: Ty,
    pub exec: ExecLoc,
    pub prv_rels: Vec<PrvRel>,
    pub body_expr: Expr,
    pub fun_ty: Ty,
}

pub type GlobalCtx = Vec<GlobalFunDef>;
