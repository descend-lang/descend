use super::nat::Nat;
use crate::ast::{Expr, Ident, Ownership, PlaceExpr};
use std::fmt;

#[derive(PartialEq, Eq, Debug, Copy, Clone)]
pub enum Kind {
    Nat,
    Memory,
    Data,
    Provenance,
    Frame,
}

impl fmt::Display for Kind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let str = match self {
            Kind::Nat => "nat",
            Kind::Memory => "mem",
            Kind::Data => "data",
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
    Data(DataTy),
    Provenance(Provenance),
    Frame(FrameExpr),
}

#[derive(PartialEq, Eq, Debug, Clone)]
// A type identifier is uniquely identified by its name (every name has exactly one kind)
pub struct TyIdent {
    pub name: String,
    pub kind: Kind,
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
    Static,
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

#[derive(PartialEq, Eq, Debug, Clone)]
pub struct Loan {
    pub place_expr: PlaceExpr,
    pub own_qual: Ownership,
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub enum DataTy {
    Scalar(ScalarData),
    Tuple(Vec<DataTy>),
    Array(Nat, Box<DataTy>),
    At(Box<DataTy>, Memory),
    Ref(Provenance, Ownership, Memory, Box<DataTy>),
    Fn(Vec<DataTy>, Box<FrameExpr>, ExecLoc, Box<DataTy>),
    GenFn(TyIdent, Box<FrameExpr>, ExecLoc, Box<DataTy>),
    Ident(TyIdent),
}

impl Kinded for DataTy {
    fn get_kind(&self) -> Kind {
        Kind::Data
    }

    fn new_ident(name: &str) -> TyIdent {
        TyIdent {
            name: String::from(name),
            kind: Kind::Data,
        }
    }
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub enum DeadTy {
    Tuple(Vec<DeadTy>),
    Data(DataTy),
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub enum Ty {
    Data(DataTy),
    Dead(DeadTy),
    Tuple(Vec<Ty>),
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub struct IdentTyped {
    pub ident: Ident,
    pub ty: Ty,
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub struct PrvMapping {
    pub prv: String,
    pub loans: Vec<Loan>,
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub enum FrameEntry {
    Var(IdentTyped),
    Prov(PrvMapping),
}
pub type FrameTyping = Vec<FrameEntry>;
pub fn append_idents_typed(frm: &FrameTyping, idents_typed: Vec<(Ident, Ty)>) -> FrameTyping {
    let mut new_frm = frm.clone();
    new_frm.append(
        &mut idents_typed
            .into_iter()
            .map(|(ident, ty)| FrameEntry::Var(IdentTyped { ident, ty }))
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

pub type TypingCtx = Vec<FrameTyping>;

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

    pub fn append_ty_idents(mut self, ty_idents: &Vec<TyIdent>) -> Self {
        let mut entries: Vec<_> = ty_idents
            .iter()
            .map(|tyi| KindingCtxEntry::Ident(tyi.clone()))
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

    pub fn get_ty_idents_by_kind(&self, kind: Kind) -> Vec<TyIdent> {
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

    pub fn outlives(&self, long: &TyIdent, short: &TyIdent) -> Result<(), String> {
        use KindingCtxEntry::PrvRel;

        if let Some(_) = self.vec.iter().find(|&entry| match entry {
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
    pub params: Vec<(Ident, DataTy)>,
    pub ret_ty: DataTy,
    pub exec: ExecLoc,
    pub prv_rels: Vec<PrvRel>,
    pub body_expr: Expr,
    pub fun_ty: DataTy,
}

pub type GlobalCtx = Vec<GlobalFunDef>;
