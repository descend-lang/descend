use super::nat::Nat;
use crate::ast::{Expr, Ident, Ownership, PlaceExpr};

#[derive(Debug, Copy, Clone)]
pub enum Kind {
    Nat,
    Memory,
    Data,
    Provenance,
    Frame,
}

#[derive(Debug, Clone)]
pub enum KindValue {
    Nat(Nat),
    Memory(Memory),
    Data(DataTy),
    Provenance(Provenance),
    Frame(FrameExpr),
}

#[derive(Debug, Clone)]
pub struct TyIdent {
    pub name: String,
    pub kind: Kind,
}

pub trait Kinded {
    fn get_kind(&self) -> Kind;
    fn new_ident(name: &str) -> TyIdent;
}

#[derive(Debug, Copy, Clone)]
pub enum ScalarData {
    I32,
    F32,
    Bool,
    Unit,
}

#[derive(Debug, Clone)]
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

#[derive(Debug, Clone)]
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

#[derive(Debug, Copy, Clone)]
pub enum ExecLoc {
    CpuThread,
    GpuGroup,
    GpuThread,
}

#[derive(Debug, Clone)]
struct Loan {
    place_expr: PlaceExpr,
    own_qual: Ownership,
}

#[derive(Debug, Clone)]
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

#[derive(Debug, Clone)]
pub enum DeadTy {
    Tuple(Vec<DeadTy>),
    Data(DataTy),
}

#[derive(Debug, Clone)]
pub enum Ty {
    Data(DataTy),
    Dead(DeadTy),
    Tuple(Vec<Ty>),
}

#[derive(Debug, Clone)]
pub struct TypedIdent {
    ident: Ident,
    ty: Ty,
}

#[derive(Debug, Clone)]
pub struct ProvMapping {
    prov: String,
    loans: Vec<Loan>,
}

#[derive(Debug, Clone)]
pub enum FrameTyping {
    Var(Box<FrameTyping>, TypedIdent),
    Prov(Box<FrameTyping>, ProvMapping),
    Nil,
}

#[derive(Debug, Clone)]
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

#[derive(Debug, Clone)]
pub enum StackTyping {
    Frame(Box<StackTyping>, FrameTyping),
    Nil,
}

// TODO: make sure TyIdent can only be of kind Provenance
// Reference Relation: varrho_1:varrho_2
pub type ProvRel = (TyIdent, TyIdent);

#[derive(Debug, Clone)]
pub enum KindingContext {
    Ident(Box<KindingContext>, TyIdent),
    RefRel(Box<KindingContext>, Vec<ProvRel>),
    Nil,
}

#[derive(Debug, Clone)]
pub struct GlobalFunDef {
    pub name: String,
    pub ty_idents: Vec<TyIdent>,
    pub params: Vec<(Ident, DataTy)>,
    pub ret_ty: DataTy,
    pub exec: ExecLoc,
    pub prov_rel: Vec<ProvRel>,
    pub body: Expr,
    pub fun_ty: DataTy,
}

#[derive(Debug, Clone)]
enum GlobalEnv {
    Fun(Box<GlobalEnv>, GlobalFunDef),
    Nil,
}
