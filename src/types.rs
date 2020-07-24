use super::nat::Nat;

#[derive(Debug, Copy, Clone)]
pub enum Kind {
    Nat,
    Data,
    CopyData,
    MoveData,
    Lifetime,
    Memory,
    Ty,
    ExecLoc,
    AffQual,
    FnTy,
}

#[derive(Debug, Clone)]
pub struct TyIdent {
    pub name: String,
    pub kind: Kind,
}

pub trait IdentType {
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
pub enum AffQual {
    Un,
    Aff,
    Ident(TyIdent),
}

impl IdentType for AffQual {
    fn new_ident(name: &str) -> TyIdent {
        TyIdent {
            name: String::from(name),
            kind: Kind::AffQual,
        }
    }
}

#[derive(Debug, Clone)]
pub enum Lifetime {
    L(String),
    Ident(TyIdent),
}

impl IdentType for Lifetime {
    fn new_ident(name: &str) -> TyIdent {
        TyIdent {
            name: String::from(name),
            kind: Kind::Lifetime,
        }
    }
}

#[derive(Debug, Clone)]
pub enum Memory {
    CpuHeap,
    GpuGlobal,
    GpuShared,
    Ident(TyIdent),
}

impl IdentType for Memory {
    fn new_ident(name: &str) -> TyIdent {
        TyIdent {
            name: String::from(name),
            kind: Kind::Memory,
        }
    }
}

#[derive(Debug, Clone)]
pub enum ExecLoc {
    Host,
    GpuGroup,
    GpuThread,
    Ident(TyIdent),
}

impl IdentType for ExecLoc {
    fn new_ident(name: &str) -> TyIdent {
        TyIdent {
            name: String::from(name),
            kind: Kind::ExecLoc,
        }
    }
}

#[derive(Debug, Clone)]
pub enum CopyData {
    Scalar(ScalarData),
    RefConst(Lifetime, Memory, Box<DataTy>),
    Ident(TyIdent),
}

impl IdentType for CopyData {
    fn new_ident(name: &str) -> TyIdent {
        TyIdent {
            name: String::from(name),
            kind: Kind::CopyData,
        }
    }
}

#[derive(Debug, Clone)]
pub enum MoveData {
    Tuple(Vec<DataTy>),
    Array(Nat, Box<DataTy>),
    RefMut(Lifetime, Memory, Box<DataTy>),
    At(Box<DataTy>, Memory),
    Ident(TyIdent),
}

impl IdentType for MoveData {
    fn new_ident(name: &str) -> TyIdent {
        TyIdent {
            name: String::from(name),
            kind: Kind::MoveData,
        }
    }
}

#[derive(Debug, Clone)]
pub enum DataTy {
    Un(CopyData),
    Aff(MoveData),
    Ident(TyIdent),
}

impl IdentType for DataTy {
    fn new_ident(name: &str) -> TyIdent {
        TyIdent {
            name: String::from(name),
            kind: Kind::Data,
        }
    }
}

#[derive(Debug, Clone)]
pub enum FnTy {
    Fn(Box<Ty>, DataTy, ExecLoc),
    GenFn(TyIdent, Box<Ty>, ExecLoc),
    Ident(TyIdent),
}

impl IdentType for FnTy {
    fn new_ident(name: &str) -> TyIdent {
        TyIdent {
            name: String::from(name),
            kind: Kind::FnTy,
        }
    }
}

#[derive(Debug, Clone)]
pub enum Ty {
    QualFnTy(AffQual, FnTy),
    Data(DataTy),
}
