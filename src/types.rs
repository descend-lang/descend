use super::nat::Nat;

pub enum Kind {
    Nat,
    Data,
    CpData,
    MvData,
    Region,
    Mem,
    Ty,
    Exec,
    AffQual,
    FnTy,
}

pub struct TyIdent {
    pub name: String,
    pub kind: Kind,
}

pub enum ScalarData {
    I32,
    F32,
    Bool,
    Unit,
}

pub enum AffQual {
    Un,
    Aff,
}

pub struct Lifetime {
    pub name: String,
}

pub enum Memory {
    CpuHeap,
    GpuGlobal,
    GpuShared,
}

pub enum ExecLoc {
    Host,
    GpuGroup,
    GpuThread,
}

pub enum CopyData {
    Scalar(ScalarData),
    RefShrd(Lifetime, Memory, Box<DataTy>),
}

pub enum MoveData {
    Pair(Box<DataTy>, Box<DataTy>),
    Array(Nat, Box<DataTy>),
    RefUniq(Lifetime, Memory, Box<DataTy>),
    Own(Box<DataTy>, Memory),
}

pub enum DataTy {
    Un(CopyData),
    Aff(MoveData),
}

pub enum FnTy {
    Fn(Box<Ty>, DataTy, ExecLoc),
    GenFn(TyIdent, Box<Ty>, ExecLoc),
}

pub enum Ty {
    QualFnTy(AffQual, FnTy),
    Data(DataTy),
}
