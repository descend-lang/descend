use super::nat::Nat;
use crate::ast::*;
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

impl DataTy {
    pub fn non_copyable(&self) -> bool {
        use DataTy::*;

        match self {
            Scalar(sc) => false,
            Ident(_) => true,
            Ref(_, Ownership::Uniq, _, _) => true,
            Ref(_, Ownership::Shrd, _, _) => false,
            Fn(_, _, _, _) => false,
            GenFn(_, _, _, _) => false,
            At(_, _) => true,
            Tuple(elem_dtys) => elem_dtys.iter().any(|dty| dty.non_copyable()),
            Array(_, dty) => dty.non_copyable(),
        }
    }

    pub fn copyable(&self) -> bool {
        !self.non_copyable()
    }
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

#[derive(PartialEq, Eq, Debug, Clone)]
pub struct TypingCtx {
    frame_tys: Vec<FrameTyping>,
}

impl TypingCtx {
    pub fn new() -> Self {
        TypingCtx {
            frame_tys: vec![vec![]],
        }
    }

    pub fn from(fr_ty: FrameTyping) -> Self {
        TypingCtx {
            frame_tys: vec![fr_ty],
        }
    }

    pub fn append_ident_typed(mut self, id_typed: IdentTyped) -> Self {
        if let Some(ref mut frame_typing) = self.frame_tys.iter_mut().last() {
            frame_typing.push(FrameEntry::Var(id_typed));
            self
        } else {
            panic!("This should never happen.")
        }
    }

    // This function MUST keep the order in which the identifiers appear in the Typing Ctx
    pub fn get_idents_typed(&self) -> Vec<IdentTyped> {
        self.frame_tys
            .iter()
            .flatten()
            .filter_map(|fe| {
                if let FrameEntry::Var(ident_typed) = fe {
                    Some(ident_typed.clone())
                } else {
                    None
                }
            })
            .collect()
    }

    // This function MUST keep the order in which the PRVs appear in the Typing Ctx
    pub fn get_prv_mappings(&self) -> Vec<PrvMapping> {
        self.frame_tys
            .iter()
            .flatten()
            .filter_map(|fe| {
                if let FrameEntry::Prov(prv_mapping) = fe {
                    Some(prv_mapping.clone())
                } else {
                    None
                }
            })
            .collect()
    }

    pub fn update_loan_set(
        mut self,
        prv_val_name: &str,
        loan_set: Vec<Loan>,
    ) -> Result<Self, String> {
        for fe in self.frame_tys.iter_mut().flatten() {
            if let FrameEntry::Prov(prv_mapping) = fe {
                if prv_mapping.prv == prv_val_name {
                    prv_mapping.loans = loan_set;
                    return Ok(self);
                }
            }
        }
        Err(format!(
            "Typing Context is missing the provenance value {}",
            prv_val_name
        ))
    }

    pub fn get_loan_set(&self, prv_val_name: &str) -> Result<Vec<Loan>, String> {
        match self
            .get_prv_mappings()
            .iter()
            .find(|prv_mapping| prv_val_name == prv_mapping.prv)
        {
            Some(set) => Ok(set.loans.clone()),
            None => Err(format!(
                "Provenance with name '{}', not found in context.",
                prv_val_name
            )),
        }
    }

    pub fn prv_val_exists(&self, prv_val_name: &str) -> bool {
        self.get_prv_mappings()
            .iter()
            .any(|prv_mapping| prv_mapping.prv == prv_val_name)
    }

    pub fn is_empty(&self) -> bool {
        if let Some(frame_typing) = self.frame_tys.first() {
            frame_typing.is_empty()
        } else {
            panic!("This should never happen.")
        }
    }

    // ∀π:τ ∈ Γ
    pub fn all_places(&self) -> Vec<TypedPlace> {
        self.get_idents_typed()
            .iter()
            .flat_map(|IdentTyped { ident, ty }| match ty {
                Ty::Data(dty) => TypingCtx::explode_places(ident, dty),
                _ => vec![],
            })
            .collect()
    }

    fn explode_places(ident: &Ident, dty: &DataTy) -> Vec<(Place, DataTy)> {
        fn proj(mut pl: Place, idx: Nat) -> Place {
            pl.1.push(idx);
            (pl.0, pl.1)
        }

        fn explode(pl: Place, dty: DataTy) -> Vec<(Place, DataTy)> {
            use super::nat::Nat::Lit;
            use DataTy::*;

            match &dty {
                Scalar(_)
                | Array(_, _)
                | At(_, _)
                | Ref(_, _, _, _)
                | Fn(_, _, _, _)
                | GenFn(_, _, _, _)
                | Ident(_) => vec![(pl, dty.clone())],
                Tuple(dtys) => {
                    let mut place_frame = vec![(pl.clone(), dty.clone())];
                    let mut index = 0;
                    for proj_dty in dtys.iter() {
                        let mut exploded_index =
                            explode(proj(pl.clone(), Lit(index)), proj_dty.clone());
                        place_frame.append(&mut exploded_index);
                        index += 1;
                    }
                    place_frame
                }
            }
        }

        explode((ident.clone(), vec![]), dty.clone())
    }

    pub fn type_place(&self, place: &Place) -> Option<Ty> {
        fn proj_dty(ty: &Ty, path: &Path) -> Ty {
            let mut res_ty = ty.clone();
            for n in path {
                if let Ty::Tuple(elem_tys) = ty {
                    let idx = n.eval();
                    res_ty = elem_tys[idx].clone();
                } else {
                    panic!("Trying to project element data type of a non tuple type.");
                }
            }
            res_ty
        }

        let (ident, path) = place;
        let ident_ty = self
            .get_idents_typed()
            .into_iter()
            .find(|id_ty| &id_ty.ident == ident)?;
        Some(proj_dty(&ident_ty.ty, &path))
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

    pub fn prv_ident_exists(&self, prv_ident_name: &TyIdent) -> bool {
        self.get_ty_idents(Kind::Provenance)
            .iter()
            .any(|prv_ident| prv_ident_name == prv_ident)
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
