use crate::ast::ty::{FrameTyping, Loan, Nat, ScalarData, Ty};
use crate::ast::{Ident, Path, Place, TypedPlace};
use std::collections::HashSet;

#[derive(PartialEq, Eq, Debug, Clone)]
// TODO only store references?
pub struct IdentTyped {
    pub ident: Ident,
    pub ty: Ty,
}

impl IdentTyped {
    pub fn new(ident: Ident, ty: Ty) -> Self {
        IdentTyped { ident, ty }
    }
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub struct PrvMapping {
    pub prv: String,
    pub loans: HashSet<Loan>,
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub enum TyEntry {
    Var(IdentTyped),
    PrvMapping(PrvMapping),
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub struct TyCtx {
    frame_tys: Vec<FrameTyping>,
}

// TODO more use of Iterators for construction of new Ctxts (Iterators representing Ctxts)
//  and to pass values to the ctx.
//  Maybe just return more references.
impl TyCtx {
    pub fn new() -> Self {
        TyCtx {
            frame_tys: vec![vec![]],
        }
    }

    pub fn from(fr_ty: FrameTyping) -> Self {
        TyCtx {
            frame_tys: vec![fr_ty],
        }
    }

    pub fn append_ident_typed(mut self, id_typed: IdentTyped) -> Self {
        let frame_typing = self.frame_tys.iter_mut().last().unwrap();
        frame_typing.push(TyEntry::Var(id_typed));
        self
    }

    pub fn append_prv_mapping(mut self, prv_mapping: PrvMapping) -> Self {
        let frame_typing = self.frame_tys.iter_mut().last().unwrap();
        frame_typing.push(TyEntry::PrvMapping(prv_mapping));
        self
    }

    pub fn idents_typed(&self) -> impl Iterator<Item = &'_ IdentTyped> {
        self.frame_tys.iter().flatten().filter_map(|fe| {
            if let TyEntry::Var(ident_typed) = fe {
                Some(ident_typed)
            } else {
                None
            }
        })
    }

    pub fn idents_typed_mut(&mut self) -> impl Iterator<Item = &'_ mut IdentTyped> {
        self.frame_tys.iter_mut().flatten().filter_map(|fe| {
            if let TyEntry::Var(ident_typed) = fe {
                Some(ident_typed)
            } else {
                None
            }
        })
    }

    pub fn prv_mappings(&self) -> impl Iterator<Item = &'_ PrvMapping> {
        self.frame_tys.iter().flatten().filter_map(|fe| {
            if let TyEntry::PrvMapping(prv_mapping) = fe {
                Some(prv_mapping)
            } else {
                None
            }
        })
    }

    pub fn prv_mappings_mut(&mut self) -> impl Iterator<Item = &'_ mut PrvMapping> {
        self.frame_tys.iter_mut().flatten().filter_map(|fe| {
            if let TyEntry::PrvMapping(prv_mapping) = fe {
                Some(prv_mapping)
            } else {
                None
            }
        })
    }

    pub fn update_loan_set(
        mut self,
        prv_val_name: &str,
        loan_set: HashSet<Loan>,
    ) -> Result<Self, String> {
        for fe in self.frame_tys.iter_mut().flatten() {
            if let TyEntry::PrvMapping(prv_mapping) = fe {
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

    pub fn extend_loans_for_prv<I>(mut self, base: &str, extension: I) -> Result<TyCtx, String>
    where
        I: IntoIterator<Item = Loan>,
    {
        let base_loans = self.loans_for_prv_mut(base)?;
        base_loans.extend(extension);
        Ok(self)
    }

    pub fn loans_for_prv(&self, prv_val_name: &str) -> Result<&HashSet<Loan>, String> {
        match self
            .prv_mappings()
            .find(|prv_mapping| prv_val_name == prv_mapping.prv)
        {
            Some(set) => Ok(&set.loans),
            None => Err(format!(
                "Provenance with name '{}', not found in context.",
                prv_val_name
            )),
        }
    }

    pub fn loans_for_prv_mut(&mut self, prv_val_name: &str) -> Result<&mut HashSet<Loan>, String> {
        match self
            .prv_mappings_mut()
            .find(|prv_mapping| prv_val_name == prv_mapping.prv)
        {
            Some(set) => Ok(&mut set.loans),
            None => Err(format!(
                "Provenance with name '{}', not found in context.",
                prv_val_name
            )),
        }
    }

    pub fn prv_val_exists(&self, prv_val_name: &str) -> bool {
        self.prv_mappings()
            .any(|prv_mapping| prv_mapping.prv == prv_val_name)
    }

    pub fn is_empty(&self) -> bool {
        self.frame_tys.first().unwrap().is_empty()
    }

    // ∀π:τ ∈ Γ
    pub fn all_places(&self) -> Vec<TypedPlace> {
        self.idents_typed()
            .flat_map(|IdentTyped { ident, ty }| TyCtx::explode_places(ident, ty))
            .collect()
    }

    fn explode_places(ident: &Ident, ty: &Ty) -> Vec<TypedPlace> {
        fn proj(mut pl: Place, idx: Nat) -> Place {
            pl.path.push(idx);
            pl
        }

        fn explode(pl: Place, ty: Ty) -> Vec<TypedPlace> {
            use super::ty::Nat;
            use Ty::*;

            match &ty {
                Scalar(_)
                | Array(_, _)
                | At(_, _)
                | Ref(_, _, _, _)
                | Fn(_, _, _, _)
                | DepFn(_, _, _, _)
                | Ident(_)
                | Dead(_) => vec![(pl, ty.clone())],
                Tuple(tys) => {
                    let mut place_frame = vec![(pl.clone(), ty.clone())];
                    for (index, proj_ty) in tys.iter().enumerate() {
                        let mut exploded_index =
                            explode(proj(pl.clone(), Nat::Lit(index)), proj_ty.clone());
                        place_frame.append(&mut exploded_index);
                    }
                    place_frame
                }
            }
        }

        explode(Place::new(ident.clone(), vec![]), ty.clone())
    }

    pub fn ident_ty(&self, ident: &Ident) -> Result<&Ty, String> {
        match self.idents_typed().find(|id_ty| &id_ty.ident == ident) {
            Some(id) => Ok(&id.ty),
            None => Err(format!("Identifier: {} not found in context.", ident)),
        }
    }

    pub fn place_ty(&self, place: &Place) -> Result<Ty, String> {
        fn proj_ty(ty: Ty, path: &Path) -> Ty {
            let mut res_ty = ty;
            for n in path {
                if let Ty::Tuple(elem_tys) = res_ty {
                    // TODO should probably use usize here and not Nat, because Nat is not always
                    //  evaluable.
                    let idx = n.eval();
                    res_ty = elem_tys[idx].clone();
                } else {
                    panic!("Trying to project element data type of a non tuple type.");
                }
            }
            res_ty
        }
        let ident_ty = self.ident_ty(&place.ident)?;
        Ok(proj_ty(ident_ty.clone(), &place.path))
    }

    pub fn kill_place(mut self, pl: &Place) -> Self {
        fn kill_path_in_ty(ty: Ty, path: &[Nat]) -> Ty {
            if path.is_empty() {
                Ty::Dead(Box::new(ty.clone()))
            } else if let Ty::Tuple(mut elem_tys) = ty {
                let idx = path.first().unwrap().eval();
                elem_tys[idx] = kill_path_in_ty(elem_tys[idx].clone(), &path[1..]);
                Ty::Tuple(elem_tys)
            } else {
                // TODO make this an Error?
                panic!("Path not compatible with type.")
            }
        }

        let mut ident_typed = self
            .idents_typed_mut()
            .find(|ident_typed| ident_typed.ident == pl.ident)
            .unwrap();
        let dead_ty = kill_path_in_ty(ident_typed.ty.clone(), pl.path.as_slice());
        ident_typed.ty = dead_ty;
        self
    }

    pub fn garbage_collect_loans(self) -> Self {
        let invalid_prvs: Vec<_> = self
            .prv_mappings()
            .map(|prv_mapping| &prv_mapping.prv)
            .filter(|prv| {
                self.idents_typed()
                    .map(|id_ty| &id_ty.ty)
                    .all(|ty| !ty.contains_ref_to_prv(prv.as_str()))
            })
            .cloned()
            .collect();
        self.invalidate_prvs(invalid_prvs)
    }

    fn invalidate_prvs(self, prv_names: Vec<String>) -> Self {
        prv_names.iter().fold(self, |ty_ctx, prv| {
            ty_ctx
                .update_loan_set(prv.as_str(), HashSet::new())
                .unwrap()
        })
    }
}

#[test]
fn test_kill_place_ident() {
    let mut ty_ctx = TyCtx::new();
    let x = IdentTyped::new(Ident::new("x"), Ty::Scalar(ScalarData::I32));
    let place = Place::new(x.ident.clone(), vec![]);
    ty_ctx = ty_ctx.append_ident_typed(x);
    ty_ctx = ty_ctx.kill_place(&place);
    assert!(
        if let Ty::Dead(_) = ty_ctx.idents_typed().next().unwrap().ty {
            true
        } else {
            false
        }
    );
}
