use crate::ast::{Ident, Path, Place, TypedPlace};
use crate::nat::Nat;
use crate::ty::{FrameTyping, Loan, Ty};
use std::iter::Flatten;
use std::slice::{Iter, IterMut};
use std::vec::IntoIter;

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

#[derive(PartialEq, Eq, Debug, Clone)]
pub struct PrvMapping {
    pub prv: String,
    pub loans: Vec<Loan>,
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub enum TyEntry {
    Var(IdentTyped),
    Prov(PrvMapping),
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub struct TyCtx {
    frame_tys: Vec<FrameTyping>,
}

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
        if let Some(ref mut frame_typing) = self.frame_tys.iter_mut().last() {
            frame_typing.push(TyEntry::Var(id_typed));
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
                if let TyEntry::Var(ident_typed) = fe {
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
                if let TyEntry::Prov(prv_mapping) = fe {
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
            if let TyEntry::Prov(prv_mapping) = fe {
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
            .flat_map(|IdentTyped { ident, ty }| TyCtx::explode_places(ident, ty))
            .collect()
    }

    fn explode_places(ident: &Ident, ty: &Ty) -> Vec<(Place, Ty)> {
        fn proj(mut pl: Place, idx: Nat) -> Place {
            pl.path.push(idx);
            pl
        }

        fn explode(pl: Place, ty: Ty) -> Vec<(Place, Ty)> {
            use crate::nat::Nat::Lit;
            use Ty::*;

            match &ty {
                Scalar(_)
                | Array(_, _)
                | At(_, _)
                | Ref(_, _, _, _)
                | Fn(_, _, _, _)
                | GenFn(_, _, _, _)
                | Ident(_)
                | Dead(_) => vec![(pl, ty.clone())],
                Tuple(tys) => {
                    let mut place_frame = vec![(pl.clone(), ty.clone())];
                    for (index, proj_ty) in tys.iter().enumerate() {
                        let mut exploded_index =
                            explode(proj(pl.clone(), Lit(index)), proj_ty.clone());
                        place_frame.append(&mut exploded_index);
                    }
                    place_frame
                }
            }
        }

        explode(Place::new(ident.clone(), vec![]), ty.clone())
    }

    pub fn type_place(&self, place: &Place) -> Result<Ty, String> {
        fn proj_ty(ty: &Ty, path: &Path) -> Ty {
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

        let ident_ty = match self
            .get_idents_typed()
            .into_iter()
            .find(|id_ty| id_ty.ident == place.ident)
        {
            Some(id) => id,
            None => return Err(format!("Identifier: {} not found in context.", place.ident)),
        };
        Ok(proj_ty(&ident_ty.ty, &place.path))
    }

    pub fn kill_place(&self, pl: &Place) -> Self {
        /*        fn kill_path_in_ty(ty: &Ty, path: &Path) -> Ty {
            if path.is_empty() {
                Ty::Dead(Box::new(ty.clone()))
            } else {
                if let Ty::Tuple(elem_tys) = ty {
                    kill_path_in_ty(elem_tys[path.first().unwrap()], path.remove(0))
                } else {
                    panic!("Path not compatible with type.")
                }
            }
        }

        if let Some(ident_typed) = self
            .get_idents_typed()
            .iter()
            .find(|ident_typed| ident_typed.ident == pl.ident)
        {
            let dead_ty = kill_path_in_ty(&ident_typed.ty, &pl.path);
            let mut res_ty_ctx = self.clone();
            res_ty_ctx.frame_tys.iter_mut()
        } else {
            panic!("Tyring to kill a place which does not exist in this context.")
        }*/
        panic!("todo")
    }

    pub fn iter(&self) -> TyIter {
        TyIter {
            inner: self.frame_tys.iter().flatten(),
        }
    }

    pub fn iter_mut(&mut self) -> TyIterMut {
        TyIterMut {
            inner: self.frame_tys.iter_mut().flatten(),
        }
    }
}

pub struct TyIter<'a> {
    inner: Flatten<Iter<'a, Vec<TyEntry>>>,
}

impl<'a> Iterator for TyIter<'a> {
    type Item = &'a TyEntry;
    fn next(&mut self) -> Option<&'a TyEntry> {
        self.inner.next()
    }
}

pub struct TyIterMut<'a> {
    inner: Flatten<IterMut<'a, Vec<TyEntry>>>,
}

impl<'a> Iterator for TyIterMut<'a> {
    type Item = &'a mut TyEntry;
    fn next(&mut self) -> Option<&'a mut TyEntry> {
        self.inner.next()
    }
}

pub struct TyIntoIter {
    inner: Flatten<IntoIter<Vec<TyEntry>>>,
}

impl Iterator for TyIntoIter {
    type Item = TyEntry;
    fn next(&mut self) -> Option<TyEntry> {
        self.inner.next()
    }
}

impl IntoIterator for TyCtx {
    type Item = TyEntry;
    type IntoIter = TyIntoIter;
    fn into_iter(self) -> TyIntoIter {
        TyIntoIter {
            inner: self.frame_tys.into_iter().flatten(),
        }
    }
}

impl<'a> IntoIterator for &'a TyCtx {
    type Item = &'a TyEntry;
    type IntoIter = TyIter<'a>;
    fn into_iter(self) -> TyIter<'a> {
        self.iter()
    }
}

impl<'a> IntoIterator for &'a mut TyCtx {
    type Item = &'a mut TyEntry;
    type IntoIter = TyIterMut<'a>;
    fn into_iter(self) -> TyIterMut<'a> {
        self.iter_mut()
    }
}
