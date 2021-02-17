use super::{Path, Place};
use crate::ast::internal::FrameTyping;
use crate::ast::*;
use std::collections::HashSet;

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

pub type TypedPlace = (Place, Ty);

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
        let frame_typing = self.frame_tys.iter_mut().last().unwrap();
        frame_typing.push(TyEntry::Var(id_typed));
        self
    }

    pub fn drop_ident(mut self, ident: &Ident) -> Option<Self> {
        for frame in self.frame_tys.iter_mut().rev() {
            let rev_pos_if_exists = frame.iter().rev().position(|ty_entry| match ty_entry {
                TyEntry::Var(ident_typed) => &ident_typed.ident == ident,
                _ => false,
            });
            if let Some(rev_pos) = rev_pos_if_exists {
                let pos = frame.len() - (rev_pos + 1);
                frame.remove(pos);
                return Some(self);
            }
        }
        None
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
            use Ty::*;

            match &ty {
                Scalar(_)
                | Array(_, _)
                // TODO maybe introduce places for this type
                | ArrayView(_, _)
                | At(_, _)
                | Ref(_, _, _, _)
                | Fn(_, _, _, _, _)
                | Ident(_)
                | Dead(_)
                | Gpu => vec![(pl, ty.clone())],
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

    pub fn set_place_ty(mut self, pl: &Place, pl_ty: Ty) -> Self {
        fn set_ty_for_path_in_ty(orig_ty: Ty, path: &[Nat], part_ty: Ty) -> Ty {
            if path.is_empty() {
                part_ty
            } else if let Ty::Tuple(mut elem_tys) = orig_ty {
                let idx = path.first().unwrap().eval();
                elem_tys[idx] = set_ty_for_path_in_ty(elem_tys[idx].clone(), &path[1..], part_ty);
                Ty::Tuple(elem_tys)
            } else {
                panic!("Path not compatible with type.")
            }
        }

        let mut ident_typed = self
            .idents_typed_mut()
            .find(|ident_typed| ident_typed.ident == pl.ident)
            .unwrap();
        let updated_ty = set_ty_for_path_in_ty(ident_typed.ty.clone(), pl.path.as_slice(), pl_ty);
        ident_typed.ty = updated_ty;
        self
    }

    pub fn kill_place(mut self, pl: &Place) -> Self {
        if let Ok(pl_ty) = self.place_ty(pl) {
            self.set_place_ty(pl, Ty::Dead(Box::new(pl_ty)))
        } else {
            panic!("Trying to kill the type of a place that doesn't exist.")
        }
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

pub trait IntoGlobalItem {
    fn into_item(self) -> GlobalItem;
}

#[derive(Debug, Clone)]
pub struct PreDeclaredGlobalFun {
    pub name: String,
    pub fun_ty: Ty,
}

impl IntoGlobalItem for PreDeclaredGlobalFun {
    fn into_item(self) -> GlobalItem {
        GlobalItem::PreDecl(Box::new(self))
    }
}

impl IntoGlobalItem for GlobalFunDef {
    fn into_item(self) -> GlobalItem {
        GlobalItem::Def(Box::new(self))
    }
}

// todo move out, not part of the syntax
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
        T: IntoGlobalItem,
        I: IntoIterator<Item = T>,
    {
        self.items
            .extend(new_items.into_iter().map(IntoGlobalItem::into_item));
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

#[test]
fn test_kill_place_ident() {
    let mut ty_ctx = TyCtx::new();
    let x = IdentTyped::new(Ident::new("x"), Ty::Scalar(ScalarTy::I32));
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
