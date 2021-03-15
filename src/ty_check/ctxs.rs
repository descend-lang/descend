use crate::ast::internal::{FrameEntry, FrameTyping, IdentTyped, Loan, PrvMapping};
use crate::ast::Ty::Data;
use crate::ast::*;
use std::collections::{HashMap, HashSet};

pub(super) type TypedPlace = (Place, Ty);

#[derive(PartialEq, Eq, Debug, Clone)]
pub(super) struct TyCtx {
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
        frame_typing.push(FrameEntry::Var(id_typed));
        self
    }

    pub fn drop_ident(mut self, ident: &Ident) -> Option<Self> {
        for frame in self.frame_tys.iter_mut().rev() {
            let rev_pos_if_exists = frame.iter().rev().position(|ty_entry| match ty_entry {
                FrameEntry::Var(ident_typed) => &ident_typed.ident == ident,
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
        frame_typing.push(FrameEntry::PrvMapping(prv_mapping));
        self
    }

    pub fn idents_typed(&self) -> impl Iterator<Item = &'_ IdentTyped> {
        self.frame_tys.iter().flatten().filter_map(|fe| {
            if let FrameEntry::Var(ident_typed) = fe {
                Some(ident_typed)
            } else {
                None
            }
        })
    }

    pub fn idents_typed_mut(&mut self) -> impl Iterator<Item = &'_ mut IdentTyped> {
        self.frame_tys.iter_mut().flatten().filter_map(|fe| {
            if let FrameEntry::Var(ident_typed) = fe {
                Some(ident_typed)
            } else {
                None
            }
        })
    }

    pub fn prv_mappings(&self) -> impl Iterator<Item = &'_ PrvMapping> {
        self.frame_tys.iter().flatten().filter_map(|fe| {
            if let FrameEntry::PrvMapping(prv_mapping) = fe {
                Some(prv_mapping)
            } else {
                None
            }
        })
    }

    pub fn prv_mappings_mut(&mut self) -> impl Iterator<Item = &'_ mut PrvMapping> {
        self.frame_tys.iter_mut().flatten().filter_map(|fe| {
            if let FrameEntry::PrvMapping(prv_mapping) = fe {
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
            if let FrameEntry::PrvMapping(prv_mapping) = fe {
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
            use DataTy as d;
            use ViewTy as v;

            match &ty {
                Ty::Data(d::Scalar(_))
                | Ty::Data(d::Array(_, _))
                | Ty::Data(d::At(_, _))
                | Ty::Data(d::Ref(_, _, _, _))
                | Ty::Data(d::Fn(_, _, _, _, _))
                | Ty::Data(d::Ident(_))
                | Ty::Data(d::GridConfig(_, _))
                | Ty::Data(d::Dead(_))
                | Ty::View(v::Ident(_))
                | Ty::View(v::Array(_, _))
                | Ty::View(v::Dead(_)) => vec![(pl, ty.clone())],
                Ty::Data(d::Tuple(tys)) => {
                    let mut place_frame = vec![(pl.clone(), ty.clone())];
                    for (index, proj_ty) in tys.iter().enumerate() {
                        let mut exploded_index =
                            explode(proj(pl.clone(), Nat::Lit(index)), Ty::Data(proj_ty.clone()));
                        place_frame.append(&mut exploded_index);
                    }
                    place_frame
                }
                Ty::View(v::Tuple(tys)) => {
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
        fn proj_ty(ty: Ty, path: &[Nat]) -> Ty {
            let mut res_ty = ty;
            for n in path {
                // TODO should maybe use usize here and not Nat, because Nat is not always
                //  evaluable.
                let idx = n.eval();
                match &res_ty {
                    Ty::Data(DataTy::Tuple(elem_tys)) => {
                        res_ty = Ty::Data(elem_tys[idx].clone());
                    }
                    Ty::View(ViewTy::Tuple(elem_tys)) => {
                        res_ty = elem_tys[idx].clone();
                    }
                    _ => panic!("Trying to project element data type of a non tuple type."),
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
                return part_ty;
            }

            let idx = path.first().unwrap().eval();
            match orig_ty {
                Ty::Data(DataTy::Tuple(mut elem_tys)) => {
                    elem_tys[idx] = if let Ty::Data(dty) =
                        set_ty_for_path_in_ty(Ty::Data(elem_tys[idx].clone()), &path[1..], part_ty)
                    {
                        dty
                    } else {
                        panic!("Trying create non-data type as part of data type.")
                    };
                    Ty::Data(DataTy::Tuple(elem_tys))
                }
                Ty::View(ViewTy::Tuple(mut elem_tys)) => {
                    elem_tys[idx] =
                        set_ty_for_path_in_ty(elem_tys[idx].clone(), &path[1..], part_ty);
                    Ty::View(ViewTy::Tuple(elem_tys))
                }
                _ => panic!("Path not compatible with type."),
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

    pub fn kill_place(self, pl: &Place) -> Self {
        if let Ok(pl_ty) = self.place_ty(pl) {
            self.set_place_ty(
                pl,
                match pl_ty {
                    Ty::Data(dty) => Ty::Data(DataTy::Dead(Box::new(dty))),
                    Ty::View(vty) => Ty::View(ViewTy::Dead(Box::new(vty))),
                },
            )
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

    // Γ ▷- p = Γ′
    pub(super) fn without_reborrow_loans(&self, pl_expr: &PlaceExpr) -> TyCtx {
        let res_frame_tys = self
            .frame_tys
            .iter()
            .map(|frm_ty| {
                frm_ty
                    .iter()
                    .map(|frame| match frame {
                        FrameEntry::Var(ident_typed) => FrameEntry::Var(ident_typed.clone()),
                        FrameEntry::PrvMapping(PrvMapping { prv, loans }) => {
                            let without_reborrow: HashSet<Loan> = loans
                                .iter()
                                .filter_map(|loan| {
                                    if !PlaceExpr::Deref(Box::new(pl_expr.clone()))
                                        .prefix_of(&loan.place_expr)
                                    {
                                        Some(loan.clone())
                                    } else {
                                        None
                                    }
                                })
                                .collect();
                            FrameEntry::PrvMapping(PrvMapping {
                                prv: prv.clone(),
                                loans: without_reborrow,
                            })
                        }
                    })
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        TyCtx {
            frame_tys: res_frame_tys,
        }
    }
}

#[derive(PartialEq, Eq, Debug, Clone)]
enum KindingCtxEntry {
    Ident(IdentKinded),
    PrvRel(PrvRel),
}

pub(super) struct KindCtx {
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
pub(super) struct GlobalCtx {
    items: HashMap<String, DataTy>,
}

impl GlobalCtx {
    pub fn new() -> Self {
        GlobalCtx {
            items: HashMap::new(),
        }
    }

    pub fn append_from_gl_fun_defs(mut self, gl_fun_defs: &[FunDef]) -> Self {
        self.items.extend(
            gl_fun_defs
                .iter()
                .map(|gl_fun_def| (gl_fun_def.name.clone(), gl_fun_def.ty())),
        );
        self
    }

    pub fn append_fun_decls(mut self, fun_decls: &[(&str, DataTy)]) -> Self {
        self.items.extend(
            fun_decls
                .iter()
                .map(|(name, ty)| (String::from(*name), ty.clone())),
        );
        self
    }

    pub fn fun_ty_by_name(&self, name: &str) -> Result<&DataTy, String> {
        match self.items.get(name) {
            Some(ty) => Ok(ty),
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
    let x = IdentTyped::new(Ident::new("x"), Ty::Data(DataTy::Scalar(ScalarTy::I32)));
    let place = Place::new(x.ident.clone(), vec![]);
    ty_ctx = ty_ctx.append_ident_typed(x);
    ty_ctx = ty_ctx.kill_place(&place);
    assert!(
        if let Ty::Data(DataTy::Dead(_)) = ty_ctx.idents_typed().next().unwrap().ty {
            true
        } else {
            false
        }
    );
}
