use crate::ast::internal::{Frame, FrameEntry, IdentTyped, Loan, PrvMapping};
use crate::ast::*;
use crate::ty_check::error::CtxError;
use crate::ty_check::constraint_check::*;
use std::collections::{HashMap, HashSet};

// TODO introduce proper struct
pub(super) type TypedPlace = (internal::Place, Ty);

#[derive(PartialEq, Eq, Debug, Clone)]
pub(super) struct TyCtx {
    frame: Vec<Frame>,
}

impl TyCtx {
    pub fn new() -> Self {
        TyCtx {
            frame: vec![vec![]],
        }
    }

    pub fn from(fr_ty: Frame) -> Self {
        TyCtx { frame: vec![fr_ty] }
    }

    pub fn append_frame(mut self, frm_ty: Frame) -> Self {
        self.frame.append(&mut vec![frm_ty]);
        self
    }

    pub fn drop_last_frame(mut self) -> Self {
        self.frame
            .pop()
            .expect("It should never be the case that there is no frame typing.");
        self
    }

    pub fn append_ident_typed(mut self, id_typed: IdentTyped) -> Self {
        let frame_typing = self.frame.iter_mut().last().unwrap();
        frame_typing.push(FrameEntry::Var(id_typed));
        self
    }

    pub fn drop_ident(mut self, ident: &Ident) -> Option<Self> {
        for frame in self.frame.iter_mut().rev() {
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
        let frame_typing = self.frame.iter_mut().last().unwrap();
        frame_typing.push(FrameEntry::PrvMapping(prv_mapping));
        self
    }

    fn idents_typed(&self) -> impl DoubleEndedIterator<Item = &'_ IdentTyped> {
        self.frame.iter().flatten().filter_map(|fe| {
            if let FrameEntry::Var(ident_typed) = fe {
                Some(ident_typed)
            } else {
                None
            }
        })
    }

    fn idents_typed_mut(&mut self) -> impl DoubleEndedIterator<Item = &'_ mut IdentTyped> {
        self.frame.iter_mut().flatten().filter_map(|fe| {
            if let FrameEntry::Var(ident_typed) = fe {
                Some(ident_typed)
            } else {
                None
            }
        })
    }

    pub(crate) fn prv_mappings(&self) -> impl DoubleEndedIterator<Item = &'_ PrvMapping> {
        self.frame.iter().flatten().filter_map(|fe| {
            if let FrameEntry::PrvMapping(prv_mapping) = fe {
                Some(prv_mapping)
            } else {
                None
            }
        })
    }

    fn prv_mappings_mut(&mut self) -> impl DoubleEndedIterator<Item = &'_ mut PrvMapping> {
        self.frame.iter_mut().flatten().filter_map(|fe| {
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
    ) -> CtxResult<Self> {
        let mut found = false;
        for prv_mapping in self.prv_mappings_mut().rev() {
            if prv_mapping.prv == prv_val_name {
                prv_mapping.loans = loan_set;
                found = true;
                break;
            }
        }
        if found {
            Ok(self)
        } else {
            Err(CtxError::PrvValueNotFound(prv_val_name.to_string()))
        }
    }

    pub fn extend_loans_for_prv<I>(mut self, base: &str, extension: I) -> CtxResult<TyCtx>
    where
        I: IntoIterator<Item = Loan>,
    {
        let base_loans = self.loans_for_prv_mut(base)?;
        base_loans.extend(extension);
        Ok(self)
    }

    pub fn loans_in_prv(&self, prv_val_name: &str) -> CtxResult<&HashSet<Loan>> {
        match self
            .prv_mappings()
            .rev()
            .find(|prv_mapping| prv_val_name == prv_mapping.prv)
        {
            Some(set) => Ok(&set.loans),
            None => Err(CtxError::PrvValueNotFound(prv_val_name.to_string())),
        }
    }

    pub fn loans_for_prv_mut(&mut self, prv_val_name: &str) -> CtxResult<&mut HashSet<Loan>> {
        match self
            .prv_mappings_mut()
            .rev()
            .find(|prv_mapping| prv_val_name == prv_mapping.prv)
        {
            Some(set) => Ok(&mut set.loans),
            None => Err(CtxError::PrvValueNotFound(prv_val_name.to_string())),
        }
    }

    pub fn prv_val_exists(&self, prv_val_name: &str) -> bool {
        self.prv_mappings()
            .any(|prv_mapping| prv_mapping.prv == prv_val_name)
    }

    pub fn is_empty(&self) -> bool {
        self.frame.first().unwrap().is_empty()
    }

    // ∀π:τ ∈ Γ
    pub fn all_places(&self) -> Vec<TypedPlace> {
        self.idents_typed()
            .flat_map(|IdentTyped { ident, ty, .. }| TyCtx::explode_places(&ident, &ty))
            .collect()
    }

    fn explode_places(ident: &Ident, ty: &Ty) -> Vec<TypedPlace> {
        fn proj(mut pl: internal::Place, idx: usize) -> internal::Place {
            pl.path.push(idx);
            pl
        }

        fn explode(pl: internal::Place, ty: Ty) -> Vec<TypedPlace> {
            use DataTyKind as d;

            match &ty.ty {
                TyKind::Ident(_)
                | TyKind::Fn(_, _, _)
                | TyKind::Data(DataTy { dty: d::Range, .. })
                | TyKind::Data(DataTy {
                    dty: d::Atomic(_), ..
                })
                | TyKind::Data(DataTy {
                    dty: d::ThreadHierchy(_),
                    ..
                })
                | TyKind::Data(DataTy {
                    dty: d::Scalar(_), ..
                })
                | TyKind::Data(DataTy {
                    dty: d::Array(_, _),
                    ..
                })
                | TyKind::Data(DataTy {
                    dty: d::ArrayShape(_, _),
                    ..
                })
                | TyKind::Data(DataTy {
                    dty: d::At(_, _), ..
                })
                | TyKind::Data(DataTy {
                    dty: d::Ref(_, _, _, _),
                    ..
                })
                | TyKind::Data(DataTy {
                    dty: d::RawPtr(_), ..
                })
                | TyKind::Data(DataTy {
                    dty: d::Ident(_), ..
                })
                | TyKind::Data(DataTy {
                    dty: d::Dead(_), ..
                })
                | TyKind::Dead(_) => vec![(pl, ty.clone())],
                TyKind::Data(DataTy {
                    dty: d::Tuple(tys), ..
                }) => {
                    let mut place_frame = vec![(pl.clone(), ty.clone())];
                    for (index, proj_ty) in tys.iter().enumerate() {
                        let mut exploded_index = explode(
                            proj(pl.clone(), index),
                            Ty::new(TyKind::Data(proj_ty.clone())),
                        );
                        place_frame.append(&mut exploded_index);
                    }
                    place_frame
                },
                TyKind::Data(DataTy {
                    dty: d::StructMonoType(_), ..
                }) => unimplemented!("TODO"),
            }
        }

        explode(internal::Place::new(ident.clone(), vec![]), ty.clone())
    }

    pub fn ty_of_ident(&self, ident: &Ident) -> CtxResult<&Ty> {
        Ok(&self.ident_ty(ident)?.ty)
    }

    pub fn ident_ty(&self, ident: &Ident) -> CtxResult<&IdentTyped> {
        match self
            .idents_typed()
            .rev()
            .find(|id_ty| &id_ty.ident == ident)
        {
            Some(id) => Ok(id),
            None => Err(CtxError::IdentNotFound(ident.clone())),
        }
    }

    pub fn place_ty(&self, place: &internal::Place) -> CtxResult<Ty> {
        fn proj_ty(ty: Ty, path: &[usize]) -> CtxResult<Ty> {
            let mut res_ty = ty;
            for n in path {
                match &res_ty.ty {
                    TyKind::Data(DataTy {
                        dty: DataTyKind::Tuple(elem_tys),
                        ..
                    }) => {
                        if elem_tys.len() <= *n {
                            return Err(CtxError::IllegalProjection);
                        }
                        res_ty = Ty::new(TyKind::Data(elem_tys[*n].clone()));
                    }
                    t => {
                        panic!(
                            "Trying to project element data type of a non tuple type:\n {:?}",
                            t
                        )
                    }
                }
            }
            Ok(res_ty)
        }
        let ident_ty = self.ty_of_ident(&place.ident)?;
        proj_ty(ident_ty.clone(), &place.path)
    }

    pub fn set_place_ty(mut self, pl: &internal::Place, pl_ty: Ty) -> Self {
        fn set_ty_for_path_in_ty(orig_ty: Ty, path: &[usize], part_ty: Ty) -> Ty {
            if path.is_empty() {
                return part_ty;
            }

            let idx = path.first().unwrap();
            match orig_ty.ty {
                TyKind::Data(DataTy {
                    dty: DataTyKind::Tuple(mut elem_tys),
                    ..
                }) => {
                    elem_tys[*idx] = if let TyKind::Data(dty) = set_ty_for_path_in_ty(
                        Ty::new(TyKind::Data(elem_tys[*idx].clone())),
                        &path[1..],
                        part_ty,
                    )
                    .ty
                    {
                        dty
                    } else {
                        panic!("Trying create non-data type as part of data type.")
                    };
                    Ty::new(TyKind::Data(DataTy::new(DataTyKind::Tuple(elem_tys))))
                }
                _ => panic!("Path not compatible with type."),
            }
        }

        let mut ident_typed = self
            .idents_typed_mut()
            .rev()
            .find(|ident_typed| ident_typed.ident == pl.ident)
            .unwrap();
        let updated_ty = set_ty_for_path_in_ty(ident_typed.ty.clone(), pl.path.as_slice(), pl_ty);
        ident_typed.ty = updated_ty;
        self
    }

    pub fn kill_place(self, pl: &internal::Place) -> Self {
        if let Ok(pl_ty) = self.place_ty(pl) {
            self.set_place_ty(
                pl,
                match &pl_ty.ty {
                    TyKind::Ident(_) => Ty::new(TyKind::Dead(Box::new(pl_ty.clone()))),
                    TyKind::Fn(_, _, _) => Ty::new(TyKind::Dead(Box::new(pl_ty.clone()))),
                    TyKind::Data(dty) => Ty::new(TyKind::Data(DataTy::new(DataTyKind::Dead(
                        Box::new(dty.clone()),
                    )))),
                    TyKind::Dead(_) => {
                        panic!("Cannot kill dead type.")
                    }
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
                // TODO simply delete the provenance?1
                .update_loan_set(prv.as_str(), HashSet::new())
                .unwrap()
        })
    }

    // Γ ▷- p = Γ′
    pub(super) fn without_reborrow_loans(&self, pl_expr: &PlaceExpr) -> TyCtx {
        let res_frame_tys = self
            .frame
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
                                    if !PlaceExpr::new(PlaceExprKind::Deref(Box::new(
                                        pl_expr.clone(),
                                    )))
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
            frame: res_frame_tys,
        }
    }
}

#[derive(PartialEq, Eq, Debug, Clone)]
enum KindingCtxEntry {
    Ident(IdentKinded),
    PrvRel(PrvRel),
}

pub(super) type CtxResult<T> = Result<T, CtxError>;

#[derive(PartialEq, Eq, Debug, Clone)]
pub(super) struct KindCtx {
    ctx: Vec<KindingCtxEntry>,
}

impl KindCtx {
    pub fn new() -> Self {
        KindCtx { ctx: Vec::new() }
    }

    pub fn append_idents(mut self, idents: Vec<IdentKinded>) -> Self {
        let entries: Vec<_> = idents.into_iter().map(KindingCtxEntry::Ident).collect();
        self.ctx.extend(entries);
        self
    }

    pub fn append_prv_rels(mut self, prv_rels: Vec<PrvRel>) -> Self {
        for prv_rel in prv_rels {
            self.ctx.push(KindingCtxEntry::PrvRel(prv_rel));
        }
        self
    }

    pub fn get_idents(&self, kind: Kind) -> impl Iterator<Item = &Ident> {
        self.ctx.iter().filter_map(move |entry| {
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

    pub fn get_kind(&self, ident: &Ident) -> CtxResult<&Kind> {
        let res = self.ctx.iter().find_map(|entry| {
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
            Err(CtxError::KindedIdentNotFound(ident.clone()))
        }
    }

    pub fn ident_of_kind_exists(&self, ident: &Ident, kind: Kind) -> bool {
        self.get_idents(kind).any(|id| ident == id)
    }

    pub fn well_kinded_prv_rels(&self, prv_rels: &[PrvRel]) -> CtxResult<()> {
        let mut prv_idents = self.get_idents(Kind::Provenance);
        for prv_rel in prv_rels {
            if !prv_idents.any(|prv_ident| &prv_rel.longer == prv_ident) {
                return Err(CtxError::PrvIdentNotFound(prv_rel.longer.clone()));
            }
            if !prv_idents.any(|prv_ident| &prv_rel.shorter == prv_ident) {
                return Err(CtxError::PrvIdentNotFound(prv_rel.shorter.clone()));
            }
        }
        Ok(())
    }

    pub fn outlives(&self, l: &Ident, s: &Ident) -> CtxResult<()> {
        if self.ctx.iter().any(|entry| match entry {
            KindingCtxEntry::PrvRel(PrvRel { longer, shorter }) => longer == l && shorter == s,
            _ => false,
        }) {
            Ok(())
        } else {
            Err(CtxError::OutlRelNotDefined(l.clone(), s.clone()))
        }
    }
}

#[derive(Debug, Clone)]
pub(super) struct GlobalCtx {
    funs: HashMap<String, TypeScheme>,
    structs: HashMap<String, StructDef>,
    traits: HashMap<String, TraitDef>,
    pub theta: ConstraintEnv,
}


fn check_unique_names<'a, T: 'a + std::hash::Hash + Eq + ToString, I: std::iter::ExactSizeIterator<Item=&'a T>>(names: I, errs: &mut Vec<CtxError>) {
    let mut names_set = HashSet::with_capacity(names.len());
    names.for_each(|name|
        if names_set.insert(name) {
            errs.push(CtxError::MultipleDefinedParam(name.to_string()))
    })
}

impl GlobalCtx {
    pub fn new() -> Self {
        GlobalCtx {
            funs: HashMap::new(),
            structs: HashMap::new(),
            traits: HashMap::new(),
            theta: ConstraintEnv::new(),
        }
    }

    pub fn append_fun_decls(mut self, fun_decls: &[(&str, TypeScheme)]) -> Self {
        self.funs.extend(
            fun_decls
                .iter()
                .map(|(name, ty)| (String::from(*name), ty.clone())),
        );
        self
    }

    pub fn append_from_item_def(&mut self, item_defs: &[Item]) -> Vec::<CtxError> {
        let mut impl_defs_names: HashSet<(Ty, String)> = HashSet::new();

        item_defs.iter().fold(
        Vec::<CtxError>::new(),
        |mut errs, item_def| {
            match item_def {
                Item::FunDef(fun_def) => {
                    let old_val = self.funs.insert(fun_def.name.clone(), fun_def.ty());
                    if old_val.is_some() {
                        errs.push(CtxError::MultipleDefinedGlobalFuns(fun_def.name.clone()));
                    }
                    check_unique_names(fun_def.generic_params.iter().map(|gen| &gen.ident.name), &mut errs);
                    check_unique_names(fun_def.param_decls.iter().map(|fun_param| &fun_param.ident.name), &mut errs);
                },
                Item::StructDef(struct_def) => {
                    let old_val = self.structs.insert(struct_def.name.clone(), struct_def.clone());
                    if old_val.is_some() {
                        errs.push(CtxError::MultipleDefinedStructs(struct_def.name.clone()));
                    }
                    check_unique_names(struct_def.generic_params.iter().map(|gen| &gen.ident.name), &mut errs);
                    check_unique_names(struct_def.decls.iter().map(|decl| &decl.name), &mut errs);
                },
                Item::ImplDef(impl_def) => {
                    //TODO check also names of associated items
                    check_unique_names(impl_def.generic_params.iter().map(|gen| &gen.ident.name), &mut errs);
                    //TODO associated items
                    if let Some(trait_impl) = &impl_def.trait_impl {
                        self.theta.append_constraint(&ConstraintScheme {
                            generics: impl_def.generic_params.clone(),
                            implican: impl_def.conditions.clone(),
                            implied: WhereClauseItem {
                                param: impl_def.ty.clone(),
                                trait_bound: trait_impl.clone() } });

                        if !impl_defs_names.insert((impl_def.ty.clone(), trait_impl.name.clone())) {
                            errs.push(CtxError::MultipleDefinedImplsForTrait(impl_def.ty.clone(), trait_impl.name.clone()));
                        }
                    }
                },
                Item::TraitDef(trait_def) => {
                    self.append_trait_def(&trait_def, &mut errs);
                },
            }
            errs
        })
    }

    fn append_trait_def(&mut self, t_def: &TraitDef, errs: &mut Vec<CtxError>) {
        if self.traits.insert(t_def.name.clone(), t_def.clone()).is_some() {
            errs.push(CtxError::MultipleDefinedTraits(t_def.name.clone()));
        } else {
            //TODO check also names of associated items
            check_unique_names(t_def.generic_params.iter().map(|gen| &gen.ident.name), errs);

            let self_ident = Ident::new("Self");
            let self_generic = IdentKinded::new(&self_ident, Kind::Ty);
            let self_ty = Ty::new(TyKind::Ident(self_ident.clone()));

            let mut generics_tdef = Vec::with_capacity(t_def.generic_params.len() + 1);
            generics_tdef.push(self_generic.clone());
            generics_tdef.extend(t_def.generic_params.clone());
            let trait_mono_type = TraitMonoType {
                name: t_def.name.clone(),
                generics: t_def.generic_params.iter().map(|gen| gen.arg_kinded()).collect() };
            let self_impl_trait =
                WhereClauseItem {
                    param: self_ty.clone(),
                    trait_bound: trait_mono_type };

            t_def.decls.iter()
                .for_each(|ass_item|
                    match ass_item {
                        AssociatedItem::FunDef(_) |
                        AssociatedItem::FunDecl(_) => {
                            let (ty, name) = 
                                match ass_item {
                                    AssociatedItem::FunDef(fun_def) => (fun_def.ty(), fun_def.name.clone()),
                                    AssociatedItem::FunDecl(fun_decl) => (fun_decl.ty(), fun_decl.name.clone()),
                                    _ => panic!("This cannot happen"),
                                };

                            if let TyKind::Fn(args, exec, ret_ty) = ty.mono_ty.ty {
                                let mut generics = Vec::with_capacity(generics_tdef.len() + ty.generic_params.len());
                                generics.extend(generics_tdef.clone());
                                generics.extend(ty.generic_params.clone());
                                let mut conditions = Vec::with_capacity(ty.conditions.len() + 1);
                                conditions.push(self_impl_trait.clone());
                                conditions.extend(ty.conditions.clone());

                                let ty =
                                    TypeScheme {
                                        generic_params: generics,
                                        conditions,
                                        mono_ty: Ty::new(TyKind::Fn(args, exec, ret_ty))
                                    };
                                if self.funs.insert(name, ty).is_some() {
                                    errs.push(CtxError::MultipleDefinedTraits(t_def.name.clone()))
                                }
                            } else {
                                panic!("FunDef without FunType!");
                            }},
                        AssociatedItem::ConstItem(_, _, _) => unimplemented!("TODO"),  
                    });

            let implican = vec![self_impl_trait];
            t_def.supertraits_constraints().iter().for_each(|supertrait_cons| 
                self.theta.append_constraint(&ConstraintScheme{ generics: generics_tdef.clone(), implican: implican.clone(), implied: supertrait_cons.clone() })
            );
        }
    }

    pub fn fun_ty_by_ident(&self, ident: &Ident) -> CtxResult<&TypeScheme> {
        match self.funs.get(&ident.name) { 
            Some(ty) => Ok(ty),
            None => Err(CtxError::IdentNotFound(ident.clone())),
        }
    }

    pub fn trait_ty_by_name(&self, name: &String) -> CtxResult<&TraitDef> {
        match self.traits.get(name) {
            Some(ty) => Ok(ty),
            None => Err(CtxError::TraitNotFound(name.clone())),
        }
    }

    pub fn struct_by_name(&self, name: &String) -> CtxResult<&StructDef> {
        match self.structs.get(name) {
            Some(ty) => Ok(ty),
            None => Err(CtxError::StructNotFound(name.clone())),
        }
    }
}

#[test]
fn test_kill_place_ident() {
    let mut ty_ctx = TyCtx::new();
    let x = IdentTyped::new(
        Ident::new("x"),
        Ty::new(TyKind::Data(DataTy::new(DataTyKind::Scalar(ScalarTy::I32)))),
        Mutability::Const,
    );
    let place = internal::Place::new(x.ident.clone(), vec![]);
    ty_ctx = ty_ctx.append_ident_typed(x);
    ty_ctx = ty_ctx.kill_place(&place);
    assert!(matches!(
        ty_ctx.idents_typed().next().unwrap().ty.ty,
        TyKind::Data(DataTy {
            dty: DataTyKind::Dead(_),
            ..
        })
    ));
}
