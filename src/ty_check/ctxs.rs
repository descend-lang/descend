use crate::ast::internal::{Frame, FrameEntry, IdentTyped, Loan, PrvMapping};
use crate::ast::utils::fresh_name;
use crate::ast::*;
use crate::ty_check::constraint_check::*;
use crate::ty_check::error::CtxError;
use crate::ty_check::proj_elem_ty;
use std::collections::{HashMap, HashSet};

use super::unify::{constrain, ConstrainMap, Constrainable};
use super::TyResult;

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

    pub(crate) fn substitute(&mut self, constr_map: &ConstrainMap) {
        self.idents_typed_mut()
            .for_each(|ident_typed| ident_typed.ty.substitute(constr_map))
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
                    dty: d::SplitThreadHierchy(_, _),
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
                            pl.clone().push(&ProjEntry::TupleAccess(index)),
                            Ty::new(TyKind::Data(proj_ty.clone())),
                        );
                        place_frame.append(&mut exploded_index);
                    }
                    place_frame
                }
                TyKind::Data(DataTy {
                    dty: d::Struct(struct_ty),
                    ..
                }) => {
                    let mut place_frame = vec![(pl.clone(), ty.clone())];
                    struct_ty.struct_fields.iter().for_each(|field| {
                        let mut exploded_index = explode(
                            pl.clone()
                                .push(&ProjEntry::StructAccess(field.name.clone())),
                            Ty::new(TyKind::Data(field.dty.clone())),
                        );
                        place_frame.append(&mut exploded_index);
                    });
                    place_frame
                }
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

    pub fn place_ty(&self, place: &internal::Place) -> TyResult<Ty> {
        let ident_ty = self.ty_of_ident(&place.ident)?;
        place
            .path
            .iter()
            .try_fold(ident_ty.clone(), |res, path_entry| {
                proj_elem_ty(&res, path_entry)
            })
    }

    pub fn set_place_ty(mut self, pl: &internal::Place, pl_ty: Ty) -> Self {
        fn set_ty_for_path_in_ty(orig_ty: Ty, path: &[ProjEntry], part_ty: Ty) -> Ty {
            if path.is_empty() {
                return part_ty;
            }

            let projentry = path.first().unwrap();
            match (orig_ty.ty, projentry) {
                (
                    TyKind::Data(DataTy {
                        dty: DataTyKind::Tuple(mut elem_tys),
                        ..
                    }),
                    ProjEntry::TupleAccess(idx),
                ) => {
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
                (
                    TyKind::Data(DataTy {
                        dty: DataTyKind::Struct(mut struct_ty),
                        ..
                    }),
                    ProjEntry::StructAccess(attr_name),
                ) => {
                    *struct_ty.attribute_dty_mut(attr_name).unwrap() = if let TyKind::Data(dty) =
                        set_ty_for_path_in_ty(
                            Ty::new(TyKind::Data(
                                struct_ty.attribute_dty(attr_name).unwrap().clone(),
                            )),
                            &path[1..],
                            part_ty,
                        )
                        .ty
                    {
                        dty
                    } else {
                        panic!("Trying create non-data type as part of data type.")
                    };

                    Ty::new(TyKind::Data(DataTy::new(DataTyKind::Struct(struct_ty))))
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
pub(crate) struct KindCtx {
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

#[derive(Debug)]
pub(super) struct GlobalCtx {
    funs: HashMap<FunctionName, TypeScheme>,
    structs: HashMap<String, StructDecl>,
    traits: HashMap<String, TraitDef>,
}

/// Check if all passed names are pairwise different
fn check_unique_names<
    'a,
    T: 'a + std::hash::Hash + Eq + ToString,
    I: std::iter::ExactSizeIterator<Item = &'a T>,
>(
    names: I,
    errs: &mut Vec<CtxError>,
) {
    let mut names_set = HashSet::with_capacity(names.len());
    names.for_each(|name| {
        if !names_set.insert(name) {
            errs.push(CtxError::MultipleDefinedItems(name.to_string()))
        }
    })
}

impl GlobalCtx {
    pub fn new() -> Self {
        GlobalCtx {
            funs: HashMap::new(),
            structs: HashMap::new(),
            traits: HashMap::new(),
        }
    }

    /// Append predefined function declarations
    pub fn append_fun_decls<'a, I>(mut self, fun_decls: I) -> Self
    where
        I: Iterator<Item = (&'a str, TypeScheme)>,
    {
        self.funs.extend(
            fun_decls.map(|(name, fun_ty_scheme)| (FunctionName::global_fun(name), fun_ty_scheme)),
        );
        self
    }

    /// Append item definitions to context and append from item definitions
    /// generated constraint-scheme to `constraint_env`
    pub fn append_item_defs(
        &mut self,
        item_defs: &[Item],
        constraint_env: &mut ConstraintEnv,
    ) -> Vec<CtxError> {
        // HashSet with all datatypes of an impl and corresponding name of implemented trait
        // This is used to make sure there are no duplicate implementations of the same trait for the same datatype
        let mut impl_defs_names: HashSet<(DataTy, String)> = HashSet::new();

        // Append every single item
        item_defs
            .iter()
            .fold(Vec::<CtxError>::new(), |mut errs, item_def| {
                match item_def {
                    Item::FunDef(fun_def) => self.append_fun(
                        FunctionName::global_fun(&fun_def.name),
                        fun_def.ty(),
                        &fun_def.param_decls,
                        &mut errs,
                    ),
                    Item::StructDecl(struct_decl) => {
                        // Insert this struct in context
                        let old_val = self
                            .structs
                            .insert(struct_decl.name.clone(), struct_decl.clone());
                        // Make sure there are not multiple structs with the same name
                        if old_val.is_some() {
                            errs.push(CtxError::MultipleDefinedStructs(struct_decl.name.clone()));
                        }
                        // Check also uniqueness of names of generic params and struct_fields
                        check_unique_names(
                            struct_decl.generic_params.iter().map(|gen| &gen.ident.name),
                            &mut errs,
                        );
                        check_unique_names(
                            struct_decl.struct_fields.iter().map(|decl| &decl.name),
                            &mut errs,
                        );
                    }
                    Item::ImplDef(impl_def) => {
                        // Check uniqueness of names of generic params and associated items
                        check_unique_names(
                            impl_def.generic_params.iter().map(|gen| &gen.ident.name),
                            &mut errs,
                        );
                        check_unique_names(
                            impl_def.ass_items.iter().map(|decl| match decl {
                                AssociatedItem::FunDef(fun_def) => &fun_def.name,
                                AssociatedItem::ConstItem(name, _, _) => name,
                                AssociatedItem::FunDecl(fun_decl) => &fun_decl.name,
                            }),
                            &mut errs,
                        );
                        // If this impl implements a trait
                        // Types of functions are not needed in the context because
                        // the corresponding trait already adds relevant function types
                        if let Some(trait_impl) = &impl_def.trait_impl {
                            constraint_env.append_constraint_scheme(&ConstraintScheme {
                                generics: impl_def.generic_params.clone(),
                                implican: impl_def.constraints.clone(),
                                implied: Constraint {
                                    param: impl_def.dty.clone(),
                                    trait_bound: trait_impl.clone(),
                                },
                            });

                            if !impl_defs_names
                                .insert((impl_def.dty.clone(), trait_impl.name.clone()))
                            {
                                errs.push(CtxError::MultipleDefinedImplsForTrait {
                                    trait_name: trait_impl.name.clone(),
                                    impl_dty: impl_def.ty(),
                                });
                            }
                        }
                        // If this impl does not implement a trait
                        else {
                            impl_def.ass_items.iter().for_each(|decl| match decl {
                                AssociatedItem::FunDef(fun_def) => {
                                    let TypeScheme {
                                        generic_params,
                                        constraints,
                                        mono_ty,
                                    } = fun_def.ty();
                                    // Add generic params and constraints of the impl to the typescheme of the function
                                    let extended_fun_ty_scheme = TypeScheme {
                                        generic_params: impl_def
                                            .generic_params
                                            .clone()
                                            .into_iter()
                                            .chain(generic_params.into_iter())
                                            .collect(),
                                        constraints: impl_def
                                            .constraints
                                            .clone()
                                            .into_iter()
                                            .chain(constraints.into_iter())
                                            .collect(),
                                        mono_ty,
                                    };

                                    // Insert this function in context
                                    self.append_fun(
                                        FunctionName::from_impl(&fun_def.name, impl_def),
                                        extended_fun_ty_scheme,
                                        &fun_def.param_decls,
                                        &mut errs,
                                    )
                                }
                                AssociatedItem::ConstItem(_, _, _) => todo!("TODO"),
                                // Function declarations are not allowed. Some error will be thrown in ty_check
                                AssociatedItem::FunDecl(_) => (),
                            });
                        }
                    }
                    Item::TraitDef(trait_def) => {
                        self.append_trait_def(&trait_def, &mut errs, constraint_env)
                    }
                }
                errs
            })
    }

    /// Append a function
    /// * `fun_name` - FunctionName of the function
    /// * `fun_ty_scheme` - type-scheme of the function
    /// * `fun_params` - parameter declarations which are checked for name conflicts
    /// * `errs` - vector where errors which occur are appended
    fn append_fun(
        &mut self,
        fun_name: FunctionName,
        fun_ty_scheme: TypeScheme,
        fun_params: &Vec<ParamDecl>,
        errs: &mut Vec<CtxError>,
    ) {
        // Check uniqueness of names of generic params and function parameter
        check_unique_names(
            fun_ty_scheme
                .generic_params
                .iter()
                .map(|gen| &gen.ident.name),
            errs,
        );
        check_unique_names(
            fun_params.iter().map(|fun_param| &fun_param.ident.name),
            errs,
        );
        // Insert typescheme of function in context
        let old_val = self.funs.insert(fun_name.clone(), fun_ty_scheme);
        // Make sure there are not multiple functions with the same name
        if old_val.is_some() {
            errs.push(CtxError::MultipleDefinedFunctions(fun_name));
        }
    }

    /// Append a trait definition
    fn append_trait_def(
        &mut self,
        t_def: &TraitDef,
        errs: &mut Vec<CtxError>,
        constraint_env: &mut ConstraintEnv,
    ) {
        // Insert trait in context
        let old_val = self.traits.insert(t_def.name.clone(), t_def.clone());
        // Make sure there are not multiple traits with the same name
        if old_val.is_some() {
            errs.push(CtxError::MultipleDefinedTraits(t_def.name.clone()));
        }
        // Add trait-functions to context
        else {
            // Check uniqueness of names of generic params and associated items
            check_unique_names(t_def.generic_params.iter().map(|gen| &gen.ident.name), errs);
            check_unique_names(
                t_def.ass_items.iter().map(|decl| match decl {
                    AssociatedItem::FunDef(fun_def) => &fun_def.name,
                    AssociatedItem::ConstItem(name, _, _) => name,
                    AssociatedItem::FunDecl(fun_decl) => &fun_decl.name,
                }),
                errs,
            );

            let self_ident = Ident::new("Self");
            let self_generic = IdentKinded::new(&self_ident, Kind::DataTy);
            let self_ty = DataTy::new(DataTyKind::Ident(self_ident.clone()));

            // Create a vector with all generics of the trait inclusive the implicit generic "Self"
            let mut generics_tdef = Vec::with_capacity(t_def.generic_params.len() + 1);
            generics_tdef.push(self_generic.clone());
            generics_tdef.extend(t_def.generic_params.clone());
            // Create a TraitMonoType with identifiers with same names as generic params as generic arguments
            let trait_mono_type = TraitMonoType {
                name: t_def.name.clone(),
                generic_args: t_def
                    .generic_params
                    .iter()
                    .map(|gen| gen.arg_kinded_implicit())
                    .collect(),
            };
            // This is the constraint "Self impls this trait"
            let self_impl_trait = Constraint {
                param: self_ty.clone(),
                trait_bound: trait_mono_type,
            };

            // Insert every associated item
            t_def.ass_items.iter().for_each(|ass_item| match ass_item {
                AssociatedItem::FunDef(_) | AssociatedItem::FunDecl(_) => {
                    // Function type-scheme and name
                    let (ty, name) = match ass_item {
                        AssociatedItem::FunDef(fun_def) => (fun_def.ty(), fun_def.name.clone()),
                        AssociatedItem::FunDecl(fun_decl) => (fun_decl.ty(), fun_decl.name.clone()),
                        _ => panic!("This cannot happen"),
                    };

                    if let TyKind::Fn(args, exec, ret_ty) = ty.mono_ty.ty {
                        // Vector with all generics of trait_definition and all generics of the function
                        let mut generic_params =
                            Vec::with_capacity(generics_tdef.len() + ty.generic_params.len());
                        generic_params.extend(generics_tdef.clone());
                        generic_params.extend(ty.generic_params.clone());
                        // Vector with all constraints of trait_definition and all constraints of the function
                        let mut constraints = Vec::with_capacity(ty.constraints.len() + 1);
                        constraints.push(self_impl_trait.clone());
                        constraints.extend(ty.constraints.clone());

                        // Create extended typescheme of this function
                        let extended_ty_scheme = TypeScheme {
                            generic_params,
                            constraints,
                            mono_ty: Ty::new(TyKind::Fn(args, exec, ret_ty)),
                        };
                        // Insert it in global context and make sure there are not multiple functions with the same name
                        if self
                            .funs
                            .insert(FunctionName::from_trait(&name, t_def), extended_ty_scheme)
                            .is_some()
                        {
                            errs.push(CtxError::MultipleDefinedFunctions(
                                FunctionName::from_trait(&name, t_def),
                            ))
                        }
                    } else {
                        panic!("FunDef without FunType!");
                    }
                }
                AssociatedItem::ConstItem(_, _, _) => unimplemented!("TODO"),
            });

            // Add constraint_schemes corresponding to the supertraits of this trait to the context
            let self_impl_trait = vec![self_impl_trait];
            t_def
                .supertraits_constraints()
                .iter()
                // for every supertrait constraint "Self implements supertrait X"
                .for_each(|supertrait_cons| {
                    // add a constraint-scheme of the form:
                    // \forall generics_tdef: if Self implements this trait => Self also implements supertrait X
                    constraint_env.append_constraint_scheme(&ConstraintScheme {
                        generics: generics_tdef.clone(),
                        implican: self_impl_trait.clone(),
                        implied: supertrait_cons.clone(),
                    })
                });
        }
    }

    /// Get the typescheme of a function by FunctionName. <br>
    /// Panics if the context does not contain this a function with this name
    pub fn fun_ty_by_name(&self, name: FunctionName) -> &TypeScheme {
        match self.funs.get(&name) {
            Some(ty) => ty,
            None => panic!("function {:#?} not found in context", name),
        }
    }

    /// Get a typescheme of a function by a ident and a function kind
    pub fn fun_ty_by_ident(
        &self,
        ident: &Ident,
        fun_kind: &FunctionKind,
    ) -> CtxResult<&TypeScheme> {
        let function_name = FunctionName {
            name: ident.name.clone(),
            fun_kind: fun_kind.clone(),
        };
        match self.funs.get(&function_name) {
            Some(ty) => Ok(ty),
            None => Err(CtxError::IdentNotFound(ident.clone())),
        }
    }

    /// Get a trait-definition by its name
    pub fn trait_ty_by_name(&self, name: &String) -> CtxResult<&TraitDef> {
        match self.traits.get(name) {
            Some(ty) => Ok(ty),
            None => Err(CtxError::TraitNotFound(name.clone())),
        }
    }

    /// Get a struct-declaration by its name
    pub fn struct_by_name(&self, name: &String) -> CtxResult<&StructDecl> {
        match self.structs.get(name) {
            Some(ty) => Ok(ty),
            None => Err(CtxError::StructNotFound(name.clone())),
        }
    }

    /// Get a FunctionName by the name of the function and the datatype of corresponding impl. <br>
    /// If no suitable function for `dty` is found this method also tries to search a suitable
    /// function for `dty_alternative`. If a function for `dty_alternative` is found, `dty`
    /// is set to `dty_alternative`. <br>
    /// This function does not add constraints on implicit identifiers or return a substitution with
    /// inferred types. This happens in function application when unify types of arguments
    /// and expected type of arguments. <br>
    pub fn fun_name_by_dty(
        &self,
        constraint_env: &ConstraintEnv,
        implicit_ident_cons: &IdentConstraints,
        fun_name: &String,
        dty: &mut DataTy,
        dty_alternative: Option<DataTy>,
    ) -> CtxResult<&FunctionName> {
        // Ty of impl of the searched function
        let ty = Ty::new(TyKind::Data(dty.clone()));
        let ty_alt = if dty_alternative.is_some() {
            Some(Ty::new(TyKind::Data(
                dty_alternative.as_ref().unwrap().clone(),
            )))
        } else {
            None
        };

        // Save result (if found) in this variable
        let mut result = None;
        // Work on a copy of "implicit_ident_cons" to avoid side effects when using constraint_check
        let mut implicit_ident_cons_clone = implicit_ident_cons.clone();

        // Search after a function suitable for `ty` or `dereferenced_ty` simultaneously
        enum Found {
            NotFound,
            FoundDtyAlt,
            MultipleFoundDtyAlt,
            FoundDty,
            MultipleFoundDty,
        }
        // Returns if we search for a function suitable for `dereferenced_dty`
        let search_deref_dty = |found: &Found| {
            dty_alternative.is_some()
                && (matches!(found, Found::NotFound) || matches!(found, Found::FoundDtyAlt))
        };
        // Return the new value for `found` after a suitable function for `dty` is found
        let found_dty = |found| match found {
            Found::NotFound => Found::FoundDty,
            Found::FoundDtyAlt => Found::FoundDty,
            Found::MultipleFoundDtyAlt => Found::FoundDty,
            Found::FoundDty => Found::MultipleFoundDty,
            Found::MultipleFoundDty => Found::MultipleFoundDty,
        };
        // Return the new value for `found` after a suitable function for `dereferenced_dty` is found
        let found_deref_dty = |found| match found {
            Found::NotFound => Found::FoundDtyAlt,
            Found::FoundDtyAlt => Found::MultipleFoundDtyAlt,
            f => f,
        };

        // Search in all suitable functions in context
        let found = self
            .funs
            .keys()
            .fold(Found::NotFound, |mut found, fun_name_candidate| {
                // Make sure the candidate-function have the same name like the searched function
                if fun_name_candidate.name == *fun_name && !matches!(found, Found::MultipleFoundDty)
                {
                    match &fun_name_candidate.fun_kind {
                        // if the function_kind of the candidate-function references an impl
                        FunctionKind::ImplFun(impl_dty_candidate, _) => {
                            // if `impl_dty_candidate` and `ty` can be unified, this is the searched function
                            if let Ok(subs) = constrain(&ty, &impl_dty_candidate.mono_ty) {
                                if implicit_ident_cons
                                    .constraint_subs(constraint_env, &subs.0)
                                    .is_ok()
                                {
                                    result = Some(fun_name_candidate);
                                    found = found_dty(found);
                                }
                            }
                            // For `dereferenced_ty`
                            if search_deref_dty(&found) {
                                if let Ok(subs) =
                                    constrain(ty_alt.as_ref().unwrap(), &impl_dty_candidate.mono_ty)
                                {
                                    if implicit_ident_cons
                                        .constraint_subs(constraint_env, &subs.0)
                                        .is_ok()
                                    {
                                        result = Some(fun_name_candidate);
                                        found = found_deref_dty(found);
                                    }
                                }
                            }
                        }
                        // if the function_kind of the candidate-function references a trait
                        FunctionKind::TraitFun(trait_name) => {
                            // if `ty` implements the trait
                            if self
                                .dty_impls_trait(
                                    constraint_env,
                                    &mut implicit_ident_cons_clone,
                                    dty.clone(),
                                    trait_name,
                                )
                                .is_ok()
                            {
                                result = Some(fun_name_candidate);
                                // Reset `implicit_ident_cons_clone` to avoid side effects
                                implicit_ident_cons_clone = implicit_ident_cons.clone();

                                found = found_dty(found);
                            }
                            // For `dereferenced_ty`
                            if search_deref_dty(&found) {
                                if self
                                    .dty_impls_trait(
                                        constraint_env,
                                        &mut implicit_ident_cons_clone,
                                        dty_alternative.as_ref().unwrap().clone(),
                                        trait_name,
                                    )
                                    .is_ok()
                                {
                                    result = Some(fun_name_candidate);
                                    // Reset `implicit_ident_cons_clone` to avoid side effects
                                    implicit_ident_cons_clone = implicit_ident_cons.clone();

                                    found = found_deref_dty(found);
                                }
                            }
                        }
                        // if this is not a impl- or trait-function, its not the searched function
                        _ => (),
                    }
                }
                found
            });

        match found {
            // if there are multiple possible functions that meets the search criteria
            Found::MultipleFoundDty | Found::MultipleFoundDtyAlt => {
                Err(CtxError::AmbiguousFunctionCall {
                    function_name: fun_name.clone(),
                    impl_dty: dty.clone(),
                })
            }
            // if there if no function that meets the search criteria
            Found::NotFound => Err(CtxError::IdentNotFound(Ident::new(fun_name))),
            // if there is exactly one function that meets the search criteria
            Found::FoundDty => Ok(result.unwrap()),
            Found::FoundDtyAlt => {
                *dty = dty_alternative.unwrap();
                Ok(result.unwrap())
            }
        }
    }

    /// Check if a datatype implements a trait
    fn dty_impls_trait(
        &self,
        constraint_env: &ConstraintEnv,
        implicit_ident_cons: &mut IdentConstraints,
        dty: DataTy,
        trait_name: &String,
    ) -> Result<ConstrainMap, ()> {
        // Get the trait_definition from the context
        let trait_def = self.trait_ty_by_name(trait_name).unwrap();

        // ArgKinded-Identifier for every kinded identifier of the trait
        let trait_def_generic_args = trait_def
            .generic_params
            .iter()
            .map(|k_ident| {
                let mut k_ident = k_ident.clone();
                k_ident.ident.name = fresh_name(&k_ident.ident.name);
                k_ident.arg_kinded_implicit()
            })
            .collect::<Vec<_>>();

        // Constraint: 'dty' implements the `trait_name` with `trait_def_generic_args` as trait-arguments
        let c_ident_constraint = Constraint {
            param: dty,
            trait_bound: TraitMonoType {
                name: trait_name.clone(),
                generic_args: trait_def_generic_args,
            },
        };

        // Check if the constraint if fulfilled
        constraint_env.check_constraint(&c_ident_constraint, implicit_ident_cons)
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
