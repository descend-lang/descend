use crate::ast::internal::{ExecMapping, Frame, FrameEntry, IdentTyped, Loan, PrvMapping};
use crate::ast::*;
use crate::ty_check::error::CtxError;
use crate::ty_check::pre_decl;
use std::collections::hash_map::Iter;
use std::collections::{HashMap, HashSet};

// TODO introduce proper struct
pub(super) type TypedPlace = (internal::Place, DataTy);

// #[derive(PartialEq, Eq, Debug, Clone)]
// struct ScopedCtx<T> {
//     scopes: Vec<T>,
// }
//
// impl<T> ScopedCtx<T> {
//     fn new() -> Self {
//         ScopedCtx { scopes: vec![] }
//     }
//
//     fn push(&mut self, v: T) -> &mut Self {
//         self.last_scope_mut().push(v);
//         self
//     }
//
//     fn push_scope(&mut self, s: Vec<T>) -> &mut Self {
//         self.scopes.push(s);
//         self
//     }
//
//     fn push_empty_scope(&mut self) -> &mut Self {
//         self.scopes.push(vec![]);
//         self
//     }
//
//     fn pop_scope(&mut self) -> Vec<T> {
//         self.scopes
//             .pop()
//             .expect("It should never be the case that there is no scope.")
//     }
//
//     pub fn is_empty(&self) -> bool {
//         if self.scopes.len() == 1 {
//             self.scopes
//                 .first()
//                 .expect("It should never be the case that there is no scope.")
//                 .is_empty()
//         } else {
//             false
//         }
//     }
//
//     fn last_scope_mut(&mut self) -> &mut Vec<T> {
//         self.scopes
//             .iter_mut()
//             .last()
//             .expect("It should never be the case that there is no scope.")
//     }
// }

#[derive(PartialEq, Eq, Debug, Clone)]
pub(super) struct TyCtx {
    frames: Vec<Frame>,
}

impl TyCtx {
    pub fn new() -> Self {
        TyCtx {
            frames: vec![Frame::new()],
        }
    }

    pub fn get_exec_expr(&self, ident: &Ident) -> CtxResult<&ExecExpr> {
        let exec_expr = self.flat_bindings().rev().find_map(|entry| match entry {
            FrameEntry::ExecMapping(em) if &em.ident == ident => Some(&em.exec_expr),
            _ => None,
        });
        match exec_expr {
            Some(exec) => Ok(exec),
            None => Err(CtxError::IdentNotFound(ident.clone())),
        }
    }
    //
    // pub fn last_frame(&self) -> &Frame {
    //     self.frames.last().unwrap()
    // }

    pub fn last_frame_mut(&mut self) -> &mut Frame {
        self.frames.last_mut().unwrap()
    }

    pub fn flat_bindings_mut(&mut self) -> impl DoubleEndedIterator<Item = &'_ mut FrameEntry> {
        self.frames.iter_mut().flat_map(|frm| &mut frm.bindings)
    }

    pub fn flat_bindings(&self) -> impl DoubleEndedIterator<Item = &'_ FrameEntry> {
        self.frames.iter().flat_map(|frm| &frm.bindings)
    }

    pub fn push_empty_frame(&mut self) -> &mut Self {
        self.frames.push(Frame::new());
        self
    }

    pub fn push_frame(&mut self, frame: Frame) -> &mut Self {
        self.frames.push(frame);
        self
    }

    pub fn pop_frame(&mut self) -> Frame {
        self.frames.pop().expect("There must always be a scope.")
    }

    pub fn append_ident_typed(&mut self, id_typed: IdentTyped) -> &mut Self {
        self.last_frame_mut()
            .bindings
            .push(FrameEntry::Var(id_typed));
        self
    }

    pub fn append_exec_mapping(&mut self, ident: Ident, exec: ExecExpr) -> &mut Self {
        self.last_frame_mut()
            .bindings
            .push(FrameEntry::ExecMapping(ExecMapping::new(ident, exec)));
        self
    }

    pub fn append_prv_mapping(&mut self, prv_mapping: PrvMapping) -> &mut Self {
        self.last_frame_mut()
            .bindings
            .push(FrameEntry::PrvMapping(prv_mapping));
        self
    }

    fn idents_typed(&self) -> impl DoubleEndedIterator<Item = &'_ IdentTyped> {
        self.flat_bindings().filter_map(|fe| {
            if let FrameEntry::Var(ident_typed) = fe {
                Some(ident_typed)
            } else {
                None
            }
        })
    }

    fn idents_typed_mut(&mut self) -> impl DoubleEndedIterator<Item = &'_ mut IdentTyped> {
        self.flat_bindings_mut().filter_map(|fe| {
            if let FrameEntry::Var(ident_typed) = fe {
                Some(ident_typed)
            } else {
                None
            }
        })
    }

    pub(crate) fn prv_mappings(&self) -> impl DoubleEndedIterator<Item = &'_ PrvMapping> {
        self.flat_bindings().filter_map(|fe| {
            if let FrameEntry::PrvMapping(prv_mapping) = fe {
                Some(prv_mapping)
            } else {
                None
            }
        })
    }

    fn prv_mappings_mut(&mut self) -> impl DoubleEndedIterator<Item = &'_ mut PrvMapping> {
        self.flat_bindings_mut().filter_map(|fe| {
            if let FrameEntry::PrvMapping(prv_mapping) = fe {
                Some(prv_mapping)
            } else {
                None
            }
        })
    }

    pub fn update_loan_set(
        &mut self,
        prv_val_name: &str,
        loan_set: HashSet<Loan>,
    ) -> CtxResult<&mut Self> {
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

    pub fn extend_loans_for_prv<I>(&mut self, base: &str, extension: I) -> CtxResult<&mut TyCtx>
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
        if let Some(frm) = self.frames.last() {
            self.frames.len() == 1 && frm.bindings.is_empty()
        } else {
            false
        }
    }

    // ∀π:τ ∈ Γ
    pub fn all_places(&self) -> Vec<TypedPlace> {
        self.idents_typed()
            .filter_map(|IdentTyped { ident, ty, .. }| {
                if let TyKind::Data(dty) = &ty.ty {
                    Some(TyCtx::explode_places(ident, dty))
                } else {
                    None
                }
            })
            .flatten()
            .collect()
    }

    fn explode_places(ident: &Ident, dty: &DataTy) -> Vec<TypedPlace> {
        fn proj(mut pl: internal::Place, idx: usize) -> internal::Place {
            pl.path.push(idx);
            pl
        }

        fn explode(pl: internal::Place, dty: DataTy) -> Vec<TypedPlace> {
            use DataTyKind as d;

            match &dty.dty {
                d::Atomic(_)
                | d::Scalar(_)
                | d::Array(_, _)
                | d::ArrayShape(_, _)
                | d::At(_, _)
                | d::Ref(_)
                | d::RawPtr(_)
                | d::Ident(_)
                | d::Dead(_) => vec![(pl, dty.clone())],
                d::Tuple(tys) => {
                    let mut place_frame = vec![(pl.clone(), dty.clone())];
                    for (index, proj_ty) in tys.iter().enumerate() {
                        let mut exploded_index = explode(proj(pl.clone(), index), proj_ty.clone());
                        place_frame.append(&mut exploded_index);
                    }
                    place_frame
                }
            }
        }

        explode(internal::Place::new(ident.clone(), vec![]), dty.clone())
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

    pub fn contains(&self, ident: &Ident) -> bool {
        self.idents_typed().any(|i| i.ident.name == ident.name)
    }

    pub fn place_dty(&self, place: &internal::Place) -> CtxResult<DataTy> {
        fn proj_ty(dty: DataTy, path: &[usize]) -> CtxResult<DataTy> {
            let mut res_dty = dty;
            for n in path {
                match &res_dty.dty {
                    DataTyKind::Tuple(elem_tys) => {
                        if elem_tys.len() <= *n {
                            return Err(CtxError::IllegalProjection);
                        }
                        res_dty = elem_tys[*n].clone();
                    }
                    t => {
                        panic!(
                            "Trying to project element data type of a non tuple type:\n {:?}",
                            t
                        )
                    }
                }
            }
            Ok(res_dty)
        }
        let ident_ty = self.ty_of_ident(&place.ident)?;
        if let TyKind::Data(dty) = &ident_ty.ty {
            proj_ty(dty.as_ref().clone(), &place.path)
        } else {
            panic!("This place is not of a data type.")
        }
    }

    pub fn set_place_dty(&mut self, pl: &internal::Place, pl_ty: DataTy) -> &mut Self {
        fn set_dty_for_path_in_dty(orig_dty: DataTy, path: &[usize], part_dty: DataTy) -> DataTy {
            if path.is_empty() {
                return part_dty;
            }

            let idx = path.first().unwrap();
            match orig_dty.dty {
                DataTyKind::Tuple(mut elem_tys) => {
                    elem_tys[*idx] =
                        set_dty_for_path_in_dty(elem_tys[*idx].clone(), &path[1..], part_dty);
                    DataTy::new(DataTyKind::Tuple(elem_tys))
                }
                _ => panic!("Path not compatible with type."),
            }
        }

        let mut ident_typed = self
            .idents_typed_mut()
            .rev()
            .find(|ident_typed| ident_typed.ident == pl.ident)
            .unwrap();
        if let TyKind::Data(dty) = &ident_typed.ty.ty {
            let updated_dty = set_dty_for_path_in_dty(*dty.clone(), pl.path.as_slice(), pl_ty);
            ident_typed.ty = Ty::new(TyKind::Data(Box::new(updated_dty)));
            self
        } else {
            panic!("Trying to set data type for identifier without data type.")
        }
    }

    pub fn kill_place(&mut self, pl: &internal::Place) -> &mut Self {
        if let Ok(pl_dty) = self.place_dty(pl) {
            self.set_place_dty(pl, DataTy::new(DataTyKind::Dead(Box::new(pl_dty))))
        } else {
            panic!("Trying to kill the type of a place that doesn't exist.")
        }
    }

    pub fn garbage_collect_loans(&mut self) -> &mut Self {
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

    fn invalidate_prvs(&mut self, prv_names: Vec<String>) -> &mut Self {
        prv_names.iter().fold(self, |ty_ctx, prv| {
            ty_ctx
                // TODO simply delete the provenance?1
                .update_loan_set(prv.as_str(), HashSet::new())
                .unwrap()
        })
    }

    // Γ ▷- p = Γ′
    pub(super) fn without_reborrow_loans(&mut self, pl_expr: &PlaceExpr) -> &mut Self {
        for frame_entry in self.flat_bindings_mut() {
            if let FrameEntry::PrvMapping(PrvMapping { prv: _, loans }) = frame_entry {
                // FIXME not prefix_of but *x within p?
                // let without_reborrow: HashSet<Loan> = loans
                //     .iter()
                //     .filter_map(|loan| {
                //         // if !PlaceExpr::new(PlaceExprKind::Deref(Box::new(pl_expr.clone())))
                //         //     .prefix_of(&loan.place_expr)
                //         // {
                //         //     Some(loan.clone())
                //         // } else {
                //         //     None
                //         // }
                //         Some(loan)
                //     })
                //     .collect();
                // *loans = without_reborrow;
                ()
            }
        }
        self
    }
}

pub(super) struct AccessCtx {
    ctx: HashMap<ExecExpr, HashSet<Loan>>,
}

impl AccessCtx {
    pub fn new() -> Self {
        AccessCtx {
            ctx: HashMap::new(),
        }
    }

    pub fn insert(&mut self, exec: &ExecExpr, loans: HashSet<Loan>) {
        let new_loans = if let Some(old) = self.ctx.get(exec) {
            old.union(&loans).cloned().collect()
        } else {
            loans
        };
        self.ctx.insert(exec.clone(), new_loans);
    }

    pub fn iter(&self) -> Iter<ExecExpr, HashSet<Loan>> {
        self.ctx.iter()
    }

    pub fn clear_for(&mut self, exec: &ExecExpr) {
        let mut outer_accesses = HashSet::new();
        for (ex, accesses) in &self.ctx {
            if ex.is_sub_exec_of(exec) {
                let accs = accesses
                    .iter()
                    .filter_map(|acc| {
                        get_select_for(&ex, &acc.place_expr).map(|select| Loan {
                            own: acc.own,
                            place_expr: select,
                        })
                    })
                    .collect::<HashSet<_>>();
                outer_accesses.extend(accs);
            }
        }
        self.insert(exec, outer_accesses);
        self.ctx.retain(|ex, _| !ex.is_sub_exec_of(exec))
    }
}

fn get_select_for(exec: &ExecExpr, pl_expr: &PlaceExpr) -> Option<PlaceExpr> {
    match &pl_expr.pl_expr {
        PlaceExprKind::Select(ipl, sel_exec) if &**sel_exec == exec => Some(ipl.as_ref().clone()),
        PlaceExprKind::Select(ipl, _)
        | PlaceExprKind::View(ipl, _)
        | PlaceExprKind::Proj(ipl, _)
        | PlaceExprKind::Idx(ipl, _)
        | PlaceExprKind::Deref(ipl) => get_select_for(exec, ipl),
        PlaceExprKind::Ident(_) => None,
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
    ctx: Vec<Vec<KindingCtxEntry>>,
}

impl KindCtx {
    pub fn new() -> Self {
        KindCtx { ctx: vec![vec![]] }
    }

    pub fn gl_fun_kind_ctx(idents: Vec<IdentKinded>, prv_rels: Vec<PrvRel>) -> CtxResult<Self> {
        let mut kind_ctx: Self = KindCtx::new();
        kind_ctx.append_idents(idents);
        kind_ctx.append_prv_rels(prv_rels)?;
        Ok(kind_ctx)
    }

    pub fn push_empty_scope(&mut self) -> &mut Self {
        self.ctx.push(vec![]);
        self
    }

    pub fn drop_scope(&mut self) {
        self.ctx.pop();
    }

    pub fn append_idents<I: IntoIterator<Item = IdentKinded>>(&mut self, idents: I) -> &mut Self {
        let entries = idents.into_iter().map(KindingCtxEntry::Ident);
        for e in entries {
            self.ctx.last_mut().unwrap().push(e);
        }
        self
    }

    pub fn append_prv_rels<I: IntoIterator<Item = PrvRel> + Clone>(
        &mut self,
        prv_rels: I,
    ) -> CtxResult<&mut Self> {
        self.well_kinded_prv_rels(prv_rels.clone())?;
        for prv_rel in prv_rels {
            self.ctx
                .last_mut()
                .unwrap()
                .push(KindingCtxEntry::PrvRel(prv_rel));
        }
        Ok(self)
    }

    pub fn well_kinded_prv_rels<I: IntoIterator<Item = PrvRel>>(
        &self,
        prv_rels: I,
    ) -> CtxResult<()> {
        let mut prv_idents = self.get_idents(Kind::Provenance);
        for prv_rel in prv_rels.into_iter() {
            if !prv_idents.any(|prv_ident| &prv_rel.longer == prv_ident) {
                return Err(CtxError::PrvIdentNotFound(prv_rel.longer.clone()));
            }
            if !prv_idents.any(|prv_ident| &prv_rel.shorter == prv_ident) {
                return Err(CtxError::PrvIdentNotFound(prv_rel.shorter.clone()));
            }
        }
        Ok(())
    }

    pub fn get_idents(&self, kind: Kind) -> impl Iterator<Item = &Ident> {
        self.ctx.iter().flatten().filter_map(move |entry| {
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

    pub fn ident_of_kind_exists(&self, ident: &Ident, kind: Kind) -> bool {
        self.get_idents(kind).any(|id| ident == id)
    }

    pub fn outlives(&self, l: &Ident, s: &Ident) -> CtxResult<()> {
        if self.ctx.iter().flatten().any(|entry| match entry {
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
    items: HashMap<Box<str>, FnTy>,
}

impl GlobalCtx {
    pub fn from_iter<'a, I>(funs: I) -> Self
    where
        I: Iterator<Item = &'a FunDef>,
    {
        let mut gl_ctx = GlobalCtx {
            items: HashMap::new(),
        };
        Self::append_fun_decls(&mut gl_ctx, &pre_decl::fun_decls());
        gl_ctx
            .items
            .extend(funs.map(|fun_def| (fun_def.ident.name.clone(), fun_def.fn_ty())));
        gl_ctx
    }

    fn append_fun_decls(gl_ctx: &mut GlobalCtx, fun_decls: &[(&str, FnTy)]) {
        gl_ctx.items.extend(
            fun_decls
                .iter()
                .map(|(name, ty)| (String::from(*name).into_boxed_str(), ty.clone())),
        )
    }

    pub fn fn_ty_by_ident(&self, ident: &Ident) -> CtxResult<&FnTy> {
        match self.items.get(&ident.name) {
            Some(fn_ty) => Ok(fn_ty),
            None => Err(CtxError::IdentNotFound(ident.clone())),
        }
    }
}

#[test]
fn test_kill_place_ident() {
    let mut ty_ctx = TyCtx::new();
    let x = IdentTyped::new(
        Ident::new("x"),
        Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
            ScalarTy::I32,
        ))))),
        Mutability::Const,
        ExecExpr::new(ExecExprKind::new(BaseExec::Ident(Ident::new("exec")))),
    );
    let place = internal::Place::new(x.ident.clone(), vec![]);
    ty_ctx.append_ident_typed(x).kill_place(&place);
    assert!(matches!(
        ty_ctx.idents_typed().next().unwrap().ty.dty(),
        DataTy {
            dty: DataTyKind::Dead(_),
            ..
        }
    ));
}
