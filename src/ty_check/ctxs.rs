use crate::arena_ast::internal::{
    ExecMapping, Frame, FrameEntry, IdentTyped, Loan, PathElem, PrvMapping,
};
use crate::arena_ast::*;
use crate::ty_check::error::CtxError;
use bumpalo::collections::CollectIn;
use bumpalo::{collections::Vec as BumpVec, Bump};
use std::collections::HashSet;

// TODO introduce proper struct
pub(super) type TypedPlace<'a> = (internal::Place<'a>, DataTy<'a>);

#[derive(PartialEq, Eq, Debug, Clone)]
pub(super) struct TyCtx<'a> {
    frames: BumpVec<'a, Frame<'a>>,
}

impl<'a> TyCtx<'a> {
    pub fn new(arena: &'a Bump) -> Self {
        let mut frames = BumpVec::new_in(arena);
        frames.push(Frame::new_in(arena));
        TyCtx { frames }
    }

    pub fn get_exec_expr_for_exec_ident(&self, ident: &Ident<'a>) -> CtxResult<'a, &ExecExpr<'a>> {
        let exec_expr = self.flat_bindings().rev().find_map(|entry| match entry {
            FrameEntry::ExecMapping(em) if &em.ident == ident => Some(&em.exec_expr),
            _ => None,
        });
        match exec_expr {
            Some(exec) => Ok(exec),
            None => Err(CtxError::IdentNotFound(ident.clone())),
        }
    }

    pub fn last_frame_mut(&mut self) -> &mut Frame<'a> {
        self.frames.last_mut().unwrap()
    }

    fn flat_bindings(&self) -> impl DoubleEndedIterator<Item = &FrameEntry<'a>> {
        self.frames.iter().flat_map(|f| &f.bindings)
    }
    fn flat_bindings_mut(&mut self) -> impl DoubleEndedIterator<Item = &mut FrameEntry<'a>> {
        self.frames.iter_mut().flat_map(|f| &mut f.bindings)
    }

    pub fn push_empty_frame(&mut self, arena: &'a Bump) -> &mut Self {
        self.frames.push(Frame::new_in(arena));
        self
    }

    pub fn push_frame(&mut self, frame: Frame<'a>) -> &mut Self {
        self.frames.push(frame);
        self
    }

    pub fn pop_frame(&mut self) -> Frame<'a> {
        assert!(self.frames.len() > 1, "Cannot pop the last frame");
        self.frames.pop().unwrap()
    }

    pub fn append_ident_typed(&mut self, id_typed: IdentTyped<'a>) -> &mut Self {
        self.last_frame_mut()
            .bindings
            .push(FrameEntry::Var(id_typed));
        self
    }

    pub fn append_exec_mapping(&mut self, ident: Ident<'a>, exec: ExecExpr<'a>) -> &mut Self {
        self.last_frame_mut()
            .bindings
            .push(FrameEntry::ExecMapping(ExecMapping::new(ident, exec)));
        self
    }

    pub fn append_prv_mapping(&mut self, prv_mapping: PrvMapping<'a>) -> &mut Self {
        self.last_frame_mut()
            .bindings
            .push(FrameEntry::PrvMapping(prv_mapping));
        self
    }

    fn idents_typed(&self) -> impl DoubleEndedIterator<Item = &'_ IdentTyped<'a>> {
        self.flat_bindings().filter_map(|fe| {
            if let FrameEntry::Var(ident_typed) = fe {
                Some(ident_typed)
            } else {
                None
            }
        })
    }

    fn idents_typed_mut(&mut self) -> impl DoubleEndedIterator<Item = &'_ mut IdentTyped<'a>> {
        self.flat_bindings_mut().filter_map(|fe| {
            if let FrameEntry::Var(ident_typed) = fe {
                Some(ident_typed)
            } else {
                None
            }
        })
    }

    pub(crate) fn prv_mappings(&self) -> impl DoubleEndedIterator<Item = &'_ PrvMapping<'a>> {
        self.flat_bindings().filter_map(|fe| {
            if let FrameEntry::PrvMapping(prv_mapping) = fe {
                Some(prv_mapping)
            } else {
                None
            }
        })
    }

    fn prv_mappings_mut(&mut self) -> impl DoubleEndedIterator<Item = &'_ mut PrvMapping<'a>> {
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
        loan_set: HashSet<Loan<'a>>,
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

    pub fn extend_loans_for_prv<I>(
        &mut self,
        base: &str,
        extension: I,
    ) -> CtxResult<'a, &mut TyCtx<'a>>
    where
        I: IntoIterator<Item = Loan<'a>>,
    {
        let base_loans = self.loans_for_prv_mut(base)?;
        base_loans.extend(extension);
        Ok(self)
    }

    pub fn loans_in_prv(&self, prv_val_name: &str) -> CtxResult<'a, &HashSet<Loan<'a>>> {
        match self
            .prv_mappings()
            .rev()
            .find(|prv_mapping| prv_val_name == prv_mapping.prv)
        {
            Some(set) => Ok(&set.loans),
            None => Err(CtxError::PrvValueNotFound(prv_val_name.to_string())),
        }
    }

    pub fn loans_for_prv_mut(
        &mut self,
        prv_val_name: &str,
    ) -> CtxResult<'a, &mut HashSet<Loan<'a>>> {
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
    pub fn all_places(&self, arena: &'a Bump) -> BumpVec<'a, TypedPlace<'a>> {
        self.idents_typed()
            .filter_map(|IdentTyped { ident, ty, .. }| {
                if let TyKind::Data(dty) = &ty.ty {
                    Some(TyCtx::explode_places(ident, dty, arena))
                } else {
                    None
                }
            })
            .flatten()
            .collect_in(arena)
    }

    fn explode_places(
        ident: &Ident<'a>,
        dty: &DataTy<'a>,
        arena: &'a Bump,
    ) -> BumpVec<'a, TypedPlace<'a>> {
        fn proj<'a>(mut pl: internal::Place<'a>, idx: PathElem<'a>) -> internal::Place<'a> {
            pl.path.push(idx);
            pl
        }

        fn explode<'a>(
            pl: internal::Place<'a>,
            dty: DataTy<'a>,
            arena: &'a Bump,
        ) -> BumpVec<'a, TypedPlace<'a>> {
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
                | d::Dead(_) => BumpVec::from_iter_in([(pl.clone(), dty.clone())], arena), //vec![(pl, dty.clone())],
                d::Tuple(tys) => {
                    let mut place_frame = BumpVec::from_iter_in([(pl.clone(), dty.clone())], arena);
                    for (index, proj_ty) in tys.iter().enumerate() {
                        let mut exploded_index = explode(
                            proj(pl.clone(), PathElem::Proj(index)),
                            proj_ty.clone(),
                            arena,
                        );
                        place_frame.append(&mut exploded_index);
                    }
                    place_frame
                }
                d::Struct(sdecl) => {
                    let mut place_frame = BumpVec::from_iter_in([(pl.clone(), dty.clone())], arena);
                    for field in sdecl.fields.iter() {
                        let mut exploded_field = explode(
                            proj(
                                pl.clone(),
                                PathElem::FieldProj(arena.alloc(field.0.clone())),
                            ),
                            field.1.clone(),
                            arena,
                        );
                        place_frame.append(&mut exploded_field);
                    }
                    place_frame
                }
            }
        }

        explode(
            internal::Place::new(ident.clone(), BumpVec::new_in(arena)),
            dty.clone(),
            arena,
        )
    }

    pub fn ty_of_ident(&self, ident: &Ident<'a>) -> CtxResult<'a, &Ty<'a>> {
        Ok(&self.ident_ty(ident)?.ty)
    }

    pub fn ident_ty(&self, ident: &Ident<'a>) -> CtxResult<'a, &IdentTyped<'a>> {
        match self
            .idents_typed()
            .rev()
            .find(|id_ty| &id_ty.ident == ident)
        {
            Some(id) => Ok(id),
            None => Err(CtxError::IdentNotFound(ident.clone())),
        }
    }

    pub fn contains(&self, ident: &Ident<'a>) -> bool {
        self.idents_typed().any(|i| i.ident.name == ident.name)
    }

    pub fn place_dty(&self, place: &internal::Place<'a>) -> CtxResult<'a, DataTy<'a>> {
        fn proj_ty<'a>(dty: DataTy<'a>, path: &[PathElem<'a>]) -> CtxResult<'a, DataTy<'a>> {
            let mut res_dty = dty;
            for pe in path {
                match (&res_dty.dty, pe) {
                    (DataTyKind::Tuple(elem_tys), PathElem::Proj(n)) => {
                        if elem_tys.len() <= *n {
                            return Err(CtxError::IllegalProjection);
                        }
                        res_dty = elem_tys[*n].clone();
                    }
                    (DataTyKind::Struct(struct_decl), PathElem::FieldProj(ident)) => {
                        res_dty = if let Some(field) =
                            struct_decl.fields.iter().find(|f| &f.0 == *ident)
                        {
                            field.1.clone()
                        } else {
                            panic!("Did not find field `{}` in struct.", ident.name)
                        }
                    }
                    t => {
                        panic!(
                            "Trying to project element data type of a non record type or\
                                wrong projection:\n {:?}",
                            t
                        )
                    }
                }
            }
            Ok(res_dty)
        }
        let ident_ty = self.ty_of_ident(&place.ident)?;
        if let TyKind::Data(dty) = &ident_ty.ty {
            proj_ty((**dty).clone(), &place.path)
        } else {
            panic!("This place is not of a data type.")
        }
    }

    pub fn set_place_dty(
        &mut self,
        pl: &internal::Place<'a>,
        pl_ty: DataTy<'a>,
        arena: &'a Bump,
    ) -> &mut Self {
        fn set_dty_for_path_in_dty<'a>(
            arena: &'a Bump,
            orig_dty: DataTy<'a>,
            path: &[PathElem<'a>],
            part_dty: DataTy<'a>,
        ) -> DataTy<'a> {
            if path.is_empty() {
                return part_dty;
            }

            let pe = path.first().unwrap();
            match (orig_dty.dty, pe) {
                (DataTyKind::Tuple(mut elem_tys), PathElem::Proj(n)) => {
                    elem_tys[*n] =
                        set_dty_for_path_in_dty(arena, elem_tys[*n].clone(), &path[1..], part_dty);
                    DataTy::new(arena, DataTyKind::Tuple(elem_tys))
                }
                (DataTyKind::Struct(struct_decl), PathElem::FieldProj(ident)) => {
                    let struct_decl = arena.alloc(struct_decl.clone());
                    if let Some(field) = struct_decl.fields.iter_mut().find(|f| &f.0 == *ident) {
                        field.1 =
                            set_dty_for_path_in_dty(arena, field.1.clone(), &path[1..], part_dty);
                        DataTy::new(arena, DataTyKind::Struct(struct_decl))
                    } else {
                        panic!("Struct field with name `{}` does not exist.", ident.name)
                    }
                }
                _ => panic!("Path not compatible with type."),
            }
        }

        let ident_typed = self
            .idents_typed_mut()
            .rev()
            .find(|ident_typed| ident_typed.ident == pl.ident)
            .unwrap();
        if let TyKind::Data(dty) = &ident_typed.ty.ty {
            let updated_dty =
                set_dty_for_path_in_dty(arena, (**dty).clone(), pl.path.as_slice(), pl_ty);
            ident_typed.ty = Ty::new(TyKind::Data(arena.alloc(updated_dty)));
            self
        } else {
            panic!("Trying to set data type for identifier without data type.")
        }
    }

    pub fn kill_place(&mut self, pl: &internal::Place<'a>, arena: &'a Bump) -> &mut Self {
        if let Ok(pl_dty) = self.place_dty(pl) {
            self.set_place_dty(
                pl,
                DataTy::new(arena, DataTyKind::Dead(arena.alloc(pl_dty))),
                arena,
            )
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
    pub(super) fn without_reborrow_loans(&mut self, pl_expr: &PlaceExpr<'a>) -> &mut Self {
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

pub(super) struct AccessCtx<'a> {
    ctx: BumpVec<'a, Loan<'a>>,
}

impl<'a> AccessCtx<'a> {
    pub fn new(arena: &'a Bump) -> Self {
        AccessCtx {
            ctx: BumpVec::new_in(arena),
        }
    }

    pub fn insert(&mut self, loans: BumpVec<Loan<'a>>) {
        self.ctx.extend(loans.into_iter())
    }

    pub fn hash_set(&self) -> &BumpVec<Loan<'a>> {
        &self.ctx
    }

    pub fn clear_sync_for(
        &mut self,
        ty_ctx: &'a TyCtx<'a>,
        exec: &'a ExecExpr<'a>,
        arena: &'a Bump,
    ) {
        self.ctx = self
            .ctx
            .iter()
            .filter_map(|l| {
                trim_after_select_of(ty_ctx, exec, l.place_expr.clone()).map(|place_expr| Loan {
                    own: l.own,
                    place_expr,
                })
            })
            .collect_in(arena);
    }

    // a tiny helper that drills down a PlaceExpr to its `Ident`
    // and returns it by value (i.e. clones the Box<str> inside Ident)
    // maybe move this one out ?
    fn root_ident_of_expr(pe: &PlaceExpr<'a>) -> Ident<'a> {
        match &pe.pl_expr {
            PlaceExprKind::Ident(id) => id.clone(),
            PlaceExprKind::Select(inner, _)
            | PlaceExprKind::View(inner, _)
            | PlaceExprKind::Proj(inner, _)
            | PlaceExprKind::FieldProj(inner, _)
            | PlaceExprKind::Idx(inner, _)
            | PlaceExprKind::Deref(inner) => {
                // recursive descent
                Self::root_ident_of_expr(inner)
            }
        }
    }

    pub fn garbage_collect(&mut self, ty_ctx: &TyCtx<'a>, arena: &'a Bump) {
        // 1) take ownership of the old loans
        let old_loans = std::mem::replace(&mut self.ctx, BumpVec::new_in(arena));

        // 2) build a fresh vec of only the “alive” loans
        let mut new_loans = BumpVec::new_in(arena);
        for loan in old_loans.into_iter() {
            // extract root ident by *value* (no long‐lived borrow)
            let ident = Self::root_ident_of_expr(&loan.place_expr);
            if ty_ctx.contains(&ident) {
                new_loans.push(loan);
            }
        }

        // 3) store it back
        self.ctx = new_loans;
    }
}

fn trim_after_select_of<'a>(
    ty_ctx: &'a TyCtx<'a>,
    exec: &'a ExecExpr<'a>,
    pl_expr: PlaceExpr<'a>,
) -> Option<PlaceExpr<'a>> {
    match pl_expr.pl_expr {
        PlaceExprKind::Select(p, sel_exec) if sel_exec == exec => {
            Some(PlaceExpr::new(PlaceExprKind::Select(p, sel_exec)))
        }
        PlaceExprKind::Select(ipl, _)
        | PlaceExprKind::View(ipl, _)
        | PlaceExprKind::Proj(ipl, _)
        | PlaceExprKind::FieldProj(ipl, _)
        | PlaceExprKind::Idx(ipl, _)
        | PlaceExprKind::Deref(ipl) => trim_after_select_of(ty_ctx, exec, ipl.clone()),
        PlaceExprKind::Ident(ident) => {
            let ident_exec = &ty_ctx
                .ident_ty(&ident)
                .expect("valid identifier must exist for every expression in access context")
                .exec;
            // FIXME: what we really want is check: ident_ty.exec is_more_specific_than exec
            //  current assumption is: longer path => more specific (which is
            //  Not always correct!!! (e.g. wenn different ranges of threads in a block are taken)
            if exec.exec.path.len() < ident_exec.exec.path.len() {
                None
            } else {
                Some(PlaceExpr::new(PlaceExprKind::Ident(ident)))
            }
        }
    }
}

#[derive(PartialEq, Eq, Debug, Clone)]
enum KindingCtxEntry<'a> {
    Ident(IdentKinded<'a>),
    PrvRel(PrvRel<'a>),
}

pub(super) type CtxResult<'a, T> = Result<T, CtxError<'a>>;

#[derive(PartialEq, Eq, Debug, Clone)]
pub(super) struct KindCtx<'a> {
    ctx: BumpVec<'a, BumpVec<'a, KindingCtxEntry<'a>>>,
}

impl<'a> KindCtx<'a> {
    pub fn new(arena: &'a Bump) -> Self {
        let mut scopes = BumpVec::new_in(arena);
        scopes.push(BumpVec::new_in(arena));
        KindCtx { ctx: scopes }
    }

    pub fn gl_fun_kind_ctx(
        idents: BumpVec<'a, IdentKinded<'a>>,
        prv_rels: BumpVec<'a, PrvRel<'a>>,
        arena: &'a Bump,
    ) -> CtxResult<'a, Self> {
        let mut kind_ctx: Self = KindCtx::new(arena);
        kind_ctx.append_idents(idents);
        kind_ctx.append_prv_rels(prv_rels)?;
        Ok(kind_ctx)
    }

    pub fn push_empty_scope(&mut self, arena: &'a Bump) -> &mut Self {
        self.ctx.push(BumpVec::new_in(arena));
        self
    }

    pub fn drop_scope(&mut self) {
        self.ctx.pop();
    }

    pub fn append_idents<I: IntoIterator<Item = IdentKinded<'a>>>(
        &mut self,
        idents: I,
    ) -> &mut Self {
        let entries = idents.into_iter().map(KindingCtxEntry::Ident);
        for e in entries {
            self.ctx.last_mut().unwrap().push(e);
        }
        self
    }

    pub fn append_prv_rels<I: IntoIterator<Item = PrvRel<'a>> + Clone>(
        &mut self,
        prv_rels: I,
    ) -> CtxResult<'a, &mut Self> {
        self.well_kinded_prv_rels(prv_rels.clone())?;
        for prv_rel in prv_rels {
            self.ctx
                .last_mut()
                .unwrap()
                .push(KindingCtxEntry::PrvRel(prv_rel));
        }
        Ok(self)
    }

    pub fn well_kinded_prv_rels<I: IntoIterator<Item = PrvRel<'a>>>(
        &self,
        prv_rels: I,
    ) -> CtxResult<'a, ()> {
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

    pub fn get_idents(&'a self, kind: Kind) -> impl Iterator<Item = &'a Ident<'a>> + 'a {
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

    pub fn ident_of_kind_exists(&self, ident: &'a Ident<'a>, kind: Kind) -> bool {
        self.get_idents(kind).any(|id| ident == id)
    }

    pub fn outlives(&self, l: &'a Ident<'a>, s: &'a Ident<'a>) -> CtxResult<'a, ()> {
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
pub(super) enum GlobalDecl<'a> {
    FnDecl(&'a str, &'a FnTy<'a>),
    StructDecl(&'a StructDecl<'a>),
}

#[derive(Debug)]
pub(super) struct GlobalCtx<'a> {
    compil_unit: &'a mut CompilUnit<'a>,
    checked_funs: BumpVec<'a, (&'a str, &'a [usize])>,
    decls: BumpVec<'a, GlobalDecl<'a>>,
}

impl<'a> GlobalCtx<'a> {
    pub fn new(
        compil_unit: &'a mut CompilUnit<'a>,
        mut decls: BumpVec<'a, GlobalDecl<'a>>,
        arena: &'a Bump,
    ) -> Self {
        // 1) grab a raw pointer + length; this does NOT borrow.
        let items_ptr = compil_unit.items.as_ptr();
        let len = compil_unit.items.len();

        // 2) iterate by pointer offets
        for i in 0..len {
            // SAFETY: `i < len` so ptr.add(i) is in-bounds, and we never touch compil_unit.items mutably.
            let item: &Item<'a> = unsafe { &*items_ptr.add(i) };
            match item {
                Item::FunDef(fun_def) => {
                    let name: &str = &fun_def.ident.name;
                    let ty_ref: &FnTy<'a> = arena.alloc(fun_def.fn_ty(arena));
                    decls.push(GlobalDecl::FnDecl(name, ty_ref));
                }
                Item::FunDecl(fun_decl) => {
                    let name: &str = &fun_decl.ident.name;
                    let ty_ref: &FnTy<'a> = arena.alloc(fun_decl.fn_ty(arena));
                    decls.push(GlobalDecl::FnDecl(name, ty_ref));
                }
                Item::StructDecl(struct_decl) => {
                    // We can safely store the reference here,
                    // because `struct_decl` lives inside `compil_unit` for 'a.
                    decls.push(GlobalDecl::StructDecl(struct_decl));
                }
                _ => {}
            }
        }

        // 3) now that we never held any &borrows of items, we can store the &mut
        GlobalCtx {
            compil_unit,
            checked_funs: BumpVec::new_in(arena),
            decls,
        }
    }

    pub fn has_been_checked(&self, name: &str, nat_args: &[usize]) -> bool {
        self.checked_funs
            .iter()
            .any(|(fun_name, nargs)| *fun_name == name && *nargs == nat_args)
    }

    pub fn push_fun_checked_under_nats(
        &mut self,
        arena: &'a bumpalo::Bump,
        fun_def_owned: FunDef<'a>, // take by value
        nat_vals: &'a [usize],
    ) {
        let fun_name = fun_def_owned.ident.name.clone();
        let fd_ref: &'a FunDef<'a> = arena.alloc(fun_def_owned);
        self.compil_unit.items.push(Item::FunDef(fd_ref));
        self.checked_funs.push((fun_name, nat_vals));
    }

    pub fn pop_fun_def(&mut self, name: &'a str) -> Option<&'a FunDef<'a>> {
        let index = self.compil_unit.items.iter().position(|item| {
            if let Item::FunDef(fun_def) = item {
                fun_def.ident.name == name
            } else {
                false
            }
        });
        if let Some(i) = index {
            if let Item::FunDef(fun_def) = self.compil_unit.items.remove(i) {
                Some(fun_def)
            } else {
                None
            }
        } else {
            None
        }
    }

    pub fn fn_ty_by_ident(&self, ident: &'a Ident<'a>) -> CtxResult<'a, &'a FnTy<'a>> {
        if let Some(fn_ty) = self.decls.iter().find_map(|decl| match decl {
            GlobalDecl::FnDecl(name, fn_ty) if name == &ident.name => Some(fn_ty),
            GlobalDecl::FnDecl(_, _) | GlobalDecl::StructDecl(_) => None,
        }) {
            Ok(fn_ty)
        } else {
            Err(CtxError::IdentNotFound(ident.clone()))
        }
    }
}

#[test]
fn test_kill_place_ident() {
    let arena = Bump::new();

    let mut ty_ctx = TyCtx::new(&arena);
    let x_ident = Ident::new(&arena, "x");
    let exec_ident = Ident::new(&arena, "exec");
    let exec_expr = ExecExpr::new(
        &arena,
        ExecExprKind::new(&arena, BaseExec::Ident(exec_ident.clone())),
    );
    let scalar_ty = arena.alloc(DataTy::new(&arena, DataTyKind::Scalar(ScalarTy::I32)));
    let ty_kind = TyKind::Data(scalar_ty);
    let x_typed = IdentTyped::new_in(&arena, "x", Ty::new(ty_kind), Mutability::Const, exec_expr);

    ty_ctx.append_ident_typed(x_typed);
    let place = internal::Place::new(x_ident.clone(), BumpVec::new_in(&arena));
    ty_ctx.kill_place(&place, &arena);

    assert!(matches!(
        ty_ctx.idents_typed().next().unwrap().ty.dty(),
        DataTy {
            dty: DataTyKind::Dead(_),
            ..
        }
    ));
}
