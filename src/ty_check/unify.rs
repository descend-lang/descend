use crate::arena_ast::utils;
use crate::arena_ast::utils::Visitable;
use crate::arena_ast::visit_mut::VisitMut;
use crate::arena_ast::*;
use crate::ty_check::ctxs::{KindCtx, TyCtx};
use crate::ty_check::error::UnifyError;
use crate::ty_check::subty;
use bumpalo::{collections::Vec as BumpVec, Bump};
use std::collections::HashMap;

#[inline]
fn arena_slice<'a, T>(v: &bumpalo::collections::Vec<'a, T>) -> &'a [T] {
    unsafe { std::slice::from_raw_parts(v.as_ptr(), v.len()) }
}

type UnifyResult<'a, T> = Result<T, UnifyError<'a>>;

pub(super) fn unify<'a, C: Constrainable<'a>>(
    t1: &'a mut C,
    t2: &'a mut C,
    arena: &'a Bump,
) -> UnifyResult<'a, ()> {
    let (_, _) = constrain(t1, t2, arena)?;
    Ok(())
}

pub(super) fn sub_unify<'a, C: Constrainable<'a>>(
    kind_ctx: &'a KindCtx<'a>,
    ty_ctx: &'a mut TyCtx<'a>,
    sub: &'a mut C,
    sup: &'a mut C,
    arena: &'a Bump,
) -> UnifyResult<'a, ()> {
    let (_map, prv) = constrain(sub, sup, arena)?;
    subty::multiple_outlives(
        kind_ctx,
        ty_ctx,
        prv.iter().map(|PrvConstr(p1, p2)| (*p1, *p2)),
        arena,
    )?;
    Ok(())
}

pub(super) fn constrain<'a, S: Constrainable<'a>>(
    t1: &'a mut S,
    t2: &'a mut S,
    arena: &'a Bump,
) -> UnifyResult<'a, (ConstrainMap<'a>, BumpVec<'a, PrvConstr<'a>>)> {
    let mut constr_map = ConstrainMap::new();
    let mut prv_rels = BumpVec::new_in(arena);
    t1.constrain(t2, &mut constr_map, &mut prv_rels, arena)?;
    Ok((constr_map, prv_rels))
}

/**
pub(super) fn inst_fn_ty_scheme<'a>(fn_ty: &'a FnTy<'a>, arena: &'a Bump) -> FnTy<'a> {
    assert!(
        fn_ty.generic_exec.is_none(),
        "exec must be substituted before instantiation to make sure that it has the correct type"
    );
    let mono_idents: Vec<_> = fn_ty
        .generics
        .iter()
        .map(|i| match i.kind {
            Kind::DataTy => ArgKinded::DataTy(DataTy::new(
                arena,
                utils::fresh_ident(arena, &i.ident.name, DataTyKind::Ident),
            )),
            Kind::Nat => ArgKinded::Nat(utils::fresh_ident(arena, &i.ident.name, Nat::Ident)),
            Kind::Memory => {
                ArgKinded::Memory(utils::fresh_ident(arena, &i.ident.name, Memory::Ident))
            }
            Kind::Provenance => {
                ArgKinded::Provenance(utils::fresh_ident(arena, &i.ident.name, Provenance::Ident))
            }
        })
        .collect();

    let mut inst_fn_ty = fn_ty.clone();
    let generics = inst_fn_ty.generics.drain(..).collect::<Vec<_>>();
    utils::subst_idents_kinded(arena, generics.iter(), mono_idents.iter(), &mut inst_fn_ty);
    inst_fn_ty
}
*/

pub(super) fn inst_fn_ty_scheme<'a>(fn_ty: &'a FnTy<'a>, arena: &'a bumpalo::Bump) -> FnTy<'a> {
    assert!(
        fn_ty.generic_exec.is_none(),
        "exec must be substituted before instantiation to make sure that it has the correct type"
    );

    // 1) Build arena-resident args (so the *elements* live for 'a)
    let mut mono_args = bumpalo::collections::Vec::new_in(arena);
    for g in fn_ty.generics.iter() {
        let arg = match g.kind {
            Kind::DataTy => {
                let dk = utils::fresh_ident(arena, &g.ident.name, |id| DataTyKind::Ident(id));
                ArgKinded::DataTy(DataTy::new(arena, dk))
            }
            Kind::Nat => ArgKinded::Nat(utils::fresh_ident(arena, &g.ident.name, |id| {
                Nat::Ident(id)
            })),
            Kind::Memory => ArgKinded::Memory(utils::fresh_ident(arena, &g.ident.name, |id| {
                Memory::Ident(id)
            })),
            Kind::Provenance => {
                ArgKinded::Provenance(utils::fresh_ident(arena, &g.ident.name, |id| {
                    Provenance::Ident(id)
                }))
            }
        };
        mono_args.push(arg);
    }

    // 2) Convert to a slice with lifetime 'a (elements are arena-owned)
    let args_a: &'a [ArgKinded<'a>] = arena_slice(&mono_args);

    // 3) Make a working copy (whatever “clone” mechanism you have)
    let mut inst = fn_ty.clone(); // or your `clone_in(arena)`/rebuild

    // 4) Substitute: domain = original generics (already 'a), codomain = args_a
    utils::subst_idents_kinded(arena, fn_ty.generics.iter(), args_a.iter(), &mut inst);

    // 5) Monomorphic result has no generics/exec param
    inst.generics.clear();
    inst.generic_exec = None;
    inst
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub(super) struct PrvConstr<'a>(pub &'a Provenance<'a>, pub &'a Provenance<'a>);

#[derive(Debug)]
pub(super) struct ConstrainMap<'a> {
    pub dty_unifier: HashMap<&'a str, DataTy<'a>>,
    pub nat_unifier: HashMap<&'a str, Nat<'a>>,
    pub mem_unifier: HashMap<&'a str, Memory<'a>>,
    pub prv_unifier: HashMap<&'a str, Provenance<'a>>,
    pub exec_unifier: HashMap<&'a str, ExecExpr<'a>>,
}

impl<'a> ConstrainMap<'a> {
    fn new() -> Self {
        Self {
            dty_unifier: HashMap::new(),
            nat_unifier: HashMap::new(),
            mem_unifier: HashMap::new(),
            prv_unifier: HashMap::new(),
            exec_unifier: HashMap::new(),
        }
    }
}

impl<'a> DataTy<'a> {
    fn bind_to(
        &self,
        ident: &'a Ident<'a>,
        constr_map: &mut ConstrainMap<'a>,
        arena: &'a Bump,
    ) -> UnifyResult<'a, ()> {
        if let DataTyKind::Ident(ty_id) = &self.dty {
            if ty_id == ident {
                return Ok(());
            }
        }
        if Self::occurs_check(&IdentKinded::new(ident, Kind::DataTy), self) {
            return Err(UnifyError::InfiniteType);
        }
        if let Some(old) = constr_map
            .dty_unifier
            .insert(ident.name.clone(), self.clone())
        {
            if &old != self {
                panic!(
                    "Rebinding bound type variable.\n\
                    Old: {:?}\n\
                    New: {:?}",
                    old, self
                );
            }
        }

        let term_ref: &'a DataTy<'a> = arena.alloc(self.clone_in(arena));
        constr_map
            .dty_unifier
            .values_mut()
            .for_each(|dty| SubstIdent::new(ident, term_ref).visit_dty(arena, dty));
        Ok(())
    }
}

pub(super) trait Substitutable<'a> {
    fn substitute<'s>(&mut self, subst: &'s ConstrainMap<'a>, arena: &'a Bump);
}

pub(super) trait Constrainable<'a>: Visitable<'a> + Substitutable<'a> {
    fn constrain<'m>(
        &'m mut self,
        other: &'m mut Self,
        constr_map: &'m mut ConstrainMap<'a>,
        prv_rels: &'m mut BumpVec<'a, PrvConstr<'a>>,
        arena: &'a Bump,
    ) -> UnifyResult<'a, ()>;

    fn occurs_check<S: Constrainable<'a>>(ident_kinded: &IdentKinded<'a>, s: &S) -> bool {
        utils::free_kinded_idents(s).contains(ident_kinded)
    }
}

impl<'a> Constrainable<'a> for FnTy<'a> {
    fn constrain<'m>(
        &'m mut self,
        other: &'m mut Self,
        constr_map: &'m mut ConstrainMap<'a>,
        prv_rels: &'m mut BumpVec<'a, PrvConstr<'a>>,
        arena: &'a Bump,
    ) -> UnifyResult<'a, ()> {
        assert!(self.generics.is_empty());
        assert!(other.generics.is_empty());
        assert!(self.generic_exec.is_none());
        assert!(other.generic_exec.is_none());

        self.exec
            .constrain(&mut other.exec, constr_map, prv_rels, arena)?;
        substitute(&*constr_map, self, arena);
        substitute(&*constr_map, other, arena);

        if self.param_sigs.len() != other.param_sigs.len() {
            return Err(UnifyError::CannotUnify);
        }
        // TODO refactor
        // substitute result of unification for every following unification
        let mut i = 0;
        let mut remain_lhs = &mut self.param_sigs[i..];
        let mut remain_rhs = &mut other.param_sigs[i..];
        while let (Some((next_lhs, _)), Some((next_rhs, _))) =
            (remain_lhs.split_first_mut(), remain_rhs.split_first_mut())
        {
            next_lhs.constrain(next_rhs, constr_map, prv_rels, arena)?;
            substitute(&*constr_map, self, arena);
            substitute(&*constr_map, other, arena);

            i += 1;
            remain_lhs = &mut self.param_sigs[i..];
            remain_rhs = &mut other.param_sigs[i..];
        }

        // self.ret_ty.constrain(&mut other.ret_ty, constr_map, prv_rels, arena)?;

        let mut lhs_ret = self.ret_ty.clone_in(arena);
        let mut rhs_ret = other.ret_ty.clone_in(arena);

        lhs_ret.constrain(&mut rhs_ret, constr_map, prv_rels, arena)?;

        self.ret_ty = arena.alloc(lhs_ret);
        other.ret_ty = arena.alloc(rhs_ret);

        substitute(&*constr_map, self, arena);
        substitute(&*constr_map, other, arena);
        Ok(())
    }
}

impl<'a> Substitutable<'a> for FnTy<'a> {
    fn substitute<'s>(&mut self, subst: &'s ConstrainMap<'a>, arena: &'a Bump) {
        let mut apply_subst = ApplySubst::new(subst);
        apply_subst.visit_fn_ty(arena, self);
    }
}

impl<'a> Constrainable<'a> for ParamSig<'a> {
    fn constrain<'m>(
        &'m mut self,
        other: &'m mut Self,
        constr_map: &'m mut ConstrainMap<'a>,
        prv_rels: &'m mut BumpVec<'a, PrvConstr<'a>>,
        arena: &'a Bump,
    ) -> UnifyResult<'a, ()> {
        self.exec_expr
            .constrain(&mut other.exec_expr, constr_map, prv_rels, arena)?;
        substitute(constr_map, self, arena);
        substitute(constr_map, other, arena);

        {
            let mut lhs = self.ty.clone_in(arena);
            let mut rhs = other.ty.clone_in(arena);

            lhs.constrain(&mut rhs, constr_map, prv_rels, arena)?;

            self.ty = arena.alloc(lhs);
            other.ty = arena.alloc(rhs);
        }

        substitute(constr_map, self, arena);
        substitute(constr_map, other, arena);
        Ok(())
    }
}

impl<'a> Substitutable<'a> for ParamSig<'a> {
    fn substitute<'s>(&mut self, subst: &'s ConstrainMap<'a>, arena: &'a Bump) {
        let mut apply_subst = ApplySubst::new(subst);
        apply_subst.visit_param_sig(arena, self);
    }
}

// TODO unification for exec expressions necessary for Nats? Can this be moved into a separate
//  equality check?
impl<'a> Constrainable<'a> for ExecExpr<'a> {
    fn constrain<'m>(
        &'m mut self,
        other: &'m mut Self,
        constr_map: &'m mut ConstrainMap<'a>,
        prv_rels: &'m mut BumpVec<'a, PrvConstr<'a>>,
        arena: &'a Bump,
    ) -> UnifyResult<'a, ()> {
        use BaseExec as BE;
        use ExecPathElem as EPE;

        match (&self.exec.base, &other.exec.base) {
            (BE::Ident(i1), BE::Ident(i2)) => {
                assert!(
                    !i1.is_implicit && !i2.is_implicit,
                    "Implicit identifier for exec expression should not exist"
                );
                if i1 != i2 {
                    return Err(UnifyError::CannotUnify);
                }
            }
            (BE::CpuThread, BE::CpuThread) => { /* ok */ }

            (BE::GpuGrid(gd1, bd1), BE::GpuGrid(gd2, bd2)) => {
                let mut lg = gd1.clone_in(arena);
                let mut rg = gd2.clone_in(arena);
                lg.constrain(&mut rg, constr_map, prv_rels, arena)?;

                let mut lb = bd1.clone_in(arena);
                let mut rb = bd2.clone_in(arena);
                lb.constrain(&mut rb, constr_map, prv_rels, arena)?;
            }

            _ => return Err(UnifyError::CannotUnify),
        }

        let l_len = self.exec.path.len();
        let r_len = other.exec.path.len();
        if l_len != r_len {
            return Err(UnifyError::CannotUnify);
        }

        for i in 0..l_len {
            let mut le = self.exec.path[i].clone();
            let mut re = other.exec.path[i].clone();

            {
                let mut ap = ApplySubst::new(constr_map);
                ap.visit_exec_path_elem(arena, &mut le);
                ap.visit_exec_path_elem(arena, &mut re);
            }

            match (&mut le, &mut re) {
                (EPE::ForAll(dl), EPE::ForAll(dr)) | (EPE::ToThreads(dl), EPE::ToThreads(dr)) => {
                    if dl != dr {
                        return Err(UnifyError::CannotUnify);
                    }
                }

                (EPE::TakeRange(rl), EPE::TakeRange(rr)) => {
                    if rl.split_dim != rr.split_dim || rl.left_or_right != rr.left_or_right {
                        return Err(UnifyError::CannotUnify);
                    }
                    let mut lp = rl.pos.clone_in(arena);
                    let mut rp = rr.pos.clone_in(arena);
                    lp.constrain(&mut rp, constr_map, prv_rels, arena)?;
                }

                (EPE::ToWarps, EPE::ToWarps) => { /* ok */ }

                _ => return Err(UnifyError::CannotUnify),
            }
        }

        // Optional: normalize by applying the final substitution to the whole exprs.
        // (This rebuilds nodes in the arena and updates the &-fields atomically.)
        substitute(constr_map, self, arena);
        substitute(constr_map, other, arena);

        Ok(())
    }
}

impl<'a> Substitutable<'a> for ExecExpr<'a> {
    fn substitute(&mut self, subst: &ConstrainMap<'a>, arena: &'a Bump) {
        let mut apply_subst = ApplySubst::new(subst);
        apply_subst.visit_exec_expr(arena, self);
    }
}

impl<'a> Constrainable<'a> for Ty<'a> {
    fn constrain<'m>(
        &'m mut self,
        other: &'m mut Self,
        constr_map: &'m mut ConstrainMap<'a>,
        prv_rels: &'m mut BumpVec<'a, PrvConstr<'a>>,
        arena: &'a Bump,
    ) -> UnifyResult<'a, ()> {
        match (&mut self.ty, &mut other.ty) {
            (TyKind::FnTy(fn_ty1), TyKind::FnTy(fn_ty2)) => {
                {
                    let mut f1 = (*fn_ty1).clone_in(arena);
                    let mut f2 = (*fn_ty2).clone_in(arena);
                    f1.constrain(&mut f2, constr_map, prv_rels, arena)?;
                }
                substitute(constr_map, self, arena);
                substitute(constr_map, other, arena);
                Ok(())
            }
            (TyKind::Data(dty1), TyKind::Data(dty2)) => {
                {
                    let mut d1 = (*dty1).clone_in(arena);
                    let mut d2 = (*dty2).clone_in(arena);
                    d1.constrain(&mut d2, constr_map, prv_rels, arena)?;
                }
                substitute(constr_map, self, arena);
                substitute(constr_map, other, arena);
                Ok(())
            }
            _ => Err(UnifyError::CannotUnify),
        }
    }
}

impl<'a> Substitutable<'a> for Ty<'a> {
    fn substitute(&mut self, subst: &ConstrainMap<'a>, arena: &'a Bump) {
        let mut apply_subst = ApplySubst::new(subst);
        apply_subst.visit_ty(arena, self);
    }
}

impl<'a> Constrainable<'a> for DataTy<'a> {
    fn constrain<'m>(
        &'m mut self,
        other: &'m mut Self,
        constr_map: &'m mut ConstrainMap<'a>,
        prv_rels: &'m mut BumpVec<'a, PrvConstr<'a>>,
        arena: &'a Bump,
    ) -> UnifyResult<'a, ()> {
        match (&mut self.dty, &mut other.dty) {
            (DataTyKind::Ident(i1), DataTyKind::Ident(i2)) => {
                if i1.is_implicit {
                    let i1_ref: &'a Ident<'a> = arena.alloc(i1.clone());
                    other.bind_to(i1_ref, constr_map, arena)?
                } else if i2.is_implicit {
                    let i2_ref: &'a Ident<'a> = arena.alloc(i2.clone());
                    self.bind_to(i2_ref, constr_map, arena)?
                } else if i1 == i2 {
                    return Ok(());
                } else {
                    return Err(UnifyError::CannotUnify);
                }
                substitute(constr_map, self, arena);
                substitute(constr_map, other, arena);
            }
            (DataTyKind::Ident(i), _) if i.is_implicit => {
                let i_ref: &'a Ident<'a> = arena.alloc(i.clone());
                other.bind_to(i_ref, constr_map, arena)?;
                substitute(constr_map, other, arena);
            }
            (_, DataTyKind::Ident(i)) if i.is_implicit => {
                let i_ref: &'a Ident<'a> = arena.alloc(i.clone());
                self.bind_to(i_ref, constr_map, arena)?;
                substitute(constr_map, self, arena);
            }
            (DataTyKind::Scalar(sty1), DataTyKind::Scalar(sty2)) => {
                if sty1 != sty2 {
                    return Err(UnifyError::CannotUnify);
                } else {
                    return Ok(());
                }
            }
            (DataTyKind::Ref(ref1), DataTyKind::Ref(ref2)) => {
                let RefDty {
                    rgn: rgn1,
                    own: own1,
                    mem: mem1,
                    dty: dty1,
                } = (**ref1).clone_in(arena);

                let RefDty {
                    rgn: rgn2,
                    own: own2,
                    mem: mem2,
                    dty: dty2,
                } = (**ref2).clone_in(arena);

                if own1 != own2 {
                    return Err(UnifyError::CannotUnify);
                }

                let mut rgn1 = rgn1;
                let mut rgn2 = rgn2;
                rgn1.constrain(&mut rgn2, constr_map, prv_rels, arena)?;

                let mut dty1_mut = (*dty1).clone();
                let mut dty2_mut = (*dty2).clone();

                substitute(constr_map, &mut dty1_mut, arena);
                substitute(constr_map, &mut dty2_mut, arena);

                let mut mem1 = mem1;
                let mut mem2 = mem2;
                mem1.constrain(&mut mem2, constr_map, prv_rels, arena)?;

                substitute(constr_map, &mut mem1, arena);
                substitute(constr_map, &mut mem2, arena);
                substitute(constr_map, &mut dty1_mut, arena);
                substitute(constr_map, &mut dty1_mut, arena);

                dty1_mut.constrain(&mut dty2_mut, constr_map, prv_rels, arena)?;

                substitute(constr_map, self, arena);
                substitute(constr_map, other, arena);
            }
            (DataTyKind::Tuple(elem_dtys1), DataTyKind::Tuple(elem_dtys2)) => {
                // TODO figure out why the las three/two lines of the while loop enable borrowing
                //  in inner for-loop
                let mut i = 0;
                let mut remain_lhs = &mut elem_dtys1[i..];
                let mut remain_rhs = &mut elem_dtys2[i..];
                while let (Some((next_lhs, _)), Some((next_rhs, _))) =
                    (remain_lhs.split_first_mut(), remain_rhs.split_first_mut())
                {
                    next_lhs.constrain(next_rhs, constr_map, prv_rels, arena)?;
                    for (dty1, dty2) in elem_dtys1.iter_mut().zip(elem_dtys2.iter_mut()) {
                        substitute(constr_map, dty1, arena);
                        substitute(constr_map, dty2, arena);
                    }

                    i += 1;
                    remain_lhs = &mut elem_dtys1[i..];
                    remain_rhs = &mut elem_dtys2[i..];
                }
            }
            (DataTyKind::Struct(struct_decl1), DataTyKind::Struct(struct_decl2)) => {
                if struct_decl1.fields.len() != struct_decl2.fields.len() {
                    return Err(UnifyError::CannotUnify);
                }

                for ((lname, lty_ref), (rname, rty_ref)) in
                    struct_decl1.fields.iter().zip(struct_decl2.fields.iter())
                {
                    if lname != rname {
                        return Err(UnifyError::CannotUnify);
                    }

                    let mut lty = lty_ref.clone_in(arena);
                    let mut rty = rty_ref.clone_in(arena);

                    lty.constrain(&mut rty, constr_map, prv_rels, arena)?;
                }

                substitute(constr_map, self, arena);
                substitute(constr_map, other, arena);

                /*
                let mut i = 0;
                let mut remain_lhs = &mut struct_decl1.fields[i..];
                let mut remain_rhs = &mut struct_decl2.fields[i..];
                while let (Some((next_lhs, _)), Some((next_rhs, _))) =
                    (remain_lhs.split_first_mut(), remain_rhs.split_first_mut())
                {
                    if next_lhs.0 != next_rhs.0 {
                        return Err(UnifyError::CannotUnify);
                    }
                    next_lhs
                        .1
                        .constrain(&mut next_rhs.1, constr_map, prv_rels, arena)?;
                    for ((_, dty1), (_, dty2)) in struct_decl1
                        .fields
                        .iter_mut()
                        .zip(struct_decl2.fields.iter_mut())
                    {
                        substitute(constr_map, dty1, arena);
                        substitute(constr_map, dty2, arena);
                    }

                    i += 1;
                    remain_lhs = &mut struct_decl1.fields[i..];
                    remain_rhs = &mut struct_decl2.fields[i..];
                }
                */
            }
            (DataTyKind::Array(dty1, n1), DataTyKind::Array(dty2, n2))
            | (DataTyKind::ArrayShape(dty1, n1), DataTyKind::ArrayShape(dty2, n2)) => {
                let mut dty1_owned = (**dty1).clone();
                let mut dty2_owned = (**dty2).clone();
                dty1_owned.constrain(&mut dty2_owned, constr_map, prv_rels, arena)?;
                substitute(constr_map, &mut dty1_owned, arena);
                substitute(constr_map, &mut dty2_owned, arena);
                *dty1 = arena.alloc(dty1_owned);
                *dty2 = arena.alloc(dty2_owned);

                n1.constrain(n2, constr_map, prv_rels, arena)?;
                substitute(constr_map, self, arena);
                substitute(constr_map, other, arena);
            }
            (DataTyKind::At(dty1, mem1), DataTyKind::At(dty2, mem2)) => {
                let mut dty1_owned = (**dty1).clone();
                let mut dty2_owned = (**dty2).clone();
                dty1_owned.constrain(&mut dty2_owned, constr_map, prv_rels, arena)?;
                substitute(constr_map, &mut dty1_owned, arena);
                substitute(constr_map, &mut dty2_owned, arena);
                *dty1 = arena.alloc(dty1_owned);
                *dty2 = arena.alloc(dty2_owned);
                mem1.constrain(mem2, constr_map, prv_rels, arena)?;
                substitute(constr_map, self, arena);
                substitute(constr_map, other, arena);
            }
            (DataTyKind::Atomic(sty1), DataTyKind::Atomic(sty2)) => {
                if sty1 != sty2 {
                    return Err(UnifyError::CannotUnify);
                } else {
                    return Ok(());
                }
            }
            (DataTyKind::RawPtr(_), DataTyKind::RawPtr(_)) => {
                unimplemented!()
            }
            (DataTyKind::Dead(_), _) => {
                panic!()
            }
            (dty1, DataTyKind::Dead(dty2)) if !matches!(dty1, DataTyKind::Dead(_)) => {
                let mut dty2_owned = (**dty2).clone();
                self.constrain(&mut dty2_owned, constr_map, prv_rels, arena)?;
                *dty2 = arena.alloc(dty2_owned);
                substitute(constr_map, self, arena);
                substitute(constr_map, other, arena);
            }
            _ => return Err(UnifyError::CannotUnify),
        }
        Ok(())
    }
}

impl<'a> Substitutable<'a> for DataTy<'a> {
    fn substitute(&mut self, subst: &ConstrainMap<'a>, arena: &'a Bump) {
        let mut apply_subst = ApplySubst::new(subst);
        apply_subst.visit_dty(arena, self);
    }
}

impl<'a> Constrainable<'a> for ExecTy<'a> {
    fn constrain<'m>(
        &'m mut self,
        other: &'m mut Self,
        constr_map: &'m mut ConstrainMap<'a>,
        prv_rels: &'m mut BumpVec<'a, PrvConstr<'a>>,
        arena: &'a Bump,
    ) -> UnifyResult<'a, ()> {
        match (&mut self.ty, &mut other.ty) {
            (ExecTyKind::CpuThread, ExecTyKind::CpuThread)
            | (ExecTyKind::GpuThread, ExecTyKind::GpuThread)
            | (ExecTyKind::GpuWarp, ExecTyKind::GpuWarp)
            | (_, ExecTyKind::Any) => Ok(()),

            (ExecTyKind::GpuWarpGrp(ln), ExecTyKind::GpuWarpGrp(rn)) => {
                let mut l = (*ln).clone_in(arena);
                let mut r = (*rn).clone_in(arena);
                l.constrain(&mut r, constr_map, prv_rels, arena)
            }

            (ExecTyKind::GpuGrid(lg, lb), ExecTyKind::GpuGrid(rg, rb))
            | (ExecTyKind::GpuBlockGrp(lg, lb), ExecTyKind::GpuBlockGrp(rg, rb)) => {
                let mut lgc = (*lg).clone_in(arena);
                let mut rgc = (*rg).clone_in(arena);
                lgc.constrain(&mut rgc, constr_map, prv_rels, arena)?;

                let mut lbc = (*lb).clone_in(arena);
                let mut rbc = (*rb).clone_in(arena);
                lbc.constrain(&mut rbc, constr_map, prv_rels, arena)
            }

            (ExecTyKind::GpuToThreads(ldc, l_inner), ExecTyKind::GpuToThreads(rdc, r_inner)) => {
                if ldc != rdc {
                    return Err(UnifyError::CannotUnify);
                }
                let mut li = (*l_inner).clone_in(arena);
                let mut ri = (*r_inner).clone_in(arena);
                li.constrain(&mut ri, constr_map, prv_rels, arena)
            }

            (ExecTyKind::GpuBlock(ld), ExecTyKind::GpuBlock(rd))
            | (ExecTyKind::GpuThreadGrp(ld), ExecTyKind::GpuThreadGrp(rd)) => {
                let mut lc = (*ld).clone_in(arena);
                let mut rc = (*rd).clone_in(arena);
                lc.constrain(&mut rc, constr_map, prv_rels, arena)
            }

            _ => Err(UnifyError::CannotUnify),
        }
    }
}

impl<'a> Substitutable<'a> for ExecTy<'a> {
    fn substitute(&mut self, subst: &ConstrainMap<'a>, _arena: &'a Bump) {
        let mut apply_subst = ApplySubst::new(subst);
        apply_subst.visit_exec_ty(self);
    }
}

/**
impl<'a> Constrainable<'a> for Dim<'a> {
    fn constrain<'m>(
        &'m mut self,
        other: &'m mut Self,
        constr_map: &'m mut ConstrainMap<'a>,
        prv_rels: &'m mut BumpVec<'a, PrvConstr<'a>>,
        arena: &'a Bump,
    ) -> UnifyResult<'a, ()> {
        match (self, other) {
            (Dim::XYZ(ldim), Dim::XYZ(rdim)) => {
                ldim.0.constrain(&mut rdim.0, constr_map, prv_rels, arena)?;
                ldim.1.constrain(&mut rdim.1, constr_map, prv_rels, arena)?;
                ldim.2.constrain(&mut rdim.2, constr_map, prv_rels, arena)
            }
            (Dim::XY(ldim), Dim::XY(rdim))
            | (Dim::XZ(ldim), Dim::XZ(rdim))
            | (Dim::YZ(ldim), Dim::YZ(rdim)) => {
                ldim.0.constrain(&mut rdim.0, constr_map, prv_rels, arena)?;
                ldim.1.constrain(&mut rdim.1, constr_map, prv_rels, arena)
            }
            (Dim::X(ld), Dim::X(rd)) | (Dim::Y(ld), Dim::Y(rd)) | (Dim::Z(ld), Dim::Z(rd)) => {
                ld.0.constrain(&mut rd.0, constr_map, prv_rels, arena)
            }
            _ => Err(UnifyError::CannotUnify),
        }
    }
}
*/

impl<'a> Constrainable<'a> for Dim<'a> {
    fn constrain<'m>(
        &'m mut self,
        other: &'m mut Self,
        constr_map: &'m mut ConstrainMap<'a>,
        prv_rels: &'m mut BumpVec<'a, PrvConstr<'a>>,
        arena: &'a Bump,
    ) -> UnifyResult<'a, ()> {
        use Dim::*;

        match (self, other) {
            (XYZ(ld), XYZ(rd)) => {
                let mut lx = ld.0.clone_in(arena);
                let mut rx = rd.0.clone_in(arena);
                lx.constrain(&mut rx, constr_map, prv_rels, arena)?;

                let mut ly = ld.1.clone_in(arena);
                let mut ry = rd.1.clone_in(arena);
                ly.constrain(&mut ry, constr_map, prv_rels, arena)?;

                let mut lz = ld.2.clone_in(arena);
                let mut rz = rd.2.clone_in(arena);
                lz.constrain(&mut rz, constr_map, prv_rels, arena)?;

                Ok(())
            }

            (XY(ld), XY(rd)) | (XZ(ld), XZ(rd)) | (YZ(ld), YZ(rd)) => {
                let mut l0 = ld.0.clone_in(arena);
                let mut r0 = rd.0.clone_in(arena);
                l0.constrain(&mut r0, constr_map, prv_rels, arena)?;

                let mut l1 = ld.1.clone_in(arena);
                let mut r1 = rd.1.clone_in(arena);
                l1.constrain(&mut r1, constr_map, prv_rels, arena)?;

                Ok(())
            }

            (X(ld), X(rd)) | (Y(ld), Y(rd)) | (Z(ld), Z(rd)) => {
                let mut ln = ld.0.clone_in(arena);
                let mut rn = rd.0.clone_in(arena);
                ln.constrain(&mut rn, constr_map, prv_rels, arena)
            }

            _ => Err(UnifyError::CannotUnify),
        }
    }
}

impl<'a> Substitutable<'a> for Dim<'a> {
    fn substitute(&mut self, subst: &ConstrainMap<'a>, arena: &'a Bump) {
        let mut apply_subst = ApplySubst::new(subst);
        apply_subst.visit_dim(arena, self);
    }
}

impl<'a> Nat<'a> {
    fn bind_to(
        &self,
        ident: &'a Ident<'a>,
        constr_map: &mut ConstrainMap<'a>,
        arena: &'a Bump,
    ) -> UnifyResult<'a, ()> {
        // No occurs check.
        // Nats can be equal to an expression in which the nat appears again. E.g., a = a * 1
        if let Some(old) = constr_map
            .nat_unifier
            .insert(ident.name.clone(), self.clone())
        {
            if &old != self {
                panic!(
                    "not able to check equality of Nats `{}` and `{}`",
                    old, self
                )
            }
        }
        let term_ref: &'a Nat<'a> = arena.alloc(self.clone_in(arena));
        constr_map
            .nat_unifier
            .values_mut()
            .for_each(|n| SubstIdent::new(ident, term_ref).visit_nat(arena, n));
        Ok(())
    }

    fn unify<'m>(n1: &'m Nat<'a>, n2: &'m Nat<'a>) -> UnifyResult<'a, ()> {
        if n1 == n2 {
            Ok(())
        } else {
            Err(UnifyError::CannotUnify)
        }
    }
}

impl<'a> Constrainable<'a> for Nat<'a> {
    fn constrain<'m>(
        &'m mut self,
        other: &'m mut Self,
        constr_map: &'m mut ConstrainMap<'a>,
        prv_rels: &'m mut BumpVec<'a, PrvConstr<'a>>,
        arena: &'a Bump,
    ) -> UnifyResult<'a, ()> {
        match (&*self, &*other) {
            (Nat::Ident(n1i), Nat::Ident(n2i)) if n1i.is_implicit || n2i.is_implicit => {
                match (n1i.is_implicit, n2i.is_implicit) {
                    (true, _) => other.bind_to(arena.alloc(n1i.clone()), constr_map, arena),
                    (false, _) => self.bind_to(arena.alloc(n2i.clone()), constr_map, arena),
                }
            }
            (Nat::Ident(n1i), _) if n1i.is_implicit => {
                other.bind_to(arena.alloc(n1i.clone()), constr_map, arena)
            }
            (_, Nat::Ident(n2i)) if n2i.is_implicit => {
                self.bind_to(arena.alloc(n2i.clone()), constr_map, arena)
            }
            (Nat::BinOp(op1, n1l, n1r), Nat::BinOp(op2, n2l, n2r)) if op1 == op2 => {
                let mut l_left = (*n1l).clone_in(arena);
                let mut r_left = (*n2l).clone_in(arena);
                l_left.constrain(&mut r_left, constr_map, prv_rels, arena)?;

                let mut l_right = (*n1r).clone_in(arena);
                let mut r_right = (*n2r).clone_in(arena);
                l_right.constrain(&mut r_right, constr_map, prv_rels, arena)?;

                Ok(())
            }
            (Nat::App(f1, ns1), Nat::App(f2, ns2)) if f1 == f2 => {
                if ns1.len() != ns2.len() {
                    return Err(UnifyError::CannotUnify);
                }
                for (n1, n2) in ns1.iter().zip(ns2.iter()) {
                    let mut l = n1.clone_in(arena);
                    let mut r = n2.clone_in(arena);
                    l.constrain(&mut r, constr_map, prv_rels, arena)?;
                }
                Ok(())
            }
            _ => Self::unify(self, other),
        }
    }
}

impl<'a> Substitutable<'a> for Nat<'a> {
    fn substitute(&mut self, subst: &ConstrainMap<'a>, arena: &'a Bump) {
        let mut apply_subst = ApplySubst::new(subst);
        apply_subst.visit_nat(arena, self);
    }
}

impl<'a> Memory<'a> {
    fn bind_to(
        &self,
        ident: &'a Ident<'a>,
        constr_map: &mut ConstrainMap<'a>,
        arena: &'a Bump,
    ) -> UnifyResult<'a, ()> {
        if Self::occurs_check(&IdentKinded::new(ident, Kind::Memory), self) {
            return Err(UnifyError::InfiniteType);
        }

        if let Memory::Ident(mem_id) = &self {
            if mem_id == ident {
                return Ok(());
            }
        }
        if let Some(old) = constr_map
            .mem_unifier
            .insert(ident.name.clone(), self.clone())
        {
            if &old != self {
                panic!(
                    "Attempting to bind same variable name twice.\n\
        Old value: `{:?}` replaced by new value: `{:?}`",
                    old, self
                )
            }
        }
        let term_ref: &'a Memory<'a> = arena.alloc(self.clone_in(arena));
        constr_map
            .mem_unifier
            .values_mut()
            .for_each(|m| SubstIdent::new(ident, term_ref).visit_mem(arena, m));
        Ok(())
    }
}

impl<'a> Constrainable<'a> for Memory<'a> {
    fn constrain<'m>(
        &'m mut self,
        other: &'m mut Self,
        constr_map: &'m mut ConstrainMap<'a>,
        _prv_rels: &'m mut BumpVec<'a, PrvConstr<'a>>,
        arena: &'a Bump,
    ) -> UnifyResult<'a, ()> {
        match (&*self, &*other) {
            (Memory::Ident(i1), Memory::Ident(i2)) if i1 == i2 => Ok(()),
            (Memory::Ident(i1), Memory::Ident(i2)) => match (i1.is_implicit, i2.is_implicit) {
                (true, _) => other.bind_to(arena.alloc(i1.clone()), constr_map, arena),
                (false, _) => self.bind_to(arena.alloc(i2.clone()), constr_map, arena),
            },
            (Memory::Ident(i), o) => o.bind_to(arena.alloc(i.clone()), constr_map, arena),
            (s, Memory::Ident(i)) => s.bind_to(arena.alloc(i.clone()), constr_map, arena),
            (mem1, mem2) if mem1 == mem2 => Ok(()),
            _ => Err(UnifyError::CannotUnify),
        }
    }
}

impl<'a> Substitutable<'a> for Memory<'a> {
    fn substitute(&mut self, subst: &ConstrainMap<'a>, arena: &'a Bump) {
        let mut apply_subst = ApplySubst::new(subst);
        apply_subst.visit_mem(arena, self);
    }
}

impl<'a> Provenance<'a> {
    fn bind_to(
        &self,
        ident: &'a Ident<'a>,
        constr_map: &mut ConstrainMap<'a>,
        arena: &'a Bump,
    ) -> UnifyResult<'a, ()> {
        // TODO not necessary, since no recursion possible
        if Self::occurs_check(&IdentKinded::new(ident, Kind::Provenance), self) {
            return Err(UnifyError::InfiniteType);
        }

        if let Provenance::Ident(prv_id) = &self {
            if prv_id == ident {
                return Ok(());
            }
        }
        if let Some(old) = constr_map
            .prv_unifier
            .insert(ident.name.clone(), self.clone())
        {
            if &old != self {
                panic!(
                    "Attempting to bind same variable name twice.\n\
        Old value: `{:?}` replaced by new value: `{:?}`",
                    old, self
                )
            }
        }
        let term_ref: &'a Provenance<'a> = arena.alloc(self.clone_in(arena));
        constr_map
            .prv_unifier
            .values_mut()
            .for_each(|m| SubstIdent::new(ident, term_ref).visit_prv(arena, m));
        Ok(())
    }
}

impl<'a> Constrainable<'a> for Provenance<'a> {
    fn constrain<'m>(
        &'m mut self,
        other: &'m mut Self,
        constr_map: &'m mut ConstrainMap<'a>,
        prv_rels: &'m mut BumpVec<'a, PrvConstr<'a>>,
        arena: &'a Bump,
    ) -> UnifyResult<'a, ()> {
        // TODO restructure cases for less?
        match (&*self, &*other) {
            (Provenance::Ident(i1), Provenance::Ident(i2)) if i1 == i2 => Ok(()),
            (Provenance::Ident(i), r) | (r, Provenance::Ident(i)) if i.is_implicit => {
                let i_ref: &'a Ident<'a> = arena.alloc(i.clone());
                r.bind_to(i_ref, constr_map, arena)
            }
            (Provenance::Ident(_), _) | (_, Provenance::Ident(_)) => {
                let l_ref: &'a Provenance<'a> = arena.alloc(self.clone_in(arena));
                let r_ref: &'a Provenance<'a> = arena.alloc(other.clone_in(arena));
                prv_rels.push(PrvConstr(l_ref, r_ref));
                Ok(())
            }
            (Provenance::Value(_), Provenance::Value(_)) => {
                let l_ref: &'a Provenance<'a> = arena.alloc(self.clone_in(arena));
                let r_ref: &'a Provenance<'a> = arena.alloc(other.clone_in(arena));
                prv_rels.push(PrvConstr(l_ref, r_ref));
                Ok(())
            }
        }
    }
}

impl<'a> Substitutable<'a> for Provenance<'a> {
    fn substitute(&mut self, subst: &ConstrainMap<'a>, arena: &'a Bump) {
        let mut apply_subst = ApplySubst::new(subst);
        apply_subst.visit_prv(arena, self);
    }
}

impl<'a> Substitutable<'a> for View<'a> {
    fn substitute(&mut self, subst: &ConstrainMap<'a>, arena: &'a Bump) {
        let mut apply_subst = ApplySubst::new(subst);
        apply_subst.visit_view(arena, self);
    }
}

pub(super) fn substitute<'a, 's, S: Substitutable<'a>>(
    subst: &'s ConstrainMap<'a>,
    s: &mut S,
    arena: &'a Bump,
) {
    s.substitute(subst, arena)
}

pub(super) struct ApplySubst<'s, 'a> {
    subst: &'s ConstrainMap<'a>,
}

impl<'s, 'a> ApplySubst<'s, 'a> {
    pub(super) fn new(subst: &'s ConstrainMap<'a>) -> Self {
        ApplySubst { subst }
    }
}

impl<'s, 'a> VisitMut<'a> for ApplySubst<'s, 'a> {
    fn visit_nat(&mut self, arena: &'a Bump, nat: &mut Nat<'a>) {
        match nat {
            Nat::Ident(ident) if self.subst.nat_unifier.contains_key(&ident.name) => {
                *nat = self.subst.nat_unifier.get(&ident.name).unwrap().clone();
            }
            _ => visit_mut::walk_nat(self, arena, nat),
        }
    }

    fn visit_mem(&mut self, arena: &'a Bump, mem: &mut Memory<'a>) {
        match mem {
            Memory::Ident(ident) if self.subst.mem_unifier.contains_key(&ident.name) => {
                *mem = self.subst.mem_unifier.get(&ident.name).unwrap().clone();
            }
            _ => visit_mut::walk_mem(self, arena, mem),
        }
    }

    fn visit_prv(&mut self, arena: &'a Bump, prv: &mut Provenance<'a>) {
        match prv {
            Provenance::Ident(ident) if self.subst.prv_unifier.contains_key(&ident.name) => {
                *prv = self.subst.prv_unifier.get(&ident.name).unwrap().clone()
            }
            _ => visit_mut::walk_prv(self, arena, prv),
        }
    }

    fn visit_dty(&mut self, arena: &'a Bump, dty: &mut DataTy<'a>) {
        match &mut dty.dty {
            DataTyKind::Ident(ident) if self.subst.dty_unifier.contains_key(&ident.name) => {
                *dty = self.subst.dty_unifier.get(&ident.name).unwrap().clone()
            }
            _ => visit_mut::walk_dty(self, arena, dty),
        }
    }
}

struct SubstIdent<'a, S: Constrainable<'a>> {
    ident: &'a Ident<'a>,
    term: &'a S,
}

impl<'a, S: Constrainable<'a>> SubstIdent<'a, S> {
    fn new(ident: &'a Ident, term: &'a S) -> Self {
        SubstIdent { ident, term }
    }
}

impl<'a> VisitMut<'a> for SubstIdent<'a, Nat<'a>> {
    fn visit_nat(&mut self, arena: &'a Bump, nat: &mut Nat<'a>) {
        match nat {
            Nat::Ident(ident) if ident.name == self.ident.name => *nat = self.term.clone(),
            _ => visit_mut::walk_nat(self, arena, nat),
        }
    }
}

impl<'a> VisitMut<'a> for SubstIdent<'a, Memory<'a>> {
    fn visit_mem(&mut self, arena: &'a Bump, mem: &mut Memory<'a>) {
        match mem {
            Memory::Ident(ident) if ident.name == self.ident.name => *mem = self.term.clone(),
            _ => visit_mut::walk_mem(self, arena, mem),
        }
    }
}

impl<'a> VisitMut<'a> for SubstIdent<'a, Provenance<'a>> {
    fn visit_prv(&mut self, arena: &'a Bump, prv: &mut Provenance<'a>) {
        match prv {
            Provenance::Ident(ident) if ident.name == self.ident.name => *prv = self.term.clone(),
            _ => visit_mut::walk_prv(self, arena, prv),
        }
    }
}

impl<'a> VisitMut<'a> for SubstIdent<'a, DataTy<'a>> {
    fn visit_dty(&mut self, arena: &'a Bump, dty: &mut DataTy<'a>) {
        match &mut dty.dty {
            DataTyKind::Ident(ident) if ident.name == self.ident.name => *dty = self.term.clone(),
            _ => visit_mut::walk_dty(self, arena, dty),
        }
    }
}

/**
impl<'a> VisitMut<'a> for SubstIdent<'a, ExecExpr<'a>> {
    fn visit_exec_expr(&mut self, arena: &'a Bump, exec: &mut ExecExpr<'a>) {
        if let BaseExec::Ident(i) = &exec.exec.base {
            if i.name == self.ident.name {
                let mut subst_exec = self.term.clone();
                subst_exec.exec.path.append(&mut exec.exec.path);
                *exec = subst_exec;
            }
        }
    }
}
*/

impl<'a> VisitMut<'a> for SubstIdent<'a, ExecExpr<'a>> {
    fn visit_exec_expr(&mut self, arena: &'a Bump, exec: &mut ExecExpr<'a>) {
        use crate::arena_ast::{BaseExec, ExecExpr, ExecExprKind};

        if let BaseExec::Ident(i) = &exec.exec.base {
            if i.name == self.ident.name {
                let mut merged = bumpalo::collections::Vec::new_in(arena);

                for e in self.term.exec.path.iter() {
                    merged.push(e.clone_in(arena));
                }
                for e in exec.exec.path.iter() {
                    merged.push(e.clone_in(arena));
                }

                let new_kind = arena.alloc(ExecExprKind {
                    base: self.term.exec.base.clone_in(arena),
                    path: merged,
                });

                *exec = ExecExpr {
                    exec: new_kind,
                    ty: exec.ty,
                    span: exec.span,
                };

                return;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn shrd_ref_ty<'a>() -> DataTy<'a> {
        Dim::X(Box::new(Dim1d(Nat::Lit(32))));
        DataTy::new(DataTyKind::Ref(Box::new(RefDty::new(
            Provenance::Value("r".to_string()),
            Ownership::Shrd,
            Memory::GpuGlobal,
            DataTy::new(DataTyKind::Array(
                Box::new(DataTy::new(DataTyKind::Scalar(ScalarTy::I32))),
                Nat::Ident(Ident::new("n")),
            )),
        ))))
    }

    #[test]
    fn scalar<'a>() -> UnifyResult<'a, ()> {
        let mut i32 = DataTy::new(DataTyKind::Scalar(ScalarTy::I32));
        let mut t = DataTy::new(DataTyKind::Ident(Ident::new_impli("t")));
        let (subst, _) = constrain(&mut i32, &mut t)?;
        substitute(&subst, &mut i32);
        substitute(&subst, &mut t);
        assert_eq!(i32, t);
        Ok(())
    }

    #[test]
    fn shrd_reft<'a>() -> UnifyResult<'a, ()> {
        let mut t = DataTy::new(DataTyKind::Ident(Ident::new_impli("t")));
        let mut shrd_ref = shrd_ref_ty();
        let (subst, _) = constrain(&mut shrd_ref, &mut t)?;
        substitute(&subst, &mut shrd_ref);
        substitute(&subst, &mut t);
        assert_eq!(shrd_ref, t);
        Ok(())
    }

    #[test]
    fn shrd_ref_inner_var<'a>() -> UnifyResult<'a, ()> {
        let mut shrd_ref_t = DataTy::new(DataTyKind::Ref(Box::new(RefDty::new(
            Provenance::Value("r".to_string()),
            Ownership::Shrd,
            Memory::GpuGlobal,
            DataTy::new(DataTyKind::Ident(Ident::new_impli("t"))),
        ))));
        let mut shrd_ref = shrd_ref_ty();
        let (subst, _) = constrain(&mut shrd_ref, &mut shrd_ref_t)?;
        println!("{:?}", subst);
        substitute(&subst, &mut shrd_ref);
        substitute(&subst, &mut shrd_ref_t);
        assert_eq!(shrd_ref, shrd_ref_t);
        Ok(())
    }

    #[test]
    fn prv_val_ident<'a>() -> UnifyResult<'a, ()> {
        let mut shrd_ref_t = DataTy::new(DataTyKind::Ref(Box::new(RefDty::new(
            Provenance::Ident(Ident::new("a")),
            Ownership::Shrd,
            Memory::GpuGlobal,
            DataTy::new(DataTyKind::Ident(Ident::new_impli("t"))),
        ))));
        let mut shrd_ref = shrd_ref_ty();
        let (subst, prv_rels) = constrain(&mut shrd_ref, &mut shrd_ref_t)?;
        println!("{:?}", subst);
        substitute(&subst, &mut shrd_ref);
        substitute(&subst, &mut shrd_ref_t);
        assert_eq!(
            prv_rels[0],
            PrvConstr(
                Provenance::Value("r".to_string()),
                Provenance::Ident(Ident::new("a"))
            )
        );
        Ok(())
    }
}
