use crate::ast::utils;
use crate::ast::utils::Visitable;
use crate::ast::visit_mut::VisitMut;
use crate::ast::*;
use crate::ty_check::ctxs::{KindCtx, TyCtx};
use crate::ty_check::error::UnifyError;
use crate::ty_check::subty;
use std::collections::HashMap;

type UnifyResult<T> = Result<T, UnifyError>;

pub(super) fn unify<C: Constrainable>(t1: &mut C, t2: &mut C) -> UnifyResult<()> {
    let (_, _) = constrain(t1, t2)?;
    Ok(())
}

pub(super) fn sub_unify<C: Constrainable>(
    kind_ctx: &KindCtx,
    ty_ctx: &mut TyCtx,
    sub: &mut C,
    sup: &mut C,
) -> UnifyResult<()> {
    let (_, prv_rels) = constrain(sub, sup)?;
    subty::multiple_outlives(
        kind_ctx,
        ty_ctx,
        prv_rels.iter().map(|PrvConstr(p1, p2)| (p1, p2)),
    )?;
    Ok(())
}

pub(super) fn constrain<S: Constrainable>(
    t1: &mut S,
    t2: &mut S,
) -> UnifyResult<(ConstrainMap, Vec<PrvConstr>)> {
    let mut constr_map = ConstrainMap::new();
    let mut prv_rels = Vec::new();
    t1.constrain(t2, &mut constr_map, &mut prv_rels)?;
    Ok((constr_map, prv_rels))
}

pub(super) fn inst_fn_ty_scheme(fn_ty: &FnTy) -> FnTy {
    assert!(
        fn_ty.generic_exec.is_none(),
        "exec must be substituted before instantiation to make sure that it has the correct type"
    );
    let mono_idents: Vec<_> = fn_ty
        .generics
        .iter()
        .map(|i| match i.kind {
            Kind::DataTy => ArgKinded::DataTy(DataTy::new(utils::fresh_ident(
                &i.ident.name,
                DataTyKind::Ident,
            ))),
            Kind::Nat => ArgKinded::Nat(utils::fresh_ident(&i.ident.name, Nat::Ident)),
            Kind::Memory => ArgKinded::Memory(utils::fresh_ident(&i.ident.name, Memory::Ident)),
            Kind::Provenance => {
                ArgKinded::Provenance(utils::fresh_ident(&i.ident.name, Provenance::Ident))
            }
        })
        .collect();
    let mut inst_fn_ty = fn_ty.clone();
    let generics = inst_fn_ty.generics.drain(..).collect::<Vec<_>>();
    utils::subst_idents_kinded(generics.iter(), mono_idents.iter(), &mut inst_fn_ty);
    inst_fn_ty
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub(super) struct PrvConstr(pub Provenance, pub Provenance);

#[derive(Debug)]
pub(super) struct ConstrainMap {
    // TODO swap Box<str> for something more abstract, like Symbol or Identifier
    pub dty_unifier: HashMap<Box<str>, DataTy>,
    pub nat_unifier: HashMap<Box<str>, Nat>,
    pub mem_unifier: HashMap<Box<str>, Memory>,
    pub prv_unifier: HashMap<Box<str>, Provenance>,
}

impl ConstrainMap {
    fn new() -> Self {
        ConstrainMap {
            dty_unifier: HashMap::new(),
            nat_unifier: HashMap::new(),
            mem_unifier: HashMap::new(),
            prv_unifier: HashMap::new(),
        }
    }
}

impl DataTy {
    fn bind_to(&self, ident: &Ident, constr_map: &mut ConstrainMap) -> UnifyResult<()> {
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
        constr_map
            .dty_unifier
            .values_mut()
            .for_each(|dty| SubstIdent::new(ident, self).visit_dty(dty));
        Ok(())
    }
}

pub(super) trait Constrainable: Visitable {
    fn constrain(
        &mut self,
        other: &mut Self,
        constr_map: &mut ConstrainMap,
        prv_rels: &mut Vec<PrvConstr>,
    ) -> UnifyResult<()>;
    fn substitute(&mut self, subst: &ConstrainMap);
    fn occurs_check<S: Constrainable>(ident_kinded: &IdentKinded, s: &S) -> bool {
        utils::free_kinded_idents(s).contains(ident_kinded)
    }
}

impl Constrainable for FnTy {
    fn constrain(
        &mut self,
        other: &mut Self,
        constr_map: &mut ConstrainMap,
        prv_rels: &mut Vec<PrvConstr>,
    ) -> UnifyResult<()> {
        assert!(self.generics.is_empty());
        assert!(other.generics.is_empty());
        assert!(self.generic_exec.is_none());
        assert!(other.generic_exec.is_none());

        self.exec.constrain(&mut other.exec, constr_map, prv_rels)?;
        substitute(constr_map, self);
        substitute(constr_map, other);

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
            next_lhs.constrain(next_rhs, constr_map, prv_rels)?;
            substitute(constr_map, self);
            substitute(constr_map, other);

            i += 1;
            remain_lhs = &mut self.param_sigs[i..];
            remain_rhs = &mut other.param_sigs[i..];
        }
        self.ret_ty
            .constrain(&mut other.ret_ty, constr_map, prv_rels)?;
        substitute(constr_map, self);
        substitute(constr_map, other);
        Ok(())
    }

    fn substitute(&mut self, subst: &ConstrainMap) {
        let mut apply_subst = ApplySubst::new(subst);
        apply_subst.visit_fn_ty(self);
    }
}

impl Constrainable for ParamSig {
    fn constrain(
        &mut self,
        other: &mut Self,
        constr_map: &mut ConstrainMap,
        prv_rels: &mut Vec<PrvConstr>,
    ) -> UnifyResult<()> {
        self.exec_expr
            .constrain(&mut other.exec_expr, constr_map, prv_rels)?;
        substitute(constr_map, self);
        substitute(constr_map, other);
        self.ty.constrain(&mut other.ty, constr_map, prv_rels)?;
        substitute(constr_map, self);
        substitute(constr_map, other);
        Ok(())
    }

    fn substitute(&mut self, subst: &ConstrainMap) {
        let mut apply_subst = ApplySubst::new(subst);
        apply_subst.visit_param_sig(self);
    }
}

// TODO unification for exec expressions necessary for Nats? Can this be moved into a separate
//  equality check?
impl Constrainable for ExecExpr {
    fn constrain(
        &mut self,
        other: &mut Self,
        constr_map: &mut ConstrainMap,
        prv_rels: &mut Vec<PrvConstr>,
    ) -> UnifyResult<()> {
        match (&mut self.exec.base, &mut other.exec.base) {
            (BaseExec::Ident(i1), BaseExec::Ident(i2)) => {
                assert!(
                    !i1.is_implicit,
                    "Implicit identifier for exec expression should not exist"
                );
                assert!(
                    !i2.is_implicit,
                    "Implicit identifier for exec expression should not exist"
                );
                if i1 == i2 {
                    return Ok(());
                } else {
                    return Err(UnifyError::CannotUnify);
                }
            }
            (BaseExec::CpuThread, BaseExec::CpuThread) => {}
            (BaseExec::GpuGrid(gdim1, bdim1), BaseExec::GpuGrid(gdim2, bdim2)) => {
                gdim1.constrain(gdim2, constr_map, prv_rels)?;
                bdim1.constrain(bdim2, constr_map, prv_rels)?;
            }
            _ => return Err(UnifyError::CannotUnify),
        }

        let mut i = 0;
        let mut remain_lhs = &mut self.exec.path[i..];
        let mut remain_rhs = &mut other.exec.path[i..];
        while let (Some((next_lhs, tail_lhs)), Some((next_rhs, tail_rhs))) =
            (remain_lhs.split_first_mut(), remain_rhs.split_first_mut())
        {
            tail_lhs.iter_mut().for_each(|ep| {
                let mut apply_subst = ApplySubst::new(constr_map);
                apply_subst.visit_exec_path_elem(ep);
            });
            tail_rhs.iter_mut().for_each(|ep| {
                let mut apply_subst = ApplySubst::new(constr_map);
                apply_subst.visit_exec_path_elem(ep);
            });

            match (next_lhs, next_rhs) {
                (ExecPathElem::ForAll(dl), ExecPathElem::ForAll(dr))
                | (ExecPathElem::ToThreads(dl), ExecPathElem::ToThreads(dr)) => {
                    if dl != dr {
                        return Err(UnifyError::CannotUnify);
                    }
                }
                (ExecPathElem::TakeRange(rl), ExecPathElem::TakeRange(rr)) => {
                    if rl.split_dim != rr.split_dim {
                        return Err(UnifyError::CannotUnify);
                    }
                    if rl.left_or_right != rr.left_or_right {
                        return Err(UnifyError::CannotUnify);
                    }
                    rl.pos.constrain(&mut rr.pos, constr_map, prv_rels)?
                }
                (ExecPathElem::ToWarps, ExecPathElem::ToWarps) => {}
                _ => return Err(UnifyError::CannotUnify),
            }

            i += 1;
            remain_lhs = &mut self.exec.path[i..];
            remain_rhs = &mut other.exec.path[i..];
        }
        Ok(())
    }

    fn substitute(&mut self, subst: &ConstrainMap) {
        let mut apply_subst = ApplySubst::new(subst);
        apply_subst.visit_exec_expr(self);
    }
}

impl Constrainable for Ty {
    fn constrain(
        &mut self,
        other: &mut Self,
        constr_map: &mut ConstrainMap,
        prv_rels: &mut Vec<PrvConstr>,
    ) -> UnifyResult<()> {
        match (&mut self.ty, &mut other.ty) {
            (TyKind::FnTy(fn_ty1), TyKind::FnTy(fn_ty2)) => {
                fn_ty1.constrain(fn_ty2, constr_map, prv_rels)
            }
            (TyKind::Data(dty1), TyKind::Data(dty2)) => dty1.constrain(dty2, constr_map, prv_rels),
            _ => Err(UnifyError::CannotUnify),
        }
    }

    fn substitute(&mut self, subst: &ConstrainMap) {
        let mut apply_subst = ApplySubst::new(subst);
        apply_subst.visit_ty(self);
    }
}

impl Constrainable for DataTy {
    fn constrain(
        &mut self,
        other: &mut Self,
        constr_map: &mut ConstrainMap,
        prv_rels: &mut Vec<PrvConstr>,
    ) -> UnifyResult<()> {
        match (&mut self.dty, &mut other.dty) {
            (DataTyKind::Ident(i1), DataTyKind::Ident(i2)) => {
                if i1.is_implicit {
                    other.bind_to(i1, constr_map)?
                } else if i2.is_implicit {
                    self.bind_to(i2, constr_map)?
                } else if i1 == i2 {
                    return Ok(());
                } else {
                    return Err(UnifyError::CannotUnify);
                }
                substitute(constr_map, self);
                substitute(constr_map, other);
            }
            (DataTyKind::Ident(i), _) if i.is_implicit => {
                other.bind_to(i, constr_map)?;
                substitute(constr_map, other);
            }
            (_, DataTyKind::Ident(i)) if i.is_implicit => {
                self.bind_to(i, constr_map)?;
                substitute(constr_map, self);
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
                } = ref1.as_mut();
                let RefDty {
                    rgn: rgn2,
                    own: own2,
                    mem: mem2,
                    dty: dty2,
                } = ref2.as_mut();

                if own1 != own2 {
                    return Err(UnifyError::CannotUnify);
                }
                rgn1.constrain(rgn2, constr_map, prv_rels)?;
                substitute(constr_map, &mut **dty1);
                substitute(constr_map, &mut **dty2);
                mem1.constrain(mem2, constr_map, prv_rels)?;
                substitute(constr_map, mem1);
                substitute(constr_map, mem2);
                substitute(constr_map, &mut **dty1);
                substitute(constr_map, &mut **dty2);
                dty1.constrain(dty2, constr_map, prv_rels)?;
                substitute(constr_map, self);
                substitute(constr_map, other);
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
                    next_lhs.constrain(next_rhs, constr_map, prv_rels)?;
                    for (dty1, dty2) in elem_dtys1.iter_mut().zip(elem_dtys2.iter_mut()) {
                        substitute(constr_map, dty1);
                        substitute(constr_map, dty2);
                    }

                    i += 1;
                    remain_lhs = &mut elem_dtys1[i..];
                    remain_rhs = &mut elem_dtys2[i..];
                }
            }
            (DataTyKind::Array(dty1, n1), DataTyKind::Array(dty2, n2))
            | (DataTyKind::ArrayShape(dty1, n1), DataTyKind::ArrayShape(dty2, n2)) => {
                dty1.constrain(dty2, constr_map, prv_rels)?;
                substitute(constr_map, &mut **dty1);
                substitute(constr_map, &mut **dty2);
                n1.constrain(n2, constr_map, prv_rels)?;
                substitute(constr_map, self);
                substitute(constr_map, other);
            }
            (DataTyKind::At(dty1, mem1), DataTyKind::At(dty2, mem2)) => {
                dty1.constrain(dty2, constr_map, prv_rels)?;
                substitute(constr_map, &mut **dty1);
                substitute(constr_map, &mut **dty2);
                mem1.constrain(mem2, constr_map, prv_rels)?;
                substitute(constr_map, self);
                substitute(constr_map, other);
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
                self.constrain(dty2, constr_map, prv_rels)?;
                substitute(constr_map, self);
                substitute(constr_map, other);
            }
            _ => return Err(UnifyError::CannotUnify),
        }
        Ok(())
    }

    fn substitute(&mut self, subst: &ConstrainMap) {
        let mut apply_subst = ApplySubst::new(subst);
        apply_subst.visit_dty(self);
    }
}

impl Constrainable for ExecTy {
    fn constrain(
        &mut self,
        other: &mut Self,
        constr_map: &mut ConstrainMap,
        prv_rels: &mut Vec<PrvConstr>,
    ) -> UnifyResult<()> {
        match (&mut self.ty, &mut other.ty) {
            (ExecTyKind::CpuThread, ExecTyKind::CpuThread)
            | (ExecTyKind::GpuThread, ExecTyKind::GpuThread)
            | (ExecTyKind::GpuWarp, ExecTyKind::GpuWarp)
            | (_, ExecTyKind::Any) => Ok(()),
            (ExecTyKind::GpuWarpGrp(nl), ExecTyKind::GpuWarpGrp(nr)) => {
                nl.constrain(nr, constr_map, prv_rels)
            }
            (ExecTyKind::GpuGrid(lgdim, lbdim), ExecTyKind::GpuGrid(rgdim, rbdim))
            | (ExecTyKind::GpuBlockGrp(lgdim, lbdim), ExecTyKind::GpuBlockGrp(rgdim, rbdim)) => {
                lgdim.constrain(rgdim, constr_map, prv_rels)?;
                lbdim.constrain(rbdim, constr_map, prv_rels)
            }
            (
                ExecTyKind::GpuToThreads(ldim_compo, l_inner),
                ExecTyKind::GpuToThreads(rdim_compo, r_inner),
            ) => {
                if ldim_compo != rdim_compo {
                    return Err(UnifyError::CannotUnify);
                }
                l_inner.constrain(r_inner, constr_map, prv_rels)
            }
            (ExecTyKind::GpuBlock(ldim), ExecTyKind::GpuBlock(rdim))
            | (ExecTyKind::GpuThreadGrp(ldim), ExecTyKind::GpuThreadGrp(rdim)) => {
                ldim.constrain(rdim, constr_map, prv_rels)
            }
            _ => Err(UnifyError::CannotUnify),
        }
    }

    fn substitute(&mut self, subst: &ConstrainMap) {
        let mut apply_subst = ApplySubst::new(subst);
        apply_subst.visit_exec_ty(self);
    }
}

impl Constrainable for Dim {
    fn constrain(
        &mut self,
        other: &mut Self,
        constr_map: &mut ConstrainMap,
        prv_rels: &mut Vec<PrvConstr>,
    ) -> UnifyResult<()> {
        match (self, other) {
            (Dim::XYZ(ldim), Dim::XYZ(rdim)) => {
                ldim.0.constrain(&mut rdim.0, constr_map, prv_rels)?;
                ldim.1.constrain(&mut rdim.1, constr_map, prv_rels)?;
                ldim.2.constrain(&mut rdim.2, constr_map, prv_rels)
            }
            (Dim::XY(ldim), Dim::XY(rdim))
            | (Dim::XZ(ldim), Dim::XZ(rdim))
            | (Dim::YZ(ldim), Dim::YZ(rdim)) => {
                ldim.0.constrain(&mut rdim.0, constr_map, prv_rels)?;
                ldim.1.constrain(&mut rdim.1, constr_map, prv_rels)
            }
            (Dim::X(ld), Dim::X(rd)) | (Dim::Y(ld), Dim::Y(rd)) | (Dim::Z(ld), Dim::Z(rd)) => {
                ld.0.constrain(&mut rd.0, constr_map, prv_rels)
            }
            _ => Err(UnifyError::CannotUnify),
        }
    }

    fn substitute(&mut self, subst: &ConstrainMap) {
        let mut apply_subst = ApplySubst::new(subst);
        apply_subst.visit_dim(self);
    }
}

impl Nat {
    fn bind_to(
        &self,
        ident: &Ident,
        constr_map: &mut ConstrainMap,
        _: &mut Vec<PrvConstr>,
    ) -> UnifyResult<()> {
        // No occurs check.
        // Nats can be equal to an expression in which the nat appears again. E.g., a = a * 1
        if let Some(old) = constr_map
            .nat_unifier
            .insert(ident.name.clone(), self.clone())
        {
            if &old != self {
                println!(
                    "WARNING: Not able to check equality of Nats `{}` and `{}`",
                    old, self
                )
            }
        }
        constr_map
            .nat_unifier
            .values_mut()
            .for_each(|n| SubstIdent::new(ident, self).visit_nat(n));
        Ok(())
    }

    fn unify(n1: &Nat, n2: &Nat, _constr_map: &mut ConstrainMap) -> UnifyResult<()> {
        if n1 == n2 {
            Ok(())
        } else {
            println!(
                "WARNING: Not able to check equality of Nats `{}` and `{}`",
                n1, n2
            );
            Ok(())
        }
    }
}

impl Constrainable for Nat {
    fn constrain(
        &mut self,
        other: &mut Self,
        constr_map: &mut ConstrainMap,
        prv_rels: &mut Vec<PrvConstr>,
    ) -> UnifyResult<()> {
        match (&mut *self, &mut *other) {
            (Nat::Ident(n1i), Nat::Ident(n2i)) if n1i.is_implicit || n2i.is_implicit => {
                match (n1i.is_implicit, n2i.is_implicit) {
                    (true, _) => other.bind_to(n1i, constr_map, prv_rels),
                    (false, _) => self.bind_to(n2i, constr_map, prv_rels),
                }
            }
            (Nat::Ident(n1i), _) if n1i.is_implicit => other.bind_to(n1i, constr_map, prv_rels),
            (_, Nat::Ident(n2i)) if n2i.is_implicit => self.bind_to(n2i, constr_map, prv_rels),
            (Nat::BinOp(op1, n1l, n1r), Nat::BinOp(op2, n2l, n2r)) if op1 == op2 => {
                n1l.constrain(n2l, constr_map, prv_rels)?;
                n1r.constrain(n2r, constr_map, prv_rels)
            }
            (Nat::App(f1, ns1), Nat::App(f2, ns2)) if f1 == f2 => {
                for (n1, n2) in ns1.iter_mut().zip(ns2.iter_mut()) {
                    n1.constrain(n2, constr_map, prv_rels)?;
                }
                Ok(())
            }
            _ => Self::unify(self, other, constr_map),
        }
    }

    fn substitute(&mut self, subst: &ConstrainMap) {
        let mut apply_subst = ApplySubst::new(subst);
        apply_subst.visit_nat(self);
    }
}

impl Memory {
    fn bind_to(&self, ident: &Ident, constr_map: &mut ConstrainMap) -> UnifyResult<()> {
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
        constr_map
            .mem_unifier
            .values_mut()
            .for_each(|m| SubstIdent::new(ident, self).visit_mem(m));
        Ok(())
    }
}

impl Constrainable for Memory {
    fn constrain(
        &mut self,
        other: &mut Self,
        constr_map: &mut ConstrainMap,
        _prv_rels: &mut Vec<PrvConstr>,
    ) -> UnifyResult<()> {
        match (&*self, &*other) {
            (Memory::Ident(i1), Memory::Ident(i2)) if i1 == i2 => Ok(()),
            (Memory::Ident(i1), Memory::Ident(i2)) => match (i1.is_implicit, i2.is_implicit) {
                (true, _) => other.bind_to(i1, constr_map),
                (false, _) => self.bind_to(i2, constr_map),
            },
            (Memory::Ident(i), o) => o.bind_to(i, constr_map),
            (s, Memory::Ident(i)) => s.bind_to(i, constr_map),
            (mem1, mem2) if mem1 == mem2 => Ok(()),
            _ => Err(UnifyError::CannotUnify),
        }
    }

    fn substitute(&mut self, subst: &ConstrainMap) {
        let mut apply_subst = ApplySubst::new(subst);
        apply_subst.visit_mem(self);
    }
}

impl Provenance {
    fn bind_to(&self, ident: &Ident, constr_map: &mut ConstrainMap) -> UnifyResult<()> {
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
        constr_map
            .prv_unifier
            .values_mut()
            .for_each(|m| SubstIdent::new(ident, self).visit_prv(m));
        Ok(())
    }
}

impl Constrainable for Provenance {
    fn constrain(
        &mut self,
        other: &mut Self,
        constr_map: &mut ConstrainMap,
        prv_rels: &mut Vec<PrvConstr>,
    ) -> UnifyResult<()> {
        // TODO restructure cases for less?
        match (&*self, &*other) {
            (Provenance::Ident(i1), Provenance::Ident(i2)) if i1 == i2 => Ok(()),
            (Provenance::Ident(i), r) | (r, Provenance::Ident(i)) if i.is_implicit => {
                r.bind_to(i, constr_map)
            }
            (Provenance::Ident(_), _) | (_, Provenance::Ident(_)) => {
                prv_rels.push(PrvConstr(self.clone(), other.clone()));
                Ok(())
            }
            (Provenance::Value(_), Provenance::Value(_)) => {
                prv_rels.push(PrvConstr(self.clone(), other.clone()));
                Ok(())
            }
        }
    }

    fn substitute(&mut self, subst: &ConstrainMap) {
        let mut apply_subst = ApplySubst::new(subst);
        apply_subst.visit_prv(self);
    }
}

pub(super) fn substitute<C: Constrainable>(subst: &ConstrainMap, c: &mut C) {
    c.substitute(subst)
}

struct ApplySubst<'a> {
    subst: &'a ConstrainMap,
}

impl<'a> ApplySubst<'a> {
    fn new(subst: &'a ConstrainMap) -> Self {
        ApplySubst { subst }
    }
}

impl<'a> VisitMut for ApplySubst<'a> {
    fn visit_nat(&mut self, nat: &mut Nat) {
        match nat {
            Nat::Ident(ident) if self.subst.nat_unifier.contains_key(&ident.name) => {
                *nat = self.subst.nat_unifier.get(&ident.name).unwrap().clone();
            }
            _ => visit_mut::walk_nat(self, nat),
        }
    }

    fn visit_mem(&mut self, mem: &mut Memory) {
        match mem {
            Memory::Ident(ident) if self.subst.mem_unifier.contains_key(&ident.name) => {
                *mem = self.subst.mem_unifier.get(&ident.name).unwrap().clone();
            }
            _ => visit_mut::walk_mem(self, mem),
        }
    }

    fn visit_prv(&mut self, prv: &mut Provenance) {
        match prv {
            Provenance::Ident(ident) if self.subst.prv_unifier.contains_key(&ident.name) => {
                *prv = self.subst.prv_unifier.get(&ident.name).unwrap().clone()
            }
            _ => visit_mut::walk_prv(self, prv),
        }
    }

    fn visit_dty(&mut self, dty: &mut DataTy) {
        match &mut dty.dty {
            DataTyKind::Ident(ident) if self.subst.dty_unifier.contains_key(&ident.name) => {
                *dty = self.subst.dty_unifier.get(&ident.name).unwrap().clone()
            }
            _ => visit_mut::walk_dty(self, dty),
        }
    }
}

struct SubstIdent<'a, S: Constrainable> {
    ident: &'a Ident,
    term: &'a S,
}

impl<'a, S: Constrainable> SubstIdent<'a, S> {
    fn new(ident: &'a Ident, term: &'a S) -> Self {
        SubstIdent { ident, term }
    }
}

impl<'a> VisitMut for SubstIdent<'a, Nat> {
    fn visit_nat(&mut self, nat: &mut Nat) {
        match nat {
            Nat::Ident(ident) if ident.name == self.ident.name => *nat = self.term.clone(),
            _ => visit_mut::walk_nat(self, nat),
        }
    }
}

impl<'a> VisitMut for SubstIdent<'a, Memory> {
    fn visit_mem(&mut self, mem: &mut Memory) {
        match mem {
            Memory::Ident(ident) if ident.name == self.ident.name => *mem = self.term.clone(),
            _ => visit_mut::walk_mem(self, mem),
        }
    }
}

impl<'a> VisitMut for SubstIdent<'a, Provenance> {
    fn visit_prv(&mut self, prv: &mut Provenance) {
        match prv {
            Provenance::Ident(ident) if ident.name == self.ident.name => *prv = self.term.clone(),
            _ => visit_mut::walk_prv(self, prv),
        }
    }
}

impl<'a> VisitMut for SubstIdent<'a, DataTy> {
    fn visit_dty(&mut self, dty: &mut DataTy) {
        match &mut dty.dty {
            DataTyKind::Ident(ident) if ident.name == self.ident.name => *dty = self.term.clone(),
            _ => visit_mut::walk_dty(self, dty),
        }
    }
}

impl<'a> VisitMut for SubstIdent<'a, ExecExpr> {
    fn visit_exec_expr(&mut self, exec: &mut ExecExpr) {
        if let BaseExec::Ident(i) = &exec.exec.base {
            if i.name == self.ident.name {
                let mut subst_exec = self.term.clone();
                subst_exec.exec.path.append(&mut exec.exec.path);
                *exec = subst_exec;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn shrd_ref_ty() -> DataTy {
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
    fn scalar() -> UnifyResult<()> {
        let mut i32 = DataTy::new(DataTyKind::Scalar(ScalarTy::I32));
        let mut t = DataTy::new(DataTyKind::Ident(Ident::new_impli("t")));
        let (subst, _) = constrain(&mut i32, &mut t)?;
        substitute(&subst, &mut i32);
        substitute(&subst, &mut t);
        assert_eq!(i32, t);
        Ok(())
    }

    #[test]
    fn shrd_reft() -> UnifyResult<()> {
        let mut t = DataTy::new(DataTyKind::Ident(Ident::new_impli("t")));
        let mut shrd_ref = shrd_ref_ty();
        let (subst, _) = constrain(&mut shrd_ref, &mut t)?;
        substitute(&subst, &mut shrd_ref);
        substitute(&subst, &mut t);
        assert_eq!(shrd_ref, t);
        Ok(())
    }

    #[test]
    fn shrd_ref_inner_var() -> UnifyResult<()> {
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
    fn prv_val_ident() -> UnifyResult<()> {
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
