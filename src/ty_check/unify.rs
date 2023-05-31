use crate::ast::utils;
use crate::ast::utils::Visitable;
use crate::ast::visit_mut::VisitMut;
use crate::ast::*;
use crate::ty_check::ctxs::{KindCtx, TyCtx};
use crate::ty_check::error::UnifyError;
use crate::ty_check::subty;
use std::collections::HashMap;

type UnifyResult<T> = Result<T, UnifyError>;

pub(super) fn unify<C: Unifyable>(t1: &mut C, t2: &mut C) -> UnifyResult<()> {
    let (subst, _) = constrain(t1, t2)?;
    substitute(&subst, t1);
    substitute(&subst, t2);
    Ok(())
}

pub(super) fn sub_unify<C: Unifyable>(
    kind_ctx: &KindCtx,
    ty_ctx: &mut TyCtx,
    sub: &mut C,
    sup: &mut C,
) -> UnifyResult<()> {
    let (subst, prv_rels) = constrain(sub, sup)?;
    substitute(&subst, sub);
    substitute(&subst, sup);
    subty::multiple_outlives(
        kind_ctx,
        ty_ctx,
        prv_rels.iter().map(|PrvConstr(p1, p2)| (p1, p2)),
    )?;
    Ok(())
}

fn constrain<S: Unifyable>(t1: &mut S, t2: &mut S) -> UnifyResult<(ConstrainMap, Vec<PrvConstr>)> {
    let mut constr_map = ConstrainMap::new();
    let mut prv_rels = Vec::new();
    t1.constrain(t2, &mut constr_map, &mut prv_rels)?;
    Ok((constr_map, prv_rels))
}

pub(super) fn inst_fn_ty_scheme(
    idents_kinded: &[IdentKinded],
    idents_typed: &[IdentTyped],
    exec_ty: &ExecTy,
    ret_dty: &DataTy,
) -> FnTy {
    let mono_idents: Vec<_> = idents_kinded
        .iter()
        .map(|i| match i.kind {
            Kind::DataTy => GenArg::DataTy(DataTy::new(utils::fresh_ident(
                &i.ident.name,
                DataTyKind::Ident,
            ))),
            Kind::Nat => GenArg::Nat(utils::fresh_ident(&i.ident.name, Nat::Ident)),
            Kind::Memory => GenArg::Memory(utils::fresh_ident(&i.ident.name, Memory::Ident)),
            Kind::Provenance => {
                GenArg::Provenance(utils::fresh_ident(&i.ident.name, Provenance::Ident))
            }
        })
        .collect();

    let mut mono_idents_typed = idents_typed.to_vec();
    for ident_typed in &mut mono_idents_typed {
        utils::subst_idents_kinded(idents_kinded, mono_idents.as_slice(), &mut ident_typed.dty);
    }
    let mut mono_ret_dty = ret_dty.clone();
    utils::subst_idents_kinded(idents_kinded, mono_idents.as_slice(), &mut mono_ret_dty);

    FnTy::new(vec![], mono_idents_typed, exec_ty.clone(), mono_ret_dty)
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub(super) struct PrvConstr(pub Provenance, pub Provenance);

#[derive(Debug)]
pub(super) struct ConstrainMap {
    pub dty_unifier: HashMap<Box<str>, DataTy>,
    pub mem_unifier: HashMap<Box<str>, Memory>,
    pub prv_unifier: HashMap<Box<str>, Provenance>,
    pub nat_constraints: Vec<Constraint>,
}

impl ConstrainMap {
    fn new() -> Self {
        ConstrainMap {
            dty_unifier: HashMap::new(),
            mem_unifier: HashMap::new(),
            prv_unifier: HashMap::new(),
            nat_constraints: Vec::new(),
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

pub(super) trait Unifyable: Visitable {
    fn constrain(
        &mut self,
        other: &mut Self,
        constr_map: &mut ConstrainMap,
        prv_rels: &mut Vec<PrvConstr>,
    ) -> UnifyResult<()>;
    fn substitute(&mut self, subst: &ConstrainMap);
    fn occurs_check<S: Unifyable>(ident_kinded: &IdentKinded, s: &S) -> bool {
        utils::free_kinded_idents(s).contains(ident_kinded)
    }
}

// TODO must inline identifiers into following types
fn unify_param_list<C>(
    dtysl: Vec<&mut C>,
    dtysr: Vec<&mut C>,
    constr_map: &mut ConstrainMap,
    prv_rels: &mut Vec<PrvConstr>,
) -> UnifyResult<()>
where
    C: Unifyable,
{
    if dtysl.len() != dtysr.len() {
        return Err(UnifyError::CannotUnify);
    }
    // substitute result of unification for every following unification
    let mut i = 0;
    let mut remain_lhs = &mut dtysl[i..];
    let mut remain_rhs = &mut dtysr[i..];
    while let (Some((next_lhs, tail_lhs)), Some((next_rhs, tail_rhs))) =
        (remain_lhs.split_first_mut(), remain_rhs.split_first_mut())
    {
        next_lhs.constrain(next_rhs, constr_map, prv_rels)?;
        tail_lhs
            .iter_mut()
            .for_each(|ldty| substitute(constr_map, *ldty));
        tail_rhs
            .iter_mut()
            .for_each(|rdty| substitute(constr_map, *rdty));

        i += 1;
        remain_lhs = &mut dtysl[i..];
        remain_rhs = &mut dtysr[i..];
    }
    Ok(())
}

impl Unifyable for FnTy {
    fn constrain(
        &mut self,
        other: &mut Self,
        constr_map: &mut ConstrainMap,
        prv_rels: &mut Vec<PrvConstr>,
    ) -> UnifyResult<()> {
        assert!(self.generics.is_empty());
        assert!(other.generics.is_empty());

        self.exec_ty
            .constrain(&mut other.exec_ty, constr_map, prv_rels)?;

        unify_param_list(
            self.idents_typed
                .iter_mut()
                .map(|ident_typed| &mut ident_typed.dty)
                .collect(),
            other
                .idents_typed
                .iter_mut()
                .map(|ident_typed| &mut ident_typed.dty)
                .collect(),
            constr_map,
            prv_rels,
        )?;

        substitute(constr_map, &mut *self.ret_dty);
        substitute(constr_map, &mut *other.ret_dty);
        self.ret_dty
            .constrain(&mut other.ret_dty, constr_map, prv_rels)
    }

    fn substitute(&mut self, subst: &ConstrainMap) {
        let mut apply_subst = ApplySubst::new(subst);
        apply_subst.visit_fn_ty(self);
    }
}

impl Unifyable for Ty {
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

impl Unifyable for DataTy {
    fn constrain(
        &mut self,
        other: &mut Self,
        constr_map: &mut ConstrainMap,
        prv_rels: &mut Vec<PrvConstr>,
    ) -> UnifyResult<()> {
        match (&mut self.dty, &mut other.dty) {
            (DataTyKind::Ident(i1), DataTyKind::Ident(i2)) => {
                match (i1.is_implicit, i2.is_implicit) {
                    (true, _) => other.bind_to(i1, constr_map),
                    _ => self.bind_to(i2, constr_map),
                }
            }
            (DataTyKind::Ident(i), _) => other.bind_to(i, constr_map),
            (_, DataTyKind::Ident(i)) => self.bind_to(i, constr_map),
            (DataTyKind::Scalar(sty1), DataTyKind::Scalar(sty2)) => {
                if sty1 != sty2 {
                    Err(UnifyError::CannotUnify)
                } else {
                    Ok(())
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
                mem1.constrain(mem2, constr_map, prv_rels)?;
                dty1.constrain(dty2, constr_map, prv_rels)
            }
            (DataTyKind::Refine(base_tyl, refinel), DataTyKind::Refine(base_tyr, refiner)) => {
                if base_tyl != base_tyr {
                    return Err(UnifyError::CannotUnify);
                }
                constr_map.nat_constraints.push(Constraint::Implic(
                    refinel.ident.clone(),
                    *base_tyl,
                    refinel.pred,
                    Box::new(Constraint::Pred({
                        let mut subst_pred = refiner.pred.clone();
                        subst_pred.subst_ident(&refiner.ident, &refinel.ident);
                        subst_pred
                    })),
                ));
                Ok(())
            }
            (DataTyKind::Tuple(elem_dtys1), DataTyKind::Tuple(elem_dtys2)) => elem_dtys1
                .iter_mut()
                .zip(elem_dtys2)
                .try_for_each(|(dty1, dty2)| dty1.constrain(dty2, constr_map, prv_rels)),
            (DataTyKind::Array(dty1, ident1), DataTyKind::Array(dty2, ident2)) => {
                dty1.constrain(dty2, constr_map, prv_rels)?;
                if ident1 != ident2 {
                    return Err(UnifyError::CannotUnify);
                }
                Ok(())
            }
            (DataTyKind::ArrayShape(dty1, ident1), DataTyKind::ArrayShape(dty2, ident2)) => {
                dty1.constrain(dty2, constr_map, prv_rels)?;
                if ident1 != ident2 {
                    return Err(UnifyError::CannotUnify);
                }
                Ok(())
            }
            (DataTyKind::At(dty1, mem1), DataTyKind::At(dty2, mem2)) => {
                dty1.constrain(dty2, constr_map, prv_rels)?;
                mem1.constrain(mem2, constr_map, prv_rels)
            }
            (DataTyKind::Atomic(sty1), DataTyKind::Atomic(sty2)) => {
                if sty1 != sty2 {
                    Err(UnifyError::CannotUnify)
                } else {
                    Ok(())
                }
            }
            (DataTyKind::Range, DataTyKind::Range) => Ok(()),
            (_, DataTyKind::Dead(dty)) => self.constrain(dty, constr_map, prv_rels),
            (DataTyKind::RawPtr(_), DataTyKind::RawPtr(_)) => {
                unimplemented!()
            }
            (DataTyKind::Dead(_), _) => {
                panic!()
            }
            _ => Err(UnifyError::CannotUnify),
        }
    }

    fn substitute(&mut self, subst: &ConstrainMap) {
        let mut apply_subst = ApplySubst::new(subst);
        apply_subst.visit_dty(self);
    }
}

impl Unifyable for ExecTy {
    fn constrain(
        &mut self,
        other: &mut Self,
        constr_map: &mut ConstrainMap,
        prv_rels: &mut Vec<PrvConstr>,
    ) -> UnifyResult<()> {
        match (&mut self.ty, &mut other.ty) {
            (ExecTyKind::CpuThread, ExecTyKind::CpuThread)
            | (ExecTyKind::GpuThread, ExecTyKind::GpuThread)
            | (ExecTyKind::View, ExecTyKind::View) => Ok(()),
            (ExecTyKind::GpuGrid(lgdim, lbdim), ExecTyKind::GpuGrid(rgdim, rbdim))
            | (ExecTyKind::GpuBlockGrp(lgdim, lbdim), ExecTyKind::GpuBlockGrp(rgdim, rbdim)) => {
                lgdim.constrain(rgdim, constr_map, prv_rels)?;
                lbdim.constrain(rbdim, constr_map, prv_rels)
            }
            (ExecTyKind::GpuGlobalThreads(ldim), ExecTyKind::GpuGlobalThreads(rdim))
            | (ExecTyKind::GpuBlock(ldim), ExecTyKind::GpuBlock(rdim))
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

impl Unifyable for Dim {
    fn constrain(
        &mut self,
        other: &mut Self,
        constr_map: &mut ConstrainMap,
        prv_rels: &mut Vec<PrvConstr>,
    ) -> UnifyResult<()> {
        match (self, other) {
            (Dim::XYZ(ldim), Dim::XYZ(rdim)) => {
                todo!()
                // ldim.0.constrain(&mut rdim.0, constr_map, prv_rels)?;
                // ldim.1.constrain(&mut rdim.1, constr_map, prv_rels)?;
                // ldim.2.constrain(&mut rdim.2, constr_map, prv_rels)
            }
            (Dim::XY(ldim), Dim::XY(rdim))
            | (Dim::XZ(ldim), Dim::XZ(rdim))
            | (Dim::YZ(ldim), Dim::YZ(rdim)) => {
                todo!()
                // ldim.0.constrain(&mut rdim.0, constr_map, prv_rels)?;
                // ldim.1.constrain(&mut rdim.1, constr_map, prv_rels)
            }
            (Dim::X(ld), Dim::X(rd)) | (Dim::Y(ld), Dim::Y(rd)) | (Dim::Z(ld), Dim::Z(rd)) => {
                // ld.0.constrain(&mut rd.0, constr_map, prv_rels)
                todo!()
            }
            _ => Err(UnifyError::CannotUnify),
        }
    }

    fn substitute(&mut self, subst: &ConstrainMap) {
        let mut apply_subst = ApplySubst::new(subst);
        apply_subst.visit_dim(self);
    }
}

impl Unifyable for ViewTy {
    fn constrain(
        &mut self,
        other: &mut Self,
        constr_map: &mut ConstrainMap,
        prv_rels: &mut Vec<PrvConstr>,
    ) -> UnifyResult<()> {
        match (self, other) {
            (ViewTy::View(view_fn_tyl), ViewTy::View(view_fn_tyr)) => {
                view_fn_tyl.constrain(view_fn_tyr, constr_map, prv_rels)
            }
            (ViewTy::Refine(base_tyl, refinementl), ViewTy::Refine(base_tyr, refinementr)) => {
                if base_tyl != base_tyr {
                    return Err(UnifyError::CannotUnify);
                }
                let mut subst_predr = refinementr.pred.clone();
                subst_predr.subst_ident(&refinementr.ident, &refinementl.ident);
                // TODO
                // Constraint::Implic(
                //     refinementl.ident.clone(),
                //     *base_tyl,
                //     refinementl.pred.clone(),
                //     Constraint::Pred(subst_predr),
                // )
                Ok(())
            }
            _ => Err(UnifyError::CannotUnify),
        }
    }

    fn substitute(&mut self, subst: &ConstrainMap) {
        todo!()
    }
}

impl Unifyable for ViewFunTy {
    fn constrain(
        &mut self,
        other: &mut Self,
        constr_map: &mut ConstrainMap,
        prv_rels: &mut Vec<PrvConstr>,
    ) -> UnifyResult<()> {
        assert!(self.gen_params.is_empty());
        assert!(other.gen_params.is_empty());

        unify_param_list(
            other
                .params
                .iter_mut()
                .map(|(_, view_ty)| view_ty)
                .collect(),
            self.params.iter_mut().map(|(_, view_ty)| view_ty).collect(),
            constr_map,
            prv_rels,
        )?;

        substitute(constr_map, &mut *self.in_view_elem_dty);
        substitute(constr_map, &mut *other.in_view_elem_dty);
        other
            .in_view_elem_dty
            .constrain(&mut self.in_view_elem_dty, constr_map, prv_rels)?;

        // TODO constraints!

        substitute(constr_map, &mut *self.ret_dty);
        substitute(constr_map, &mut *other.ret_dty);
        self.ret_dty
            .constrain(&mut other.ret_dty, constr_map, prv_rels)
    }

    fn substitute(&mut self, subst: &ConstrainMap) {
        todo!()
    }
}
// impl Nat {
//     fn bind_to(
//         &self,
//         ident: &Ident,
//         constr_map: &mut ConstrainMap,
//         _: &mut Vec<PrvConstr>,
//     ) -> UnifyResult<()> {
//         // No occurs check.
//         // Nats can be equal to an expression in which the nat appears again. E.g., a = a * 1
//         if let Some(old) = constr_map
//             .nat_unifier
//             .insert(ident.name.clone(), self.clone())
//         {
//             if &old != self {
//                 println!(
//                     "WARNING: Not able to check equality of Nats `{}` and `{}`",
//                     old, self
//                 )
//             }
//         }
//         constr_map
//             .nat_unifier
//             .values_mut()
//             .for_each(|n| SubstIdent::new(ident, self).visit_nat(n));
//         Ok(())
//     }
//
//     fn unify(n1: &Nat, n2: &Nat, _constr_map: &mut ConstrainMap) -> UnifyResult<()> {
//         if n1 == n2 {
//             Ok(())
//         } else {
//             println!(
//                 "WARNING: Not able to check equality of Nats `{}` and `{}`",
//                 n1, n2
//             );
//             Ok(())
//         }
//     }
// }
//
// impl Constrainable for Nat {
//     fn constrain(
//         &mut self,
//         other: &mut Self,
//         constr_map: &mut ConstrainMap,
//         prv_rels: &mut Vec<PrvConstr>,
//     ) -> UnifyResult<()> {
//         match (&mut *self, &mut *other) {
//             (Nat::Ident(n1i), Nat::Ident(n2i)) if n1i.is_implicit || n2i.is_implicit => {
//                 match (n1i.is_implicit, n2i.is_implicit) {
//                     (true, _) => other.bind_to(n1i, constr_map, prv_rels),
//                     (false, _) => self.bind_to(n2i, constr_map, prv_rels),
//                 }
//             }
//             (Nat::Ident(n1i), _) if n1i.is_implicit => other.bind_to(n1i, constr_map, prv_rels),
//             (_, Nat::Ident(n2i)) if n2i.is_implicit => self.bind_to(n2i, constr_map, prv_rels),
//             (Nat::BinOp(op1, n1l, n1r), Nat::BinOp(op2, n2l, n2r)) if op1 == op2 => {
//                 n1l.constrain(n2l, constr_map, prv_rels)?;
//                 n1r.constrain(n2r, constr_map, prv_rels)
//             }
//             (Nat::App(f1, ns1), Nat::App(f2, ns2)) if f1 == f2 => {
//                 for (n1, n2) in ns1.iter_mut().zip(ns2.iter_mut()) {
//                     n1.constrain(n2, constr_map, prv_rels)?;
//                 }
//                 Ok(())
//             }
//             _ => Self::unify(self, other, constr_map),
//         }
//     }
//
//     fn substitute(&mut self, subst: &ConstrainMap) {
//         let mut apply_subst = ApplySubst::new(subst);
//         apply_subst.visit_nat(self);
//     }
// }

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

impl Unifyable for Memory {
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

impl Unifyable for Provenance {
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
            (Provenance::Ident(i), _) | (_, Provenance::Ident(i)) => {
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

pub(super) fn substitute<C: Unifyable>(subst: &ConstrainMap, c: &mut C) {
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
    // fn visit_nat(&mut self, nat: &mut Nat) {
    //     match nat {
    //         Nat::Ident(ident) if self.subst.nat_unifier.contains_key(&ident.name) => {
    //             *nat = self.subst.nat_unifier.get(&ident.name).unwrap().clone();
    //         }
    //         _ => visit_mut::walk_nat(self, nat),
    //     }
    // }

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

struct SubstIdent<'a, S: Unifyable> {
    ident: &'a Ident,
    term: &'a S,
}

impl<'a, S: Unifyable> SubstIdent<'a, S> {
    fn new(ident: &'a Ident, term: &'a S) -> Self {
        SubstIdent { ident, term }
    }
}

// impl<'a> VisitMut for SubstIdent<'a, Nat> {
//     fn visit_nat(&mut self, nat: &mut Nat) {
//         match nat {
//             Nat::Ident(ident) if ident.name == self.ident.name => *nat = self.term.clone(),
//             _ => visit_mut::walk_nat(self, nat),
//         }
//     }
// }

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

#[cfg(test)]
mod tests {
    use super::*;

    fn shrd_ref_ty() -> DataTy {
        DataTy::new(DataTyKind::Ref(Box::new(RefDty::new(
            Provenance::Value("r".to_string()),
            Ownership::Shrd,
            Memory::GpuGlobal,
            DataTy::new(DataTyKind::Array(
                Box::new(DataTy::new(DataTyKind::Scalar(ScalarTy::I32))),
                Box::new(Predicate::Num(5)),
            )),
        ))))
    }

    #[test]
    fn scalar() -> UnifyResult<()> {
        let mut i32 = DataTy::new(DataTyKind::Scalar(ScalarTy::I32));
        let mut t = DataTy::new(DataTyKind::Ident(Ident::new("t")));
        let (subst, _) = constrain(&mut i32, &mut t)?;
        substitute(&subst, &mut i32);
        substitute(&subst, &mut t);
        assert_eq!(i32, t);
        Ok(())
    }

    #[test]
    fn shrd_reft() -> UnifyResult<()> {
        let mut t = DataTy::new(DataTyKind::Ident(Ident::new("t")));
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
            DataTy::new(DataTyKind::Ident(Ident::new("t"))),
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
            DataTy::new(DataTyKind::Ident(Ident::new("t"))),
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
