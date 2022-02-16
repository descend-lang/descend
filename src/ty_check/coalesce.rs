use super::constrain::ConstrainMap;
use super::error::TyError;
use super::TyResult;
use crate::ast::{DataTy, Nat, Provenance, ThreadHierchyTy, Ty, TyKind};
use crate::ty_check::ctxs::TyCtx;

#[derive(Clone, Copy, Debug)]
enum Bound {
    LeastUpper,
    GreatestLower,
}

impl std::ops::Not for Bound {
    type Output = Self;

    fn not(self) -> Self::Output {
        match self {
            Bound::LeastUpper => Bound::GreatestLower,
            Bound::GreatestLower => Bound::LeastUpper,
        }
    }
}

pub(super) fn coalesce_ty(
    constr_map: &mut ConstrainMap,
    ty_ctx: &mut TyCtx,
    ty: &Ty,
) -> TyResult<Ty> {
    fn go(
        constr_map: &mut ConstrainMap,
        ty_ctx: &mut TyCtx,
        ty: &Ty,
        bound: Bound,
    ) -> TyResult<Ty> {
        let tty = match &ty.ty {
            TyKind::Ident(ident) => {
                let bounds = match bound {
                    Bound::GreatestLower => &mut constr_map.ty_lower_bound,
                    Bound::LeastUpper => &mut constr_map.ty_upper_bound,
                };
                if let Some(bs) = bounds.get(&ident.name) {
                    let bounds_clone = bs.clone();
                    let mut coalesced_bounds = bounds_clone
                        .iter()
                        .map(|ty| go(constr_map, ty_ctx, ty, bound))
                        .collect::<TyResult<Vec<_>>>()?;
                    let init_ty = Ty::new(TyKind::Ident(ident.clone()));
                    coalesced_bounds
                        .iter()
                        .try_fold(init_ty, |acc, ty| acc.bound_with(ty_ctx, ty, bound))?
                } else {
                    panic!("Identifier not in constrain map: `{}`", ident.name)
                }
            }
            TyKind::TupleView(elem_tys) => Ty::new(TyKind::TupleView(
                elem_tys
                    .iter()
                    .map(|ty| go(constr_map, ty_ctx, ty, bound))
                    .collect::<TyResult<Vec<_>>>()?,
            )),
            TyKind::Fn(id_kinded, param_tys, exec, ret_ty) => Ty::new(TyKind::Fn(
                id_kinded.clone(),
                param_tys
                    .iter()
                    .map(|ty| go(constr_map, ty_ctx, ty, !bound))
                    .collect::<TyResult<Vec<_>>>()?,
                *exec,
                Box::new(go(constr_map, ty_ctx, ret_ty, bound)?),
            )),
            // TODO do we have to pass polarity here?
            TyKind::Data(dty) => Ty::new(TyKind::Data(coalesce_dty(constr_map, ty_ctx, dty)?)),
            TyKind::Dead(_) => {
                unimplemented!()
            }
        };
        Ok(tty)
    }
    go(constr_map, ty_ctx, ty, Bound::LeastUpper)
}

fn coalesce_dty(
    constr_map: &mut ConstrainMap,
    ty_ctx: &mut TyCtx,
    dty: &DataTy,
) -> TyResult<DataTy> {
    fn go(
        constr_map: &mut ConstrainMap,
        ty_ctx: &mut TyCtx,
        dty: &DataTy,
        bound: Bound,
    ) -> TyResult<DataTy> {
        let dtty = match dty {
            DataTy::Ident(ident) => {
                let bounds = match bound {
                    Bound::GreatestLower => &mut constr_map.dty_lower_bound,
                    Bound::LeastUpper => &mut constr_map.dty_upper_bound,
                };
                if let Some(bs) = bounds.get(&ident.name) {
                    let bounds_clone = bs.clone();
                    let mut coalesced_bounds = bounds_clone
                        .iter()
                        .map(|dty| go(constr_map, ty_ctx, dty, bound))
                        .collect::<TyResult<Vec<_>>>()?;
                    let init_dty = DataTy::Ident(ident.clone());
                    coalesced_bounds
                        .iter()
                        .try_fold(init_dty, |acc, dty| acc.bound_for_dty(ty_ctx, dty, bound))?
                } else {
                    panic!("Identifier not in constrain map: `{}`", ident.name)
                }
            }
            DataTy::Scalar(sty) => DataTy::Scalar(sty.clone()),
            DataTy::Atomic(sty) => DataTy::Atomic(sty.clone()),
            DataTy::ThreadHierchy(th_hierchy) => {
                DataTy::ThreadHierchy(Box::new(match th_hierchy.as_ref() {
                    ThreadHierchyTy::BlockGrp(n1, n2, n3, m1, m2, m3) => ThreadHierchyTy::BlockGrp(
                        coalesce_nat(constr_map, n1),
                        coalesce_nat(constr_map, n2),
                        coalesce_nat(constr_map, n3),
                        coalesce_nat(constr_map, m1),
                        coalesce_nat(constr_map, m2),
                        coalesce_nat(constr_map, m3),
                    ),
                    ThreadHierchyTy::ThreadGrp(n1, n2, n3) => ThreadHierchyTy::ThreadGrp(
                        coalesce_nat(constr_map, n1),
                        coalesce_nat(constr_map, n2),
                        coalesce_nat(constr_map, n3),
                    ),
                    ThreadHierchyTy::WarpGrp(n) => {
                        ThreadHierchyTy::WarpGrp(coalesce_nat(constr_map, n))
                    }
                    ThreadHierchyTy::Warp => ThreadHierchyTy::Warp,
                }))
            }
            DataTy::Tuple(elem_dtys) => DataTy::Tuple(
                elem_dtys
                    .iter()
                    .map(|dty| coalesce_dty(constr_map, ty_ctx, dty))
                    .collect::<TyResult<Vec<_>>>()?,
            ),
            DataTy::Array(dty, n) => {
                DataTy::Array(Box::new(coalesce_dty(constr_map, ty_ctx, dty)?), n.clone())
            }
            DataTy::ArrayShape(dty, n) => {
                DataTy::ArrayShape(Box::new(coalesce_dty(constr_map, ty_ctx, dty)?), n.clone())
            }
            DataTy::At(dty, mem) => DataTy::At(
                Box::new(coalesce_dty(constr_map, ty_ctx, dty)?),
                mem.clone(),
            ),
            DataTy::Ref(prv, own, mem, dty) => DataTy::Ref(
                coalesce_prv(constr_map, ty_ctx, prv)?,
                *own,
                mem.clone(),
                Box::new(coalesce_dty(constr_map, ty_ctx, dty)?),
            ),
            DataTy::RawPtr(dty) => DataTy::RawPtr(Box::new(coalesce_dty(constr_map, ty_ctx, dty)?)),
            DataTy::Range => DataTy::Range,
            DataTy::Dead(dty) => DataTy::Dead(Box::new(coalesce_dty(constr_map, ty_ctx, dty)?)),
        };
        Ok(dtty)
    }
    go(constr_map, ty_ctx, dty, Bound::LeastUpper)
}

fn coalesce_nat(constr_map: &mut ConstrainMap, n: &Nat) -> Nat {
    unimplemented!()
}

impl Ty {
    fn bound_with(&self, ty_ctx: &mut TyCtx, ty: &Ty, bound: Bound) -> TyResult<Ty> {
        let ty = match (&self.ty, &ty.ty) {
            (TyKind::Ident(i1), TyKind::Ident(i2)) if i1 == i2 => TyKind::Ident(i1.clone()),
            (TyKind::TupleView(ty_es1), TyKind::TupleView(ty_es2)) => TyKind::TupleView(
                ty_es1
                    .iter()
                    .zip(ty_es2)
                    .map(|(t1, t2)| t1.bound_with(ty_ctx, t2, bound))
                    .collect::<TyResult<Vec<_>>>()?,
            ),
            (
                TyKind::Fn(id_k1, p_tys1, exec1, ret_ty1),
                TyKind::Fn(id_k2, p_tys2, exec2, ret_ty2),
            ) => {
                unimplemented!()
            }
            (TyKind::Data(dty1), TyKind::Data(dty2)) => {
                TyKind::Data(dty1.bound_for_dty(ty_ctx, dty2, bound)?)
            }
            (TyKind::Dead(_), TyKind::Dead(_)) => {
                unimplemented!()
            }
            _ => return Err(TyError::CannotUnify),
        };
        Ok(Ty::new(ty))
    }
}

impl DataTy {
    fn bound_for_dty(&self, ty_ctx: &mut TyCtx, dty: &DataTy, bound: Bound) -> TyResult<DataTy> {
        let dty = match (self, dty) {
            (DataTy::Ident(i1), DataTy::Ident(i2)) if i1 == i2 => DataTy::Ident(i1.clone()),
            (DataTy::Ident(i1), DataTy::Ident(i2)) if i1 != i2 => return Err(TyError::CannotUnify),
            (DataTy::Ident(_), _) => dty.clone(),
            (_, DataTy::Ident(_)) => self.clone(),
            (DataTy::Tuple(dty_es1), DataTy::Tuple(dty_es2)) => DataTy::Tuple(
                dty_es1
                    .iter()
                    .zip(dty_es2)
                    .map(|(d1, d2)| d1.bound_for_dty(ty_ctx, d2, bound))
                    .collect::<TyResult<Vec<_>>>()?,
            ),
            (DataTy::At(dty1, mem1), DataTy::At(dty2, mem2)) if mem1 == mem2 => DataTy::At(
                Box::new(dty1.bound_for_dty(ty_ctx, dty2, bound)?),
                mem1.clone(),
            ),
            (DataTy::Array(dty1, n1), DataTy::Array(dty2, n2)) if n1 == n2 => DataTy::Array(
                Box::new(dty1.bound_for_dty(ty_ctx, dty2, bound)?),
                n1.clone(),
            ),
            (DataTy::ArrayShape(dty1, n1), DataTy::ArrayShape(dty2, n2)) if n1 == n2 => {
                DataTy::ArrayShape(
                    Box::new(dty1.bound_for_dty(ty_ctx, dty2, bound)?),
                    n1.clone(),
                )
            }
            (DataTy::Scalar(sty1), DataTy::Scalar(sty2)) if sty1 == sty2 => {
                DataTy::Scalar(sty1.clone())
            }
            (DataTy::Ref(prv1, own1, mem1, dty1), DataTy::Ref(prv2, own2, mem2, dty2))
                if own1 == own2 && mem1 == mem2 =>
            {
                DataTy::Ref(
                    prv1.bound_for_prv(ty_ctx, prv2, bound)?,
                    *own1,
                    mem1.clone(),
                    Box::new(dty1.bound_for_dty(ty_ctx, dty2, bound)?),
                )
            }
            (DataTy::RawPtr(dty1), DataTy::RawPtr(dty2)) => {
                DataTy::RawPtr(Box::new(dty1.bound_for_dty(ty_ctx, dty2, bound)?))
            }
            (DataTy::Atomic(sty1), DataTy::Atomic(sty2)) if sty1 == sty2 => DataTy::Atomic(*sty1),
            (DataTy::ThreadHierchy(th_h1), DataTy::ThreadHierchy(th_h2)) if th_h1 == th_h2 => {
                DataTy::ThreadHierchy(th_h1.clone())
            }
            (DataTy::Range, DataTy::Range) => DataTy::Range,
            (DataTy::Dead(_), DataTy::Dead(_)) => {
                unimplemented!()
            }
            _ => return Err(TyError::CannotUnify),
        };
        Ok(dty)
    }
}

fn coalesce_prv(
    constr_map: &mut ConstrainMap,
    ty_ctx: &mut TyCtx,
    prv: &Provenance,
) -> TyResult<Provenance> {
    fn go(
        constr_map: &mut ConstrainMap,
        ty_ctx: &mut TyCtx,
        prv: &Provenance,
        bound: Bound,
    ) -> TyResult<Provenance> {
        let pprv = match prv {
            Provenance::Ident(ident) => {
                let bounds = match bound {
                    Bound::GreatestLower => &mut constr_map.prv_lower_bound,
                    Bound::LeastUpper => &mut constr_map.prv_upper_bound,
                };
                if let Some(bs) = bounds.get(&ident.name) {
                    let bounds_clone = bs.clone();
                    let mut coalesced_bounds = bounds_clone
                        .iter()
                        .map(|prv| go(constr_map, ty_ctx, prv, bound))
                        .collect::<TyResult<Vec<_>>>()?;
                    let init_prv = Provenance::Ident(ident.clone());
                    coalesced_bounds
                        .iter()
                        .try_fold(init_prv, |acc, prv| acc.bound_for_prv(ty_ctx, prv, bound))?
                } else {
                    panic!("Identifier not in constrain map: `{}`", ident.name)
                }
            }
            Provenance::Value(v) => Provenance::Value(v.clone()),
        };
        Ok(pprv)
    }
    go(constr_map, ty_ctx, prv, Bound::LeastUpper)
}

impl Provenance {
    fn bound_for_prv(
        &self,
        ty_ctx: &mut TyCtx,
        prv: &Provenance,
        bound: Bound,
    ) -> TyResult<Provenance> {
        match (self, prv) {
            (Provenance::Ident(i1), Provenance::Ident(i2)) => {
                // TODO check in Delta that i1 <: i2, then return i2 as bound?!
                // use outlives
                unimplemented!()
            }
            (Provenance::Ident(id), Provenance::Value(v)) => unimplemented!(), // TODO check outlives
            (Provenance::Value(v), Provenance::Ident(id)) => unimplemented!(), // TODO check outlives
            (Provenance::Value(v1), Provenance::Value(v2)) => {
                let l1 = ty_ctx.loans_in_prv(v1)?;
                let l2 = ty_ctx.loans_in_prv(v2)?;
                let bounds = match bound {
                    Bound::GreatestLower => unimplemented!(), //l1.union(l2).collect(),
                    Bound::LeastUpper => unimplemented!(),    //l1.intersection(l2).collect(),
                };
            }
        }
    }
}
