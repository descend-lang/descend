use super::constrain::ConstrainMap;
use super::error::TyError;
use super::TyResult;
use crate::ast::{DataTy, Nat, Provenance, ThreadHierchyTy, Ty, TyKind};

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

fn coalesce_ty(constr_map: &mut ConstrainMap, ty: &Ty) -> TyResult<Ty> {
    fn go(constr_map: &mut ConstrainMap, ty: &Ty, bound: Bound) -> TyResult<Ty> {
        let tty = match &ty.ty {
            TyKind::Ident(ident) => {
                let bounds = match bound {
                    Bound::GreatestLower => &mut constr_map.ty_lower_bound,
                    Bound::LeastUpper => &mut constr_map.ty_upper_bound,
                };
                if let Some(bs) = bounds.get(&ident.name) {
                    let bounds_clone = bs.clone();
                    let mut coalesced_bounds =
                        bounds_clone.iter().map(|ty| go(constr_map, ty, bound));
                    let init_ty = Ty::new(TyKind::Ident(ident.clone()));
                    coalesced_bounds.try_fold(init_ty, |acc, ty| acc.bound_with(&(ty?), bound))?
                } else {
                    panic!("Identifier not in constrain map: `{}`", ident.name)
                }
            }
            TyKind::TupleView(elem_tys) => Ty::new(TyKind::TupleView(
                elem_tys
                    .iter()
                    .map(|ty| go(constr_map, ty, bound))
                    .collect::<TyResult<Vec<_>>>()?,
            )),
            TyKind::ThreadHierchy(th_hierchy) => {
                Ty::new(TyKind::ThreadHierchy(Box::new(match th_hierchy.as_ref() {
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
                })))
            }
            TyKind::Fn(id_kinded, param_tys, exec, ret_ty) => Ty::new(TyKind::Fn(
                id_kinded.clone(),
                param_tys
                    .iter()
                    .map(|ty| go(constr_map, ty, !bound))
                    .collect::<TyResult<Vec<_>>>()?,
                *exec,
                Box::new(go(constr_map, ret_ty, bound)?),
            )),
            // TODO do we have to pass polarity here?
            TyKind::Data(dty) => Ty::new(TyKind::Data(coalesce_dty(constr_map, dty))),
            TyKind::Dead(_) => {
                unimplemented!()
            }
        };
        Ok(tty)
    }
    go(constr_map, ty, Bound::LeastUpper)
}

fn coalesce_dty(constr_map: &mut ConstrainMap, dty: &DataTy) -> DataTy {
    fn go(constr_map: &mut ConstrainMap, dty: &DataTy, polar: bool) -> DataTy {
        //let dty = match dty {};
        unimplemented!()
    }
    unimplemented!()
}

fn coalesce_nat(constr_map: &mut ConstrainMap, n: &Nat) -> Nat {
    unimplemented!()
}

impl Ty {
    fn bound_with(&self, ty: &Ty, bound: Bound) -> TyResult<Ty> {
        let ty = match (&self.ty, &ty.ty) {
            (TyKind::Ident(i1), TyKind::Ident(i2)) if i1 == i2 => TyKind::Ident(i1.clone()),
            (TyKind::TupleView(ty_es1), TyKind::TupleView(ty_es2)) => TyKind::TupleView(
                ty_es1
                    .iter()
                    .zip(ty_es2)
                    .map(|(t1, t2)| t1.bound_with(t2, bound))
                    .collect::<TyResult<Vec<_>>>()?,
            ),
            (TyKind::ThreadHierchy(th_h1), TyKind::ThreadHierchy(th_h2)) if th_h1 == th_h2 => {
                TyKind::ThreadHierchy(th_h1.clone())
            }
            (
                TyKind::Fn(id_k1, p_tys1, exec1, ret_ty1),
                TyKind::Fn(id_k2, p_tys2, exec2, ret_ty2),
            ) => {
                unimplemented!()
            }
            (TyKind::Data(dty1), TyKind::Data(dty2)) => {
                TyKind::Data(dty1.bound_for_tys(dty2, bound)?)
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
    fn bound_for_tys(&self, dty: &DataTy, bound: Bound) -> TyResult<DataTy> {
        let dty = match (self, dty) {
            (DataTy::Ident(i1), DataTy::Ident(i2)) if i1 == i2 => DataTy::Ident(i1.clone()),
            (DataTy::Tuple(dty_es1), DataTy::Tuple(dty_es2)) => DataTy::Tuple(
                dty_es1
                    .iter()
                    .zip(dty_es2)
                    .map(|(d1, d2)| d1.bound_for_tys(d2, bound))
                    .collect::<TyResult<Vec<_>>>()?,
            ),
            (DataTy::At(dty1, mem1), DataTy::At(dty2, mem2)) if mem1 == mem2 => {
                DataTy::At(Box::new(dty1.bound_for_tys(dty2, bound)?), mem1.clone())
            }
            (DataTy::Array(dty1, n1), DataTy::Array(dty2, n2)) if n1 == n2 => {
                DataTy::Array(Box::new(dty1.bound_for_tys(dty2, bound)?), n1.clone())
            }
            (DataTy::ArrayShape(dty1, n1), DataTy::ArrayShape(dty2, n2)) if n1 == n2 => {
                DataTy::ArrayShape(Box::new(dty1.bound_for_tys(dty2, bound)?), n1.clone())
            }
            (DataTy::Scalar(sty1), DataTy::Scalar(sty2)) if sty1 == sty2 => {
                DataTy::Scalar(sty1.clone())
            }
            (DataTy::Ref(prv1, own1, mem1, dty1), DataTy::Ref(prv2, own2, mem2, dty2))
                if own1 == own2 && mem1 == mem2 =>
            {
                DataTy::Ref(
                    prv1.bound_for_prvs(prv2, bound)?,
                    own1.clone(),
                    mem1.clone(),
                    Box::new(dty1.bound_for_tys(dty2, bound)?),
                )
            }
            (DataTy::RawPtr(dty1), DataTy::RawPtr(dty2)) => {
                DataTy::RawPtr(Box::new(dty1.bound_for_tys(dty2, bound)?))
            }
            (DataTy::Atomic(sty1), DataTy::Atomic(sty2)) if sty1 == sty2 => {
                DataTy::Atomic(sty1.clone())
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

impl Provenance {
    fn bound_for_prvs(&self, prv: &Provenance, bound: Bound) -> TyResult<Provenance> {
        match (self, prv) {
            (Provenance::Ident(i1), Provenance::Ident(i2)) => {
                unimplemented!()
            }
            (Provenance::Ident(id), Provenance::Value(v)) => unimplemented!(),
            (Provenance::Value(v), Provenance::Ident(id)) => unimplemented!(),
            (Provenance::Value(v1), Provenance::Value(v2)) => unimplemented!(),
        }
    }
}
