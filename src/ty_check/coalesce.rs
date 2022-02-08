fn coalesce_ty(subst: &mut Substitution, ty: &Ty) -> Ty {
    fn go(subst: &mut Substitution, ty: &Ty, polar: bool) -> Ty {
        let ty_kind = match &ty.ty {
            TyKind::Ident(ident) => {
                let bounds = if polar {
                    &mut subst.ty_lower_bound
                } else {
                    &mut subst.ty_upper_bound
                };
                if let Some(bs) = bounds.get_mut(&ident.name) {
                    let coalesced_bounds = bs.iter().map(|ty| go(subst, ty, polar)).collect();
                    let op = if polar { Ty::union } else { Ty::inter };
                    let init_ty = Ty::new(TyKind::Ident(ident.clone()));
                    coalesced_bounds.fold(init_ty, op)
                }
            }
            TyKind::TupleView(elem_tys) => {
                TyKind::TupleView(elem_tys.iter().map(|ty| go(subst, ty, polar)).collect())
            }
            TyKind::ThreadHierchy(th_hierchy) => match th_hierchy.as_ref() {
                ThreadHierchyTy::BlockGrp(n1, n2, n3, m1, m2, m3) => ThreadHierchyTy::BlockGrp(
                    subst.coalesce_nat(n1),
                    subst.coalesce_nat(n2),
                    subst.coalesce_nat(n3),
                    subst.coalesce_nat(m1),
                    subst.coalesce_nat(m2),
                    subst.coalesce_nat(m3),
                ),
                ThreadHierchyTy::ThreadGrp(n1, n2, n3) => ThreadHierchyTy::ThreadGrp(
                    subst.coalesce_nat(n1),
                    subst.coalesce_nat(n2),
                    subst.coalesce_nat(n3),
                ),
                ThreadHierchyTy::WarpGrp(n) => ThreadHierchyTy::WarpGrp(subst.coalesce_nat(n)),
                ThreadHierchyTy::Warp => ThreadHierchyTy::Warp,
            },
            TyKind::Fn(id_kinded, param_tys, exec, ret_ty) => TyKind::Fn(
                id_kinded.clone(),
                param_tys.iter().map(|ty| go(subst, ty, !polar)).collect(),
                *exec,
                Box::new(go(subst, ret_ty, polar)),
            ),
            // TODO do we have to pass polarity here?
            TyKind::Data(dty) => TyKind::Data(subst.coalesce_dty(dty)),
            TyKind::Dead(_) => {
                unimplemented!()
            }
        };
        Ty::new(ty_kind)
    }
    subst.ty_upper_bound.keys().go(ty, true)
}

fn coalesce_dty(subst: &mut Substitution, dty: &DataTy) -> DataTy {
    fn go(subst: &mut Substitution, dty: &DataTy, polar: bool) -> DataTy {
        //let dty = match dty {};
        unimplemented!()
    }
    unimplemented!()
}

fn coalesce_nat(subst: &mut Substitution, n: &Nat) -> Nat {
    unimplemented!()
}

impl Ty {
    fn union(&self, ty: &Ty) -> TyResult<Ty> {
        let ty = match (&self.ty, &ty.ty) {
            (TyKind::Ident(i1), TyKind::Ident(i2)) if i1 == i2 => TyKind::Ident(i1.clone()),
            (TyKind::TupleView(ty_es1), TyKind::TupleView(ty_es2)) => TyKind::TupleView(
                ty_es1
                    .iter()
                    .zip(ty_es2)
                    .map(|(t1, t2)| t1.union(t2))
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
            (TyKind::Data(dty1), TyKind::Data(dty2)) => TyKind::Data(dty1.union(dty2)?),
            (TyKind::Dead(_), TyKind::Dead(_)) => {
                unimplemented!()
            }
            _ => return Err(TyError::CannotUnify),
        };
        Ok(Ty::new(ty))
    }
}

impl DataTy {
    fn union(&self, dty: &DataTy) -> TyResult<DataTy> {
        let dty = match (self, dty) {
            (DataTy::Ident(i1), DataTy::Ident(i2)) if i1 == i2 => DataTy::Ident(i1.clone()),
            (DataTy::Tuple(dty_es1), DataTy::Tuple(dty_es2)) => DataTy::Tuple(
                dty_es1
                    .iter()
                    .zip(dty_es2)
                    .map(|(d1, d2)| d1.union(d2))
                    .collect::<TyResult<Vec<_>>>()?,
            ),
            (DataTy::At(dty1, mem1), DataTy::At(dty2, mem2)) if mem1 == mem2 => {
                DataTy::At(Box::new(dty1.union(dty2)?), mem1.clone())
            }
            (DataTy::Array(dty1, n1), DataTy::Array(dty2, n2)) if n1 == n2 => {
                DataTy::Array(Box::new(dty1.union(dty2)?), n1.clone())
            }
            (DataTy::ArrayShape(dty1, n1), DataTy::ArrayShape(dty2, n2)) if n1 == n2 => {
                DataTy::ArrayShape(Box::new(dty1.union(dty2)?), n1.clone())
            }
            (DataTy::Scalar(sty1), DataTy::Scalar(sty2)) if sty1 == sty2 => {
                DataTy::Scalar(sty1.clone())
            }
            (DataTy::Ref(prv1, own1, mem1, dty1), DataTy::Ref(prv2, own2, mem2, dty2))
                if own1 == own2 && mem1 == mem2 =>
            {
                DataTy::Ref(
                    prv1.union(prv2)?,
                    own1.clone(),
                    mem1.clone(),
                    Box::new(dty1.union(dty2)?),
                )
            }
            (DataTy::RawPtr(dty1), DataTy::RawPtr(dty2)) => {
                DataTy::RawPtr(Box::new(dty1.union(dty2)?))
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
    fn union(&self, prv: &Provenance) -> TyResult<Provenance> {
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
