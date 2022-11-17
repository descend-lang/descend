use crate::ast::utils::{fresh_ident, FreeKindedIdents};
use crate::ast::visit::Visit;
use crate::ast::visit_mut::VisitMut;
use crate::ast::*;
use crate::ty_check::ctxs::{KindCtx, TyCtx};
use crate::ty_check::error::TyError;
use crate::ty_check::subty::multiple_outlives;
use crate::ty_check::{TyChecker, TyResult};
use std::collections::{HashMap, HashSet};

pub(super) fn unify<C: Constrainable>(t1: &mut C, t2: &mut C) -> TyResult<()> {
    let (subst, _) = constrain(t1, t2)?;
    substitute(&subst, t1);
    substitute(&subst, t2);
    Ok(())
}

pub(super) fn sub_unify<C: Constrainable>(
    kind_ctx: &KindCtx,
    ty_ctx: TyCtx,
    sub: &mut C,
    sup: &mut C,
) -> TyResult<TyCtx> {
    let (subst, prv_rels) = constrain(sub, sup)?;
    substitute(&subst, sub);
    substitute(&subst, sup);
    let outlives_ctx = multiple_outlives(
        kind_ctx,
        ty_ctx,
        prv_rels.iter().map(|PrvConstr(p1, p2)| (p1, p2)),
    )?;
    Ok(outlives_ctx)
}

fn constrain<S: Constrainable>(t1: &mut S, t2: &mut S) -> TyResult<(ConstrainMap, Vec<PrvConstr>)> {
    let mut constr_map = ConstrainMap::new();
    let mut prv_rels = Vec::new();
    t1.constrain(t2, &mut constr_map, &mut prv_rels)?;
    Ok((constr_map, prv_rels))
}

pub(super) fn inst_fn_ty_scheme(
    idents_kinded: &[IdentKinded],
    param_tys: &[Ty],
    exec_ty: &ExecTy,
    ret_ty: &Ty,
) -> TyResult<Ty> {
    let mono_idents: Vec<_> = idents_kinded
        .iter()
        .map(|i| match i.kind {
            Kind::DataTy => {
                ArgKinded::DataTy(DataTy::new(fresh_ident(&i.ident.name, DataTyKind::Ident)))
            }
            Kind::Nat => ArgKinded::Nat(fresh_ident(&i.ident.name, Nat::Ident)),
            Kind::Memory => ArgKinded::Memory(fresh_ident(&i.ident.name, Memory::Ident)),
            Kind::Provenance => {
                ArgKinded::Provenance(fresh_ident(&i.ident.name, Provenance::Ident))
            }
        })
        .collect();

    let mono_param_tys = param_tys
        .iter()
        .map(|ty| TyChecker::subst_ident_kinded(idents_kinded, mono_idents.as_slice(), ty))
        .collect();
    let mono_ret_ty = TyChecker::subst_ident_kinded(idents_kinded, mono_idents.as_slice(), ret_ty);

    Ok(Ty::new(TyKind::FnTy(Box::new(FnTy::new(
        vec![],
        mono_param_tys,
        exec_ty.clone(),
        mono_ret_ty,
    )))))
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub(super) struct PrvConstr(pub Provenance, pub Provenance);

#[derive(Debug)]
pub(super) struct ConstrainMap {
    // TODO swap Box<str> for something more abstract, like Symbol or Identifier
    pub dty_unifier: HashMap<Box<str>, DataTy>,
    pub nat_unifier: HashMap<Box<str>, Nat>,
    pub mem_unifier: HashMap<Box<str>, Memory>,
}

impl ConstrainMap {
    fn new() -> Self {
        ConstrainMap {
            dty_unifier: HashMap::new(),
            nat_unifier: HashMap::new(),
            mem_unifier: HashMap::new(),
        }
    }
}

impl DataTy {
    fn bind_to(&self, ident: &Ident, constr_map: &mut ConstrainMap) -> TyResult<()> {
        if let DataTyKind::Ident(ty_id) = &self.dty {
            if ty_id == ident {
                return Ok(());
            }
        }
        if Self::occurs_check(&IdentKinded::new(ident, Kind::DataTy), self) {
            return Err(TyError::InfiniteType);
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

pub(super) trait Constrainable {
    fn constrain(
        &mut self,
        other: &mut Self,
        constr_map: &mut ConstrainMap,
        prv_rels: &mut Vec<PrvConstr>,
    ) -> TyResult<()>;
    fn free_idents(&self) -> HashSet<IdentKinded>;
    fn substitute(&mut self, subst: &ConstrainMap);

    fn occurs_check<S: Constrainable>(ident_kinded: &IdentKinded, s: &S) -> bool {
        s.free_idents().contains(ident_kinded)
    }
}

impl Constrainable for Ty {
    fn constrain(
        &mut self,
        other: &mut Self,
        constr_map: &mut ConstrainMap,
        prv_rels: &mut Vec<PrvConstr>,
    ) -> TyResult<()> {
        match (&mut self.ty, &mut other.ty) {
            (TyKind::FnTy(fn_ty1), TyKind::FnTy(fn_ty2)) => {
                assert!(fn_ty1.generics.is_empty());
                assert!(fn_ty2.generics.is_empty());

                fn_ty1
                    .exec_ty
                    .constrain(&mut fn_ty2.exec_ty, constr_map, prv_rels)?;

                if fn_ty1.param_tys.len() != fn_ty2.param_tys.len() {
                    return Err(TyError::CannotUnify);
                }
                // substitute result of unification for every following unification
                let mut i = 0;
                let mut remain_lhs = &mut fn_ty1.param_tys[i..];
                let mut remain_rhs = &mut fn_ty2.param_tys[i..];
                while let (Some((next_lhs, tail_lhs)), Some((next_rhs, tail_rhs))) =
                    (remain_lhs.split_first_mut(), remain_rhs.split_first_mut())
                {
                    next_lhs.constrain(next_rhs, constr_map, prv_rels)?;
                    tail_lhs
                        .iter_mut()
                        .for_each(|ty| substitute(constr_map, ty));
                    tail_rhs
                        .iter_mut()
                        .for_each(|ty| substitute(constr_map, ty));

                    i += 1;
                    remain_lhs = &mut fn_ty1.param_tys[i..];
                    remain_rhs = &mut fn_ty2.param_tys[i..];
                }

                fn_ty1
                    .ret_ty
                    .constrain(&mut fn_ty2.ret_ty, constr_map, prv_rels)
            }
            (TyKind::Data(dty1), TyKind::Data(dty2)) => dty1.constrain(dty2, constr_map, prv_rels),
            _ => Err(TyError::CannotUnify),
        }
    }

    fn free_idents(&self) -> HashSet<IdentKinded> {
        let mut free_idents = FreeKindedIdents::new();
        free_idents.visit_ty(self);
        free_idents.set
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
    ) -> TyResult<()> {
        match (&mut self.dty, &mut other.dty) {
            (DataTyKind::Ident(i1), DataTyKind::Ident(i2)) => {
                match (i1.is_implicit, i2.is_implicit) {
                    (true, _) => other.bind_to(i1, constr_map),
                    (false, _) => self.bind_to(i2, constr_map),
                }
            }
            (DataTyKind::Ident(i), _) => other.bind_to(i, constr_map),
            (_, DataTyKind::Ident(i)) => self.bind_to(i, constr_map),
            (DataTyKind::Scalar(sty1), DataTyKind::Scalar(sty2)) => {
                if sty1 != sty2 {
                    Err(TyError::CannotUnify)
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
                    return Err(TyError::CannotUnify);
                }
                rgn1.constrain(rgn2, constr_map, prv_rels)?;
                mem1.constrain(mem2, constr_map, prv_rels)?;
                dty1.constrain(dty2, constr_map, prv_rels)
            }
            (DataTyKind::Tuple(elem_dtys1), DataTyKind::Tuple(elem_dtys2)) => elem_dtys1
                .iter_mut()
                .zip(elem_dtys2)
                .try_for_each(|(dty1, dty2)| dty1.constrain(dty2, constr_map, prv_rels)),
            (DataTyKind::Array(dty1, n1), DataTyKind::Array(dty2, n2)) => {
                dty1.constrain(dty2, constr_map, prv_rels)?;
                n1.constrain(n2, constr_map, prv_rels)
            }
            (DataTyKind::ArrayShape(dty1, n1), DataTyKind::ArrayShape(dty2, n2)) => {
                dty1.constrain(dty2, constr_map, prv_rels)?;
                n1.constrain(n2, constr_map, prv_rels)
            }
            (DataTyKind::At(dty1, mem1), DataTyKind::At(dty2, mem2)) => {
                dty1.constrain(dty2, constr_map, prv_rels)?;
                mem1.constrain(mem2, constr_map, prv_rels)
            }
            (DataTyKind::Atomic(sty1), DataTyKind::Atomic(sty2)) => {
                if sty1 != sty2 {
                    Err(TyError::CannotUnify)
                } else {
                    Ok(())
                }
            }
            (DataTyKind::Range, DataTyKind::Range) => Ok(()),
            (DataTyKind::RawPtr(_), DataTyKind::RawPtr(_)) => {
                unimplemented!()
            }
            (DataTyKind::Dead(_), _) => {
                panic!()
            }
            _ => Err(TyError::CannotUnify),
        }
    }

    fn free_idents(&self) -> HashSet<IdentKinded> {
        let mut free_idents = FreeKindedIdents::new();
        free_idents.visit_dty(self);
        free_idents.set
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
    ) -> TyResult<()> {
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
            _ => Err(TyError::String(format!(
                "Cannot Unify: {} and {}",
                &self.ty, &other.ty
            ))),
        }
    }

    fn free_idents(&self) -> HashSet<IdentKinded> {
        let mut free_idents = FreeKindedIdents::new();
        free_idents.visit_exec_ty(self);
        free_idents.set
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
    ) -> TyResult<()> {
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
            _ => Err(TyError::CannotUnify),
        }
    }

    fn free_idents(&self) -> HashSet<IdentKinded> {
        let mut free_idents = FreeKindedIdents::new();
        free_idents.visit_dim(self);
        free_idents.set
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
    ) -> TyResult<()> {
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

    fn unify(n1: &Nat, n2: &Nat, _constr_map: &mut ConstrainMap) -> TyResult<()> {
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
    ) -> TyResult<()> {
        match (&mut *self, &mut *other) {
            (Nat::Ident(n1i), Nat::Ident(n2i)) => match (n1i.is_implicit, n2i.is_implicit) {
                (true, _) => other.bind_to(n1i, constr_map, prv_rels),
                (false, _) => self.bind_to(n2i, constr_map, prv_rels),
            },
            (Nat::Ident(n1i), _) => other.bind_to(n1i, constr_map, prv_rels),
            (_, Nat::Ident(n2i)) => self.bind_to(n2i, constr_map, prv_rels),
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

    fn free_idents(&self) -> HashSet<IdentKinded> {
        let mut free_idents = FreeKindedIdents::new();
        free_idents.visit_nat(self);
        free_idents.set
    }

    fn substitute(&mut self, subst: &ConstrainMap) {
        let mut apply_subst = ApplySubst::new(subst);
        apply_subst.visit_nat(self);
    }
}

impl Memory {
    fn bind_to(&self, ident: &Ident, constr_map: &mut ConstrainMap) -> TyResult<()> {
        if Self::occurs_check(&IdentKinded::new(ident, Kind::Memory), self) {
            return Err(TyError::InfiniteType);
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
    ) -> TyResult<()> {
        match (&mut *self, &mut *other) {
            (Memory::Ident(i1), Memory::Ident(i2)) if i1 == i2 => Ok(()),
            (Memory::Ident(i1), Memory::Ident(i2)) => match (i1.is_implicit, i2.is_implicit) {
                (true, _) => other.bind_to(i1, constr_map),
                (false, _) => self.bind_to(i2, constr_map),
            },
            (Memory::Ident(i), o) => o.bind_to(i, constr_map),
            (s, Memory::Ident(i)) => s.bind_to(i, constr_map),
            (mem1, mem2) if mem1 == mem2 => Ok(()),
            _ => Err(TyError::CannotUnify),
        }
    }

    fn free_idents(&self) -> HashSet<IdentKinded> {
        let mut free_idents = FreeKindedIdents::new();
        free_idents.visit_mem(self);
        free_idents.set
    }

    fn substitute(&mut self, subst: &ConstrainMap) {
        let mut apply_subst = ApplySubst::new(subst);
        apply_subst.visit_mem(self);
    }
}

impl Constrainable for Provenance {
    fn constrain(
        &mut self,
        other: &mut Self,
        _constr_map: &mut ConstrainMap,
        prv_rels: &mut Vec<PrvConstr>,
    ) -> TyResult<()> {
        if self == other {
            return Ok(());
        }
        prv_rels.push(PrvConstr(self.clone(), other.clone()));
        Ok(())
    }
    fn free_idents(&self) -> HashSet<IdentKinded> {
        let mut free_idents = FreeKindedIdents::new();
        free_idents.visit_prv(self);
        free_idents.set
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

    // fn visit_prv(&mut self, prv: &mut Provenance) {
    //     match prv {
    //         Provenance::Ident(ident) if self.subst.prv_constrs.contains_key(&ident.name) => {
    //             *prv = self.subst.prv_unifier.get(&ident.name).unwrap().clone()
    //         }
    //         _ => visit_mut::walk_prv(self, prv),
    //     }
    // }

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
                Nat::Ident(Ident::new("n")),
            )),
        ))))
    }

    #[test]
    fn scalar() -> TyResult<()> {
        let mut i32 = DataTy::new(DataTyKind::Scalar(ScalarTy::I32));
        let mut t = DataTy::new(DataTyKind::Ident(Ident::new("t")));
        let (subst, _) = constrain(&mut i32, &mut t)?;
        substitute(&subst, &mut i32);
        substitute(&subst, &mut t);
        assert_eq!(i32, t);
        Ok(())
    }

    #[test]
    fn shrd_reft() -> TyResult<()> {
        let mut t = DataTy::new(DataTyKind::Ident(Ident::new("t")));
        let mut shrd_ref = shrd_ref_ty();
        let (subst, _) = constrain(&mut shrd_ref, &mut t)?;
        substitute(&subst, &mut shrd_ref);
        substitute(&subst, &mut t);
        assert_eq!(shrd_ref, t);
        Ok(())
    }

    #[test]
    fn shrd_ref_inner_var() -> TyResult<()> {
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
    fn prv_val_ident() -> TyResult<()> {
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
