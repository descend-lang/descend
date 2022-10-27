use crate::ast::utils::FreeKindedIdents;
use crate::ast::visit::Visit;
use crate::ast::visit_mut::VisitMut;
use crate::ast::*;
use crate::ty_check::ctxs::{KindCtx, TyCtx};
use crate::ty_check::error::TyError;
use crate::ty_check::subty::multiple_outlives;
use crate::ty_check::TyResult;
use core::fmt;
use std::collections::{HashMap, HashSet};

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

pub(crate) fn constrain<S: Constrainable>(
    t1: &S,
    t2: &S,
) -> TyResult<(ConstrainMap, Vec<PrvConstr>)> {
    let mut constr_map = ConstrainMap::new();
    let mut prv_rels = Vec::new();
    t1.constrain(t2, &mut constr_map, &mut prv_rels)?;
    Ok((constr_map, prv_rels))
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub(crate) struct PrvConstr(pub Provenance, pub Provenance);

#[derive(Debug, Clone)]
pub(crate) struct ConstrainMap {
    pub ty_unifier: HashMap<String, Ty>,
    pub dty_unifier: HashMap<String, DataTy>,
    pub nat_unifier: HashMap<String, Nat>,
    pub mem_unifier: HashMap<String, Memory>,
}

impl ConstrainMap {
    pub fn new() -> Self {
        ConstrainMap {
            ty_unifier: HashMap::new(),
            dty_unifier: HashMap::new(),
            nat_unifier: HashMap::new(),
            mem_unifier: HashMap::new(),
        }
    }

    pub fn clear(&mut self) {
        self.ty_unifier.clear();
        self.dty_unifier.clear();
        self.nat_unifier.clear();
        self.mem_unifier.clear();
    }

    pub fn is_empty(&self) -> bool {
        self.ty_unifier.is_empty()
            && self.dty_unifier.is_empty()
            && self.nat_unifier.is_empty()
            && self.mem_unifier.is_empty()
    }

    /// Compose two substitutions `other` \circ `self`
    pub fn composition(&mut self, other: ConstrainMap) {
        if !other.is_empty() {
            self.ty_unifier
                .iter()
                .for_each(|(name, _)| assert!(other.ty_unifier.get(name).is_none()));
            self.dty_unifier
                .iter()
                .for_each(|(name, _)| assert!(other.ty_unifier.get(name).is_none()));
            self.nat_unifier
                .iter()
                .for_each(|(name, _)| assert!(other.ty_unifier.get(name).is_none()));
            self.mem_unifier
                .iter()
                .for_each(|(name, _)| assert!(other.ty_unifier.get(name).is_none()));

            self.ty_unifier
                .iter_mut()
                .for_each(|(_, bound)| bound.substitute(&other));
            self.dty_unifier
                .iter_mut()
                .for_each(|(_, bound)| bound.substitute(&other));
            self.nat_unifier
                .iter_mut()
                .for_each(|(_, bound)| bound.substitute(&other));
            self.mem_unifier
                .iter_mut()
                .for_each(|(_, bound)| bound.substitute(&other));

            self.ty_unifier.extend(other.ty_unifier.into_iter());
            self.dty_unifier.extend(other.dty_unifier.into_iter());
            self.nat_unifier.extend(other.nat_unifier.into_iter());
            self.mem_unifier.extend(other.mem_unifier.into_iter());
        }
    }
}

impl Ty {
    fn bind_to_ident(&self, ident: &Ident, constr_map: &mut ConstrainMap) -> TyResult<()> {
        if let TyKind::Ident(ty_id) = &self.ty {
            if ty_id == ident {
                return Ok(());
            }
        }
        if Self::occurs_check(&IdentKinded::new(ident, Kind::Ty), self) {
            return Err(TyError::InfiniteType);
        }
        let mut self_ty = self.clone();
        self_ty.substitute(&constr_map);
        constr_map.ty_unifier.insert(ident.name.clone(), self_ty);
        constr_map
            .ty_unifier
            .values_mut()
            .for_each(|ty| SubstIdent::new(ident, self).visit_ty(ty));
        Ok(())
    }
}

impl DataTy {
    fn bind_to_ident(&self, ident: &Ident, constr_map: &mut ConstrainMap) -> TyResult<()> {
        if let DataTyKind::Ident(ty_id) = &self.dty {
            if ty_id == ident {
                return Ok(());
            }
        }
        if Self::occurs_check(&IdentKinded::new(ident, Kind::DataTy), self) {
            return Err(TyError::InfiniteType);
        }

        let mut self_dty = self.clone();
        self_dty.substitute(&constr_map);
        constr_map.dty_unifier.insert(ident.name.clone(), self_dty);
        constr_map
            .dty_unifier
            .values_mut()
            .for_each(|dty| SubstIdent::new(ident, self).visit_dty(dty));
        Ok(())
    }
}

pub(crate) trait Constrainable: fmt::Debug {
    fn constrain(
        &self,
        other: &Self,
        constr_map: &mut ConstrainMap,
        prv_rels: &mut Vec<PrvConstr>,
    ) -> TyResult<()>;
    fn free_idents(&self) -> HashSet<IdentKinded>;
    fn substitute(&mut self, subst: &ConstrainMap);

    fn occurs_check<S: Constrainable>(ident_kinded: &IdentKinded, s: &S) -> bool {
        s.free_idents().contains(ident_kinded)
    }
}

impl Constrainable for ArgKinded {
    fn constrain(
        &self,
        other: &Self,
        constr_map: &mut ConstrainMap,
        prv_rels: &mut Vec<PrvConstr>,
    ) -> TyResult<()> {
        match (self, other) {
            (ArgKinded::Ident(_), ArgKinded::Ident(_)) => unimplemented!("needed?"),
            (ArgKinded::DataTy(dt1), ArgKinded::DataTy(dt2)) => {
                dt1.constrain(dt2, constr_map, prv_rels)
            }
            (ArgKinded::Memory(mem1), ArgKinded::Memory(mem2)) => {
                mem1.constrain(mem2, constr_map, prv_rels)
            }
            (ArgKinded::Nat(nat1), ArgKinded::Nat(nat2)) => {
                nat1.constrain(nat2, constr_map, prv_rels)
            }
            (ArgKinded::Provenance(prov1), ArgKinded::Provenance(prov2)) => {
                prov1.constrain(prov2, constr_map, prv_rels)
            }
            (ArgKinded::Ty(ty1), ArgKinded::Ty(ty2)) => ty1.constrain(ty2, constr_map, prv_rels),
            _ => Err(TyError::CannotUnify),
        }
    }

    fn free_idents(&self) -> HashSet<IdentKinded> {
        let mut free_idents = FreeKindedIdents::new();
        free_idents.visit_arg_kinded(self);
        free_idents.set
    }

    fn substitute(&mut self, subst: &ConstrainMap) {
        let mut apply_subst = ApplySubst::new(subst);
        apply_subst.visit_arg_kinded(self);
    }
}

impl Constrainable for Constraint {
    fn constrain(
        &self,
        other: &Self,
        constr_map: &mut ConstrainMap,
        prv_rels: &mut Vec<PrvConstr>,
    ) -> TyResult<()> {
        if self.trait_bound.name != other.trait_bound.name {
            return Err(TyError::CannotUnify);
        }

        self.param.constrain(&other.param, constr_map, prv_rels)?;
        self.trait_bound
            .constrain(&other.trait_bound, constr_map, prv_rels)
    }

    fn free_idents(&self) -> HashSet<IdentKinded> {
        let mut free_idents = FreeKindedIdents::new();
        free_idents.visit_constraint(self);
        free_idents.set
    }

    fn substitute(&mut self, subst: &ConstrainMap) {
        let mut apply_subst = ApplySubst::new(subst);
        apply_subst.visit_constraint(self);
    }
}

impl Constrainable for TraitMonoType {
    fn constrain(
        &self,
        other: &Self,
        constr_map: &mut ConstrainMap,
        prv_rels: &mut Vec<PrvConstr>,
    ) -> TyResult<()> {
        if self.name != other.name {
            return Err(TyError::CannotUnify);
        }

        assert!(self.generic_args.len() == other.generic_args.len());
        self.generic_args
            .iter()
            .zip(other.generic_args.iter())
            .try_for_each(|(arg_ty1, arg_ty2)| arg_ty1.constrain(arg_ty2, constr_map, prv_rels))
    }

    fn free_idents(&self) -> HashSet<IdentKinded> {
        let mut free_idents = FreeKindedIdents::new();
        free_idents.visit_trait_mono_ty(self);
        free_idents.set
    }

    fn substitute(&mut self, subst: &ConstrainMap) {
        let mut apply_subst = ApplySubst::new(subst);
        apply_subst.visit_trait_mono_ty(self);
    }
}

impl Constrainable for Ty {
    fn constrain(
        &self,
        other: &Self,
        constr_map: &mut ConstrainMap,
        prv_rels: &mut Vec<PrvConstr>,
    ) -> TyResult<()> {
        match (&self.ty, &other.ty) {
            (TyKind::Ident(i), _) if i.is_implicit => other.bind_to_ident(i, constr_map),
            (_, TyKind::Ident(i)) if i.is_implicit => self.bind_to_ident(i, constr_map),
            (TyKind::Ident(i1), TyKind::Ident(i2)) if i1 == i2 => Ok(()),
            (TyKind::Fn(param_tys1, exec1, ret_ty1), TyKind::Fn(param_tys2, exec2, ret_ty2)) => {
                if exec1 != exec2 {
                    return Err(TyError::CannotUnify);
                }
                if param_tys1.len() != param_tys2.len() {
                    return Err(TyError::CannotUnify);
                }
                // substitute result of unification for every following unification
                // TODO Refactor: create iterator over Some((next_lhs, tail_lhs), (next_rhs, tail_rhs))?
                //  move into function
                let mut param_tys1 = param_tys1.clone();
                let mut param_tys2 = param_tys2.clone();
                let mut i = 0;
                let mut remain_lhs = &mut param_tys1[i..];
                let mut remain_rhs = &mut param_tys2[i..];
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
                    remain_lhs = &mut param_tys1[i..];
                    remain_rhs = &mut param_tys2[i..];
                }

                ret_ty1.constrain(ret_ty2, constr_map, prv_rels)
            }
            (TyKind::Data(dty1), TyKind::Data(dty2)) => dty1.constrain(dty2, constr_map, prv_rels),
            (TyKind::Dead(_), _) => {
                panic!()
            }
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
        &self,
        other: &Self,
        constr_map: &mut ConstrainMap,
        prv_rels: &mut Vec<PrvConstr>,
    ) -> TyResult<()> {
        match (&self.dty, &other.dty) {
            (DataTyKind::Ident(i), _) if i.is_implicit => other.bind_to_ident(i, constr_map),
            (_, DataTyKind::Ident(i)) if i.is_implicit => self.bind_to_ident(i, constr_map),
            (DataTyKind::Ident(i1), DataTyKind::Ident(i2)) if i1 == i2 => Ok(()),
            (DataTyKind::Scalar(sty1), DataTyKind::Scalar(sty2)) => {
                if sty1 != sty2 {
                    Err(TyError::CannotUnify)
                } else {
                    Ok(())
                }
            }
            (DataTyKind::Ref(prv1, own1, mem1, dty1), DataTyKind::Ref(prv2, own2, mem2, dty2)) => {
                if own1 != own2 {
                    return Err(TyError::CannotUnify);
                }
                prv1.constrain(prv2, constr_map, prv_rels)?;
                mem1.constrain(mem2, constr_map, prv_rels)?;
                dty1.constrain(dty2, constr_map, prv_rels)
            }
            (DataTyKind::Tuple(elem_dtys1), DataTyKind::Tuple(elem_dtys2)) => elem_dtys1
                .iter()
                .zip(elem_dtys2)
                .try_for_each(|(dty1, dty2)| dty1.constrain(dty2, constr_map, prv_rels)),
            (DataTyKind::Struct(struct_1), DataTyKind::Struct(struct_2)) => {
                if struct_1.name != struct_2.name {
                    return Err(TyError::CannotUnify);
                }
                assert!(struct_1.generic_args.len() == struct_2.generic_args.len());
                assert!(struct_1.struct_fields.len() == struct_2.struct_fields.len());
                struct_1
                    .generic_args
                    .iter()
                    .zip(struct_2.generic_args.iter())
                    .try_for_each(|(gen1, gen2)| gen1.constrain(gen2, constr_map, prv_rels))?;
                struct_1.struct_fields.iter().try_for_each(|attr1| {
                    attr1.dty.constrain(
                        &struct_2
                            .struct_fields
                            .iter()
                            .find(|attr2| attr1.name == attr2.name)
                            .unwrap()
                            .dty,
                        constr_map,
                        prv_rels,
                    )
                })
            }
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
            (DataTyKind::ThreadHierchy(th1), DataTyKind::ThreadHierchy(th2)) => {
                match (th1.as_ref(), th2.as_ref()) {
                    (
                        ThreadHierchyTy::BlockGrp(n1, n2, n3, n4, n5, n6),
                        ThreadHierchyTy::BlockGrp(m1, m2, m3, m4, m5, m6),
                    ) => {
                        n1.constrain(m1, constr_map, prv_rels)?;
                        n2.constrain(m2, constr_map, prv_rels)?;
                        n3.constrain(m3, constr_map, prv_rels)?;
                        n4.constrain(m4, constr_map, prv_rels)?;
                        n5.constrain(m5, constr_map, prv_rels)?;
                        n6.constrain(m6, constr_map, prv_rels)
                    }
                    (
                        ThreadHierchyTy::ThreadGrp(n1, n2, n3),
                        ThreadHierchyTy::ThreadGrp(m1, m2, m3),
                    ) => {
                        n1.constrain(m1, constr_map, prv_rels)?;
                        n2.constrain(m2, constr_map, prv_rels)?;
                        n3.constrain(m3, constr_map, prv_rels)
                    }
                    (ThreadHierchyTy::WarpGrp(n), ThreadHierchyTy::WarpGrp(m)) => {
                        n.constrain(m, constr_map, prv_rels)
                    }
                    (ThreadHierchyTy::Warp, ThreadHierchyTy::Warp) => Ok(()),
                    _ => Err(TyError::CannotUnify),
                }
            }
            (DataTyKind::Range, DataTyKind::Range) => Ok(()), // FIXME/ REMOVE
            (DataTyKind::RawPtr(_), DataTyKind::RawPtr(_)) => {
                unimplemented!()
            }
            (DataTyKind::Dead(_), _) => {
                panic!(
                    "Found a dead type.\n Tried to unify {:#?} with {:#?}",
                    self, other
                )
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

impl Nat {
    fn bind_to(
        &self,
        ident: &Ident,
        constr_map: &mut ConstrainMap,
        _: &mut Vec<PrvConstr>,
    ) -> TyResult<()> {
        // Nats can be equal to an expression in which the nat appears again. E.g., a = a * 1
        // match &self {
        //     _ if Self::occurs_check(&IdentKinded::new(ident, Kind::Nat), self) => {
        //         Err(TyError::InfiniteType)
        //     }
        //     _ => {
        constr_map
            .nat_unifier
            .values_mut()
            .for_each(|n| SubstIdent::new(ident, self).visit_nat(n));
        if let Some(old) = constr_map
            .nat_unifier
            .insert(ident.name.clone(), self.clone())
        {
            if old != *self {
                println!(
                    "WARNING: Not able to check equality of Nats `{}` and `{}`",
                    old, self
                )
            }
        }
        Ok(())
    }

    // FIXME: Add constrains?!
    fn unify(n1: &Nat, n2: &Nat, constr_map: &mut ConstrainMap) -> TyResult<()> {
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
        &self,
        other: &Self,
        constr_map: &mut ConstrainMap,
        prv_rels: &mut Vec<PrvConstr>,
    ) -> TyResult<()> {
        match (&*self, &*other) {
            (Nat::Ident(n1i), Nat::Ident(n2i)) => match (n1i.is_implicit, n2i.is_implicit) {
                (true, true) => other.bind_to(n1i, constr_map, prv_rels),
                (true, false) => other.bind_to(n1i, constr_map, prv_rels),
                (false, true) => self.bind_to(n2i, constr_map, prv_rels),
                (false, false) => {
                    if n1i != n2i {
                        panic!(
                            "We can probably not bind to explicitly declared identifiers\
                            `{}` and `{}`.",
                            n1i, n2i
                        )
                    } else {
                        Ok(())
                    }
                }
            },
            (Nat::Ident(n1i), _) if n1i.is_implicit => other.bind_to(n1i, constr_map, prv_rels),
            (_, Nat::Ident(n2i)) if n2i.is_implicit => self.bind_to(n2i, constr_map, prv_rels),
            _ => Self::unify(self, other, constr_map),
        }
    }

    fn substitute(&mut self, subst: &ConstrainMap) {
        let mut apply_subst = ApplySubst::new(subst);
        apply_subst.visit_nat(self);
    }

    fn free_idents(&self) -> HashSet<IdentKinded> {
        let mut free_idents = FreeKindedIdents::new();
        free_idents.visit_nat(self);
        free_idents.set
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
        let mut self_mem = self.clone();
        self_mem.substitute(&constr_map);
        constr_map.mem_unifier.insert(ident.name.clone(), self_mem);
        constr_map
            .mem_unifier
            .values_mut()
            .for_each(|m| SubstIdent::new(ident, self).visit_mem(m));
        Ok(())
    }
}

impl Constrainable for Memory {
    fn constrain(
        &self,
        other: &Self,
        constr_map: &mut ConstrainMap,
        _: &mut Vec<PrvConstr>,
    ) -> TyResult<()> {
        match (self, other) {
            (Memory::Ident(i1), Memory::Ident(i2)) if i1 == i2 => Ok(()),
            (Memory::Ident(i), o) if i.is_implicit => o.bind_to(i, constr_map),
            (s, Memory::Ident(i)) if i.is_implicit => s.bind_to(i, constr_map),
            (mem1, mem2) if mem1 == mem2 => Ok(()),
            _ => Err(TyError::CannotUnify),
        }
    }

    fn substitute(&mut self, subst: &ConstrainMap) {
        let mut apply_subst = ApplySubst::new(subst);
        apply_subst.visit_mem(self);
    }

    fn free_idents(&self) -> HashSet<IdentKinded> {
        let mut free_idents = FreeKindedIdents::new();
        free_idents.visit_mem(self);
        free_idents.set
    }
}

impl Provenance {
    fn bind_to(&self, ident: &Ident, constr_map: &mut ConstrainMap) -> TyResult<()> {
        unimplemented!()
        // match &self {
        //     _ if Self::occurs_check(&IdentKinded::new(ident, Kind::Provenance), self) => {
        //         Err(TyError::InfiniteType)
        //     }
        //
        //         // if let Some(old) = constr_map
        //         //     .prv_unifier
        //         //     .insert(ident.name.clone(), self.clone())
        //         // {
        //         //     if &old != self {
        //         //         panic!(
        //         //             "Attempting to bind to same variable name twice.\n\
        //         // Old value: `{:?}` replaced by new value: `{:?}`",
        //         //             old, self
        //         //         )
        //         //     }
        //         // }
        //         Ok(())
        //     }
        // }
    }
}

impl Constrainable for Provenance {
    fn constrain(
        &self,
        other: &Self,
        constr_map: &mut ConstrainMap,
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

    fn visit_ty(&mut self, ty: &mut Ty) {
        match &mut ty.ty {
            TyKind::Ident(ident) if self.subst.ty_unifier.contains_key(&ident.name) => {
                *ty = self.subst.ty_unifier.get(&ident.name).unwrap().clone()
            }
            _ => visit_mut::walk_ty(self, ty),
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

impl<'a> VisitMut for SubstIdent<'a, Ty> {
    fn visit_ty(&mut self, ty: &mut Ty) {
        match &mut ty.ty {
            TyKind::Ident(ident) if ident.name == self.ident.name => *ty = self.term.clone(),
            _ => visit_mut::walk_ty(self, ty),
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

#[test]
fn scalar() -> TyResult<()> {
    let mut i32 = DataTy::new(DataTyKind::Scalar(ScalarTy::I32));
    let mut t = DataTy::new(DataTyKind::Ident(Ident::new_impli("t")));
    let (subst, _) = constrain(&i32, &t)?;
    substitute(&subst, &mut i32);
    substitute(&subst, &mut t);
    assert_eq!(i32, t);
    Ok(())
}

#[test]
fn shrd_ref() -> TyResult<()> {
    let mut shrd_ref = DataTy::new(DataTyKind::Ref(
        Provenance::Value("r".to_string()),
        Ownership::Shrd,
        Memory::GpuGlobal,
        Box::new(DataTy::new(DataTyKind::Array(
            Box::new(DataTy::new(DataTyKind::Scalar(ScalarTy::I32))),
            Nat::Ident(Ident::new("n")),
        ))),
    ));
    let mut t = DataTy::new(DataTyKind::Ident(Ident::new_impli("t")));
    let (subst, _) = constrain(&shrd_ref, &t)?;
    substitute(&subst, &mut shrd_ref);
    substitute(&subst, &mut t);
    assert_eq!(shrd_ref, t);
    Ok(())
}

#[test]
fn shrd_ref_inner_var() -> TyResult<()> {
    let mut shrd_ref = DataTy::new(DataTyKind::Ref(
        Provenance::Value("r".to_string()),
        Ownership::Shrd,
        Memory::GpuGlobal,
        Box::new(DataTy::new(DataTyKind::Array(
            Box::new(DataTy::new(DataTyKind::Scalar(ScalarTy::I32))),
            Nat::Ident(Ident::new("n")),
        ))),
    ));
    let mut shrd_ref_t = DataTy::new(DataTyKind::Ref(
        Provenance::Value("r".to_string()),
        Ownership::Shrd,
        Memory::GpuGlobal,
        Box::new(DataTy::new(DataTyKind::Ident(Ident::new_impli("t")))),
    ));
    let (subst, _) = constrain(&shrd_ref, &shrd_ref_t)?;
    substitute(&subst, &mut shrd_ref);
    substitute(&subst, &mut shrd_ref_t);
    assert_eq!(shrd_ref, shrd_ref_t);
    Ok(())
}

#[test]
fn prv_val_ident() -> TyResult<()> {
    let mut shrd_ref = DataTy::new(DataTyKind::Ref(
        Provenance::Value("r".to_string()),
        Ownership::Shrd,
        Memory::GpuGlobal,
        Box::new(DataTy::new(DataTyKind::Array(
            Box::new(DataTy::new(DataTyKind::Scalar(ScalarTy::I32))),
            Nat::Ident(Ident::new("n")),
        ))),
    ));
    let mut shrd_ref_t = DataTy::new(DataTyKind::Ref(
        Provenance::Ident(Ident::new("a")),
        Ownership::Shrd,
        Memory::GpuGlobal,
        Box::new(DataTy::new(DataTyKind::Ident(Ident::new_impli("t")))),
    ));
    let (subst, prv_rels) = constrain(&shrd_ref, &shrd_ref_t)?;
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
