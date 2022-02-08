use crate::ast::visit;
use crate::ast::visit::Visit;
use crate::ast::visit_mut::VisitMut;
use crate::ast::*;
use crate::ty_check::error::TyError;
use crate::ty_check::TyResult;
use crate::utils;
use std::collections::{HashMap, HashSet};

struct BiUnifier {
    unifier: Substitution,
}

impl BiUnifier {
    fn new() -> Self {
        BiUnifier {
            unifier: Substitution::new(),
        }
    }

    fn constrain<S: Substitutable>(&mut self, t1: &S, t2: &S) -> TyResult<()> {
        t1.constrain(t2, &mut self.unifier)
    }
}

fn inst_fn_ty_scheme(
    idents_kinded: &[IdentKinded],
    param_tys: &[Ty],
    exec: Exec,
    ret_ty: &Ty,
) -> TyResult<Ty> {
    let mut subst = Substitution::new();
    for i in idents_kinded {
        match i.kind {
            Kind::Ty => {
                Ty::new(TyKind::Ident(Ident::new(&fresh_name(&i.ident.name)))).bind_to_ident(
                    &i.ident,
                    BoundKind::Upper,
                    &mut subst,
                )?;
                Ty::new(TyKind::Ident(Ident::new(&fresh_name(&i.ident.name)))).bind_to_ident(
                    &i.ident,
                    BoundKind::Lower,
                    &mut subst,
                )?;
            }
            Kind::DataTy => {
                DataTy::Ident(Ident::new(&fresh_name(&i.ident.name))).bind_to_ident(
                    &i.ident,
                    &mut subst,
                    BoundKind::Upper,
                )?;
                DataTy::Ident(Ident::new(&fresh_name(&i.ident.name))).bind_to_ident(
                    &i.ident,
                    &mut subst,
                    BoundKind::Lower,
                )?;
            }
            Kind::Nat => {
                Nat::Ident(Ident::new(&fresh_name(&i.ident.name))).bind_to(&i.ident, &mut subst)?
            }
            Kind::Memory => Memory::Ident(Ident::new(&fresh_name(&i.ident.name)))
                .bind_to(&i.ident, &mut subst)?,
            Kind::Provenance => Provenance::Ident(Ident::new(&fresh_name(&i.ident.name)))
                .bind_to(&i.ident, &mut subst)?,
        }
    }

    let mut mono_param_tys = param_tys.to_vec();
    //mono_param_tys.iter_mut().for_each(|ty| subst.apply(ty));
    let mut mono_ret_ty = ret_ty.clone();
    //subst.apply(&mut mono_ret_ty);

    Ok(Ty::new(TyKind::Fn(
        vec![],
        mono_param_tys,
        exec,
        Box::new(mono_ret_ty),
    )))
}

fn fresh_name(name: &str) -> String {
    let prefix = format!("${}", name);
    utils::fresh_name(&prefix)
}

struct Substitution {
    ty_lower_bound: HashMap<String, Vec<Ty>>,
    ty_upper_bound: HashMap<String, Vec<Ty>>,
    dty_lower_bound: HashMap<String, Vec<DataTy>>,
    dty_upper_bound: HashMap<String, Vec<DataTy>>,
    nat_unifier: HashMap<String, Nat>,
    mem_unifier: HashMap<String, Memory>,
    prv_unifier: HashMap<String, Provenance>,
}

impl Substitution {
    fn new() -> Self {
        Substitution {
            ty_lower_bound: HashMap::new(),
            ty_upper_bound: HashMap::new(),
            dty_lower_bound: HashMap::new(),
            dty_upper_bound: HashMap::new(),
            nat_unifier: HashMap::new(),
            mem_unifier: HashMap::new(),
            prv_unifier: HashMap::new(),
        }
    }

    //fn apply<S: Substitutable>(&self, s: &mut S) {
    //    s.apply_subst(self);
    //}
}

enum BoundKind {
    Upper,
    Lower,
}

impl Ty {
    fn bind_to_ident(
        &self,
        ident: &Ident,
        bound: BoundKind,
        subst: &mut Substitution,
    ) -> TyResult<()> {
        if Self::occurs_check(&IdentKinded::new(ident, Kind::Ty), self) {
            return Err(TyError::InfiniteType);
        }

        let (bounds, opposite_bounds) = match bound {
            BoundKind::Upper => (&mut subst.ty_upper_bound, &mut subst.ty_lower_bound),
            BoundKind::Lower => (&mut subst.ty_lower_bound, &mut subst.ty_upper_bound),
        };

        if let Some(bs) = bounds.get_mut(&ident.name) {
            bs.push(self.clone())
        } else {
            bounds.insert(ident.name.clone(), vec![self.clone()]);
        }
        if let Some(opp_bs) = opposite_bounds.get_mut(&ident.name) {
            opp_bs.iter().try_for_each(|b| b.constrain(self, subst))?;
        }
        Ok(())
    }
}

impl DataTy {
    fn bind_to_ident(
        &self,
        ident: &Ident,
        subst: &mut Substitution,
        polarity: BoundKind,
    ) -> TyResult<()> {
        if Self::occurs_check(&IdentKinded::new(ident, Kind::DataTy), self) {
            return Err(TyError::InfiniteType);
        }

        let (bounds, opposite_bounds) = match polarity {
            BoundKind::Upper => (&mut subst.dty_upper_bound, &mut subst.dty_lower_bound),
            BoundKind::Lower => (&mut subst.dty_lower_bound, &mut subst.dty_upper_bound),
        };

        if let Some(bs) = bounds.get_mut(&ident.name) {
            bs.push(self.clone())
        } else {
            bounds.insert(ident.name.clone(), vec![self.clone()]);
        }
        if let Some(opp_bs) = opposite_bounds.get_mut(&ident.name) {
            opp_bs.iter().try_for_each(|b| b.constrain(self, subst))?;
        }
        Ok(())
    }
}

trait Substitutable {
    fn constrain(&self, other: &Self, subst: &mut Substitution) -> TyResult<()>;
    //fn apply_subst(&mut self, subst: &Substitution);
    fn free_idents(&self) -> HashSet<IdentKinded>;

    fn occurs_check<S: Substitutable>(ident_kinded: &IdentKinded, s: &S) -> bool {
        s.free_idents().contains(ident_kinded)
    }
}

impl Substitutable for Ty {
    fn constrain(&self, other: &Self, subst: &mut Substitution) -> TyResult<()> {
        match (&self.ty, &other.ty) {
            (TyKind::Ident(i), TyKind::Ident(o)) if i == o => Ok(()),
            (TyKind::Ident(i), _) => other.bind_to_ident(i, BoundKind::Upper, subst),
            (_, TyKind::Ident(i)) => self.bind_to_ident(i, BoundKind::Lower, subst),
            (TyKind::TupleView(elem_tys1), TyKind::TupleView(elem_tys2)) => elem_tys1
                .iter()
                .zip(elem_tys2)
                .try_for_each(|(t1, t2)| t1.constrain(t2, subst)),
            (TyKind::ThreadHierchy(th1), TyKind::ThreadHierchy(th2)) => {
                match (th1.as_ref(), th2.as_ref()) {
                    (
                        ThreadHierchyTy::BlockGrp(n1, n2, n3, n4, n5, n6),
                        ThreadHierchyTy::BlockGrp(m1, m2, m3, m4, m5, m6),
                    ) => {
                        n1.constrain(m1, subst)?;
                        n2.constrain(m2, subst)?;
                        n3.constrain(m3, subst)?;
                        n4.constrain(m4, subst)?;
                        n5.constrain(m5, subst)?;
                        n6.constrain(m6, subst)
                    }
                    (
                        ThreadHierchyTy::ThreadGrp(n1, n2, n3),
                        ThreadHierchyTy::ThreadGrp(m1, m2, m3),
                    ) => {
                        n1.constrain(m1, subst)?;
                        n2.constrain(m2, subst)?;
                        n3.constrain(m3, subst)
                    }
                    (ThreadHierchyTy::WarpGrp(n), ThreadHierchyTy::WarpGrp(m)) => {
                        n.constrain(m, subst)
                    }
                    (ThreadHierchyTy::Warp, ThreadHierchyTy::Warp) => Ok(()),
                    _ => Err(TyError::CannotUnify),
                }
            }
            (
                TyKind::Fn(idents_kinded1, param_tys1, exec1, ret_ty1),
                TyKind::Fn(idents_kinded2, param_tys2, exec2, ret_ty2),
            ) => {
                assert!(idents_kinded1.is_empty());
                assert!(idents_kinded2.is_empty());

                if exec1 != exec2 {
                    return Err(TyError::CannotUnify);
                }
                param_tys1
                    .iter()
                    .zip(param_tys2)
                    .try_for_each(|(ty1, ty2)| ty1.constrain(ty2, subst))?;
                ret_ty1.constrain(ret_ty2, subst)
            }
            (TyKind::Data(dty1), TyKind::Data(dty2)) => dty1.constrain(dty2, subst),
            (TyKind::Dead(_), _) => {
                panic!()
            }
            _ => Err(TyError::CannotUnify),
        }
    }

    //fn apply_subst(&mut self, subst: &Substitution) {
    //    ApplySubst::new(subst).visit_ty(self);
    //}

    fn free_idents(&self) -> HashSet<IdentKinded> {
        let mut free_idents = FreeIdents::new();
        free_idents.visit_ty(self);
        free_idents.set
    }
}

impl Substitutable for DataTy {
    fn constrain(&self, other: &Self, subst: &mut Substitution) -> TyResult<()> {
        match (self, other) {
            (DataTy::Ident(i), _) => other.bind_to_ident(i, subst, BoundKind::Upper),
            (_, DataTy::Ident(i)) => self.bind_to_ident(i, subst, BoundKind::Lower),
            (DataTy::Scalar(sty1), DataTy::Scalar(sty2)) => {
                if sty1 != sty2 {
                    Err(TyError::CannotUnify)
                } else {
                    Ok(())
                }
            }
            (DataTy::Ref(prv1, own1, mem1, dty1), DataTy::Ref(prv2, own2, mem2, dty2)) => {
                if own1 != own2 {
                    return Err(TyError::CannotUnify);
                }
                prv1.constrain(prv2, subst)?;
                mem1.constrain(mem2, subst)?;
                dty1.constrain(dty2, subst)
            }
            (DataTy::Tuple(elem_dtys1), DataTy::Tuple(elem_dtys2)) => elem_dtys1
                .iter()
                .zip(elem_dtys2)
                .try_for_each(|(dty1, dty2)| dty1.constrain(dty2, subst)),
            (DataTy::Array(dty1, n1), DataTy::Array(dty2, n2)) => {
                dty1.constrain(dty2, subst)?;
                n1.constrain(n2, subst)
            }
            (DataTy::ArrayShape(dty1, n1), DataTy::Array(dty2, n2)) => {
                dty1.constrain(dty2, subst)?;
                n1.constrain(n2, subst)
            }
            (DataTy::At(dty1, mem1), DataTy::At(dty2, mem2)) => {
                dty1.constrain(dty2, subst)?;
                mem1.constrain(mem2, subst)
            }
            (DataTy::Atomic(sty1), DataTy::Atomic(sty2)) => {
                if sty1 != sty2 {
                    Err(TyError::CannotUnify)
                } else {
                    Ok(())
                }
            }
            (DataTy::Range, DataTy::Range) => Ok(()), // FIXME/ REMOVE
            (DataTy::RawPtr(_), DataTy::RawPtr(_)) => {
                unimplemented!()
            }
            (DataTy::Dead(_), _) => {
                panic!()
            }
            _ => Err(TyError::CannotUnify),
        }
    }

    //fn apply_subst(&mut self, subst: &Substitution) {
    //    ApplySubst::new(subst).visit_dty(self);
    //}

    fn free_idents(&self) -> HashSet<IdentKinded> {
        let mut free_idents = FreeIdents::new();
        free_idents.visit_dty(self);
        free_idents.set
    }
}

impl Nat {
    fn bind_to(&self, ident: &Ident, subst: &mut Substitution) -> TyResult<()> {
        match &self {
            _ if Self::occurs_check(&IdentKinded::new(ident, Kind::Nat), self) => {
                Err(TyError::InfiniteType)
            }
            _ => {
                subst
                    .nat_unifier
                    .values_mut()
                    .for_each(|n| SubstIdent::new(ident, self).visit_nat(n));
                if let Some(old) = subst.nat_unifier.insert(ident.name.clone(), self.clone()) {
                    panic!(
                        "Attempting to bind same variable name twice.\n\
                Old value: `{:?}` replaced by new value: `{:?}`",
                        old, self
                    )
                }
                Ok(())
            }
        }
    }
}

impl Substitutable for Nat {
    fn constrain(&self, other: &Self, subst: &mut Substitution) -> TyResult<()> {
        match (self, other) {
            (Nat::Ident(i), _) => other.bind_to(i, subst),
            (_, Nat::Ident(i)) => self.bind_to(i, subst),
            (Nat::Lit(l1), Nat::Lit(l2)) if l1 == l2 => Ok(()),
            (Nat::App(f1, ns1), Nat::App(f2, ns2)) if f1.name == f2.name => ns1
                .iter()
                .zip(ns2)
                .try_for_each(|(n1, n2)| n1.constrain(n2, subst)),
            (Nat::BinOp(op1, n1, n2), Nat::BinOp(op2, m1, m2)) if op1 == op2 => {
                n1.constrain(m1, subst)?;
                n2.constrain(m2, subst)
            }
            _ => Err(TyError::CannotUnify),
        }
    }

    //fn apply_subst(&mut self, subst: &Substitution) {
    //    ApplySubst::new(subst).visit_nat(self);
    //}

    fn free_idents(&self) -> HashSet<IdentKinded> {
        let mut free_idents = FreeIdents::new();
        free_idents.visit_nat(self);
        free_idents.set
    }
}

impl Memory {
    fn bind_to(&self, ident: &Ident, subst: &mut Substitution) -> TyResult<()> {
        match &self {
            _ if Self::occurs_check(&IdentKinded::new(ident, Kind::Memory), self) => {
                Err(TyError::InfiniteType)
            }
            _ => {
                subst
                    .mem_unifier
                    .values_mut()
                    .for_each(|m| SubstIdent::new(ident, self).visit_mem(m));
                if let Some(old) = subst.mem_unifier.insert(ident.name.clone(), self.clone()) {
                    panic!(
                        "Attempting to bind same variable name twice.\n\
                Old value: `{:?}` replaced by new value: `{:?}`",
                        old, self
                    )
                }
                Ok(())
            }
        }
    }
}

impl Substitutable for Memory {
    fn constrain(&self, other: &Self, subst: &mut Substitution) -> TyResult<()> {
        match (self, other) {
            (Memory::Ident(i), _) => other.bind_to(i, subst),
            (_, Memory::Ident(i)) => self.bind_to(i, subst),
            (mem1, mem2) if mem1 == mem2 => Ok(()),
            _ => Err(TyError::CannotUnify),
        }
    }

    //fn apply_subst(&mut self, subst: &Substitution) {
    //    ApplySubst::new(subst).visit_mem(self);
    //}

    fn free_idents(&self) -> HashSet<IdentKinded> {
        let mut free_idents = FreeIdents::new();
        free_idents.visit_mem(self);
        free_idents.set
    }
}

impl Provenance {
    fn bind_to(&self, ident: &Ident, subst: &mut Substitution) -> TyResult<()> {
        match &self {
            _ if Self::occurs_check(&IdentKinded::new(ident, Kind::Provenance), self) => {
                Err(TyError::InfiniteType)
            }
            _ => {
                subst
                    .prv_unifier
                    .values_mut()
                    .for_each(|prv| SubstIdent::new(ident, self).visit_prv(prv));
                if let Some(old) = subst.prv_unifier.insert(ident.name.clone(), self.clone()) {
                    panic!(
                        "Attempting to bind same variable name twice.\n\
                Old value: `{:?}` replaced by new value: `{:?}`",
                        old, self
                    )
                }
                Ok(())
            }
        }
    }
}

impl Substitutable for Provenance {
    fn constrain(&self, other: &Self, subst: &mut Substitution) -> TyResult<()> {
        match (self, other) {
            (Provenance::Ident(i), _) => other.bind_to(i, subst),
            (_, Provenance::Ident(i)) => self.bind_to(i, subst),
            // FIXME probably wrong. How does unification work with subtyping?
            (Provenance::Value(r1), Provenance::Value(r2)) if r1 == r2 => Ok(()),
            _ => Err(TyError::CannotUnify),
        }
    }

    //fn apply_subst(&mut self, subst: &Substitution) {
    //    ApplySubst::new(subst).visit_prv(self);
    //}

    fn free_idents(&self) -> HashSet<IdentKinded> {
        let mut free_idents = FreeIdents::new();
        free_idents.visit_prv(self);
        free_idents.set
    }
}

struct ApplySubst<'a> {
    subst: &'a Substitution,
}

//impl<'a> ApplySubst<'a> {
//    fn new(subst: &'a Substitution) -> Self {
//        ApplySubst { subst }
//    }
//}
//
//impl<'a> VisitMut for ApplySubst<'a> {
//    fn visit_nat(&mut self, nat: &mut Nat) {
//        match nat {
//            Nat::Ident(ident) if self.subst.nat_unifier.contains_key(&ident.name) => {
//                *nat = self.subst.nat_unifier.get(&ident.name).unwrap().clone();
//            }
//            _ => visit_mut::walk_nat(self, nat),
//        }
//    }
//
//    fn visit_mem(&mut self, mem: &mut Memory) {
//        match mem {
//            Memory::Ident(ident) if self.subst.mem_unifier.contains_key(&ident.name) => {
//                *mem = self.subst.mem_unifier.get(&ident.name).unwrap().clone();
//            }
//            _ => visit_mut::walk_mem(self, mem),
//        }
//    }
//
//    fn visit_prv(&mut self, prv: &mut Provenance) {
//        match prv {
//            Provenance::Ident(ident) if self.subst.prv_unifier.contains_key(&ident.name) => {
//                *prv = self.subst.prv_unifier.get(&ident.name).unwrap().clone()
//            }
//            _ => visit_mut::walk_prv(self, prv),
//        }
//    }
//
//    fn visit_dty(&mut self, dty: &mut DataTy) {
//        match dty {
//            DataTy::Ident(ident) if self.subst.dty_unifier.contains_key(&ident.name) => {
//                *dty = self.subst.dty_unifier.get(&ident.name).unwrap().clone()
//            }
//            _ => visit_mut::walk_dty(self, dty),
//        }
//    }
//
//    fn visit_ty(&mut self, ty: &mut Ty) {
//        match &mut ty.ty {
//            TyKind::Ident(ident) if self.subst.ty_lower_bound.contains_key(&ident.name) => {
//                *ty = self.subst.ty_lower_bound.get(&ident.name).unwrap().clone()
//            }
//            _ => visit_mut::walk_ty(self, ty),
//        }
//    }
//}

struct SubstIdent<'a, S: Substitutable> {
    ident: &'a Ident,
    term: &'a S,
}

impl<'a, S: Substitutable> SubstIdent<'a, S> {
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
        match dty {
            DataTy::Ident(ident) if ident.name == self.ident.name => *dty = self.term.clone(),
            _ => visit_mut::walk_dty(self, dty),
        }
    }
}

struct FreeIdents {
    set: HashSet<IdentKinded>,
}

impl FreeIdents {
    fn new() -> Self {
        FreeIdents {
            set: HashSet::new(),
        }
    }
}

impl Visit for FreeIdents {
    fn visit_nat(&mut self, nat: &Nat) {
        match nat {
            Nat::Ident(ident) => self
                .set
                .extend(std::iter::once(IdentKinded::new(ident, Kind::Nat))),
            //Nat::App(ident, args) =>
            _ => visit::walk_nat(self, nat),
        }
    }

    fn visit_mem(&mut self, mem: &Memory) {
        match mem {
            Memory::Ident(ident) => self
                .set
                .extend(std::iter::once(IdentKinded::new(ident, Kind::Memory))),
            _ => visit::walk_mem(self, mem),
        }
    }

    fn visit_prv(&mut self, prv: &Provenance) {
        match prv {
            Provenance::Ident(ident) => self
                .set
                .extend(std::iter::once(IdentKinded::new(ident, Kind::Provenance))),
            _ => visit::walk_prv(self, prv),
        }
    }

    fn visit_ty(&mut self, ty: &Ty) {
        match &ty.ty {
            TyKind::Ident(ident) => self
                .set
                .extend(std::iter::once(IdentKinded::new(ident, Kind::Ty))),
            TyKind::Fn(idents_kinded, param_tys, _, ret_ty) => {
                if !idents_kinded.is_empty() {
                    panic!("Generic function types can not appear, only their instatiated counter parts.")
                }

                walk_list!(self, visit_ty, param_tys);
            }
            _ => visit::walk_ty(self, ty),
        }
    }
}
