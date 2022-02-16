use crate::ast::visit;
use crate::ast::visit::Visit;
use crate::ast::visit_mut::VisitMut;
use crate::ast::*;
use crate::ty_check::ctxs::TyCtx;
use crate::ty_check::error::TyError;
use crate::ty_check::{TyChecker, TyResult};
use crate::utils;
use std::collections::{HashMap, HashSet};

pub(super) struct TermConstrainer {
    pub(super) constr_map: ConstrainMap,
}

impl TermConstrainer {
    pub(super) fn new() -> Self {
        TermConstrainer {
            constr_map: ConstrainMap::new(),
        }
    }

    pub(super) fn constrain<S: Constrainable>(
        &mut self,
        ty_ctx: &mut TyCtx,
        t1: &S,
        t2: &S,
    ) -> TyResult<()> {
        t1.constrain(ty_ctx, t2, &mut self.constr_map)
    }
}

pub(super) fn inst_fn_ty_scheme(
    idents_kinded: &[IdentKinded],
    param_tys: &[Ty],
    exec: Exec,
    ret_ty: &Ty,
) -> TyResult<Ty> {
    let mono_idents: Vec<_> = idents_kinded
        .iter()
        .map(|i| match i.kind {
            Kind::Ty => ArgKinded::Ty(Ty::new(fresh_ident(&i.ident.name, TyKind::Ident))),
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

    let mut mono_param_tys = param_tys
        .iter()
        .map(|ty| TyChecker::subst_ident_kinded(idents_kinded, mono_idents.as_slice(), ty))
        .collect();
    let mut mono_ret_ty =
        TyChecker::subst_ident_kinded(idents_kinded, mono_idents.as_slice(), ret_ty);

    Ok(Ty::new(TyKind::Fn(
        vec![],
        mono_param_tys,
        exec,
        Box::new(mono_ret_ty),
    )))
}

pub(super) fn fresh_ident<F, R>(name: &str, ident_constr: F) -> R
where
    F: Fn(Ident) -> R,
{
    ident_constr(Ident::new(&fresh_name(name)))
}

fn fresh_name(name: &str) -> String {
    let prefix = format!("${}", name);
    utils::fresh_name(&prefix)
}

pub(super) struct ConstrainMap {
    pub ty_lower_bound: HashMap<String, Vec<Ty>>,
    pub ty_upper_bound: HashMap<String, Vec<Ty>>,
    pub dty_lower_bound: HashMap<String, Vec<DataTy>>,
    pub dty_upper_bound: HashMap<String, Vec<DataTy>>,
    pub nat_unifier: HashMap<String, Nat>,
    pub mem_unifier: HashMap<String, Memory>,
    pub prv_lower_bound: HashMap<String, Vec<Provenance>>,
    pub prv_upper_bound: HashMap<String, Vec<Provenance>>,
}

impl ConstrainMap {
    fn new() -> Self {
        ConstrainMap {
            ty_lower_bound: HashMap::new(),
            ty_upper_bound: HashMap::new(),
            dty_lower_bound: HashMap::new(),
            dty_upper_bound: HashMap::new(),
            nat_unifier: HashMap::new(),
            mem_unifier: HashMap::new(),
            prv_lower_bound: HashMap::new(),
            prv_upper_bound: HashMap::new(),
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
        ty_ctx: &mut TyCtx,
        ident: &Ident,
        bound: BoundKind,
        constr_map: &mut ConstrainMap,
    ) -> TyResult<()> {
        if Self::occurs_check(&IdentKinded::new(ident, Kind::Ty), self) {
            return Err(TyError::InfiniteType);
        }

        let (bounds, opposite_bounds) = match bound {
            BoundKind::Upper => (
                &mut constr_map.ty_upper_bound,
                &mut constr_map.ty_lower_bound,
            ),
            BoundKind::Lower => (
                &mut constr_map.ty_lower_bound,
                &mut constr_map.ty_upper_bound,
            ),
        };

        if let Some(bs) = bounds.get_mut(&ident.name) {
            bs.push(self.clone())
        } else {
            bounds.insert(ident.name.clone(), vec![self.clone()]);
        }
        if let Some(opp_bs) = opposite_bounds.get(&ident.name) {
            opp_bs
                .clone()
                .iter()
                .try_for_each(|b| b.constrain(ty_ctx, self, constr_map))?;
        }
        Ok(())
    }
}

impl DataTy {
    fn bind_to_ident(
        &self,
        ty_ctx: &mut TyCtx,
        ident: &Ident,
        constr_map: &mut ConstrainMap,
        polarity: BoundKind,
    ) -> TyResult<()> {
        if Self::occurs_check(&IdentKinded::new(ident, Kind::DataTy), self) {
            return Err(TyError::InfiniteType);
        }

        let (bounds, opposite_bounds) = match polarity {
            BoundKind::Upper => (
                &mut constr_map.dty_upper_bound,
                &mut constr_map.dty_lower_bound,
            ),
            BoundKind::Lower => (
                &mut constr_map.dty_lower_bound,
                &mut constr_map.dty_upper_bound,
            ),
        };

        if let Some(bs) = bounds.get_mut(&ident.name) {
            bs.push(self.clone())
        } else {
            bounds.insert(ident.name.clone(), vec![self.clone()]);
        }
        if let Some(opp_bs) = opposite_bounds.get(&ident.name) {
            opp_bs
                .clone()
                .iter()
                .try_for_each(|b| b.constrain(ty_ctx, self, constr_map))?;
        }
        Ok(())
    }
}

pub(super) trait Constrainable {
    fn constrain(
        &self,
        ty_ctx: &mut TyCtx,
        other: &Self,
        constr_map: &mut ConstrainMap,
    ) -> TyResult<()>;
    fn free_idents(&self) -> HashSet<IdentKinded>;

    fn occurs_check<S: Constrainable>(ident_kinded: &IdentKinded, s: &S) -> bool {
        s.free_idents().contains(ident_kinded)
    }
}

impl Constrainable for Ty {
    fn constrain(
        &self,
        ty_ctx: &mut TyCtx,
        other: &Self,
        constr_map: &mut ConstrainMap,
    ) -> TyResult<()> {
        match (&self.ty, &other.ty) {
            (TyKind::Ident(i), TyKind::Ident(o)) if i == o => Ok(()),
            (TyKind::Ident(i), _) => other.bind_to_ident(ty_ctx, i, BoundKind::Upper, constr_map),
            (_, TyKind::Ident(i)) => self.bind_to_ident(ty_ctx, i, BoundKind::Lower, constr_map),
            (TyKind::TupleView(elem_tys1), TyKind::TupleView(elem_tys2)) => elem_tys1
                .iter()
                .zip(elem_tys2)
                .try_for_each(|(t1, t2)| t1.constrain(ty_ctx, t2, constr_map)),
            (
                TyKind::Fn(idents_kinded1, param_tys1, exec1, ret_ty1),
                TyKind::Fn(idents_kinded2, param_tys2, exec2, ret_ty2),
            ) => {
                assert!(idents_kinded1.is_empty());
                assert!(idents_kinded2.is_empty());

                if exec1 != exec2 {
                    return Err(TyError::CannotUnify);
                }
                if param_tys1.len() != param_tys2.len() {
                    return Err(TyError::CannotUnify);
                }
                param_tys1
                    .iter()
                    .zip(param_tys2)
                    .try_for_each(|(ty1, ty2)| ty1.constrain(ty_ctx, ty2, constr_map))?;
                ret_ty1.constrain(ty_ctx, ret_ty2, constr_map)
            }
            (TyKind::Data(dty1), TyKind::Data(dty2)) => dty1.constrain(ty_ctx, dty2, constr_map),
            (TyKind::Dead(_), _) => {
                panic!()
            }
            _ => Err(TyError::CannotUnify),
        }
    }

    fn free_idents(&self) -> HashSet<IdentKinded> {
        let mut free_idents = FreeIdents::new();
        free_idents.visit_ty(self);
        free_idents.set
    }
}

impl Constrainable for DataTy {
    fn constrain(
        &self,
        ty_ctx: &mut TyCtx,
        other: &Self,
        constr_map: &mut ConstrainMap,
    ) -> TyResult<()> {
        match (&self.dty, &other.dty) {
            (DataTyKind::Ident(i), _) => {
                other.bind_to_ident(ty_ctx, i, constr_map, BoundKind::Upper)
            }
            (_, DataTyKind::Ident(i)) => {
                self.bind_to_ident(ty_ctx, i, constr_map, BoundKind::Lower)
            }
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
                prv1.constrain(ty_ctx, prv2, constr_map)?;
                mem1.constrain(ty_ctx, mem2, constr_map)?;
                dty1.constrain(ty_ctx, dty2, constr_map)
            }
            (DataTyKind::Tuple(elem_dtys1), DataTyKind::Tuple(elem_dtys2)) => elem_dtys1
                .iter()
                .zip(elem_dtys2)
                .try_for_each(|(dty1, dty2)| dty1.constrain(ty_ctx, dty2, constr_map)),
            (DataTyKind::Array(dty1, n1), DataTyKind::Array(dty2, n2)) => {
                dty1.constrain(ty_ctx, dty2, constr_map)?;
                n1.constrain(ty_ctx, n2, constr_map)
            }
            (DataTyKind::ArrayShape(dty1, n1), DataTyKind::ArrayShape(dty2, n2)) => {
                dty1.constrain(ty_ctx, dty2, constr_map)?;
                n1.constrain(ty_ctx, n2, constr_map)
            }
            (DataTyKind::At(dty1, mem1), DataTyKind::At(dty2, mem2)) => {
                dty1.constrain(ty_ctx, dty2, constr_map)?;
                mem1.constrain(ty_ctx, mem2, constr_map)
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
                        n1.constrain(ty_ctx, m1, constr_map)?;
                        n2.constrain(ty_ctx, m2, constr_map)?;
                        n3.constrain(ty_ctx, m3, constr_map)?;
                        n4.constrain(ty_ctx, m4, constr_map)?;
                        n5.constrain(ty_ctx, m5, constr_map)?;
                        n6.constrain(ty_ctx, m6, constr_map)
                    }
                    (
                        ThreadHierchyTy::ThreadGrp(n1, n2, n3),
                        ThreadHierchyTy::ThreadGrp(m1, m2, m3),
                    ) => {
                        n1.constrain(ty_ctx, m1, constr_map)?;
                        n2.constrain(ty_ctx, m2, constr_map)?;
                        n3.constrain(ty_ctx, m3, constr_map)
                    }
                    (ThreadHierchyTy::WarpGrp(n), ThreadHierchyTy::WarpGrp(m)) => {
                        n.constrain(ty_ctx, m, constr_map)
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
                panic!()
            }
            _ => Err(TyError::CannotUnify),
        }
    }

    fn free_idents(&self) -> HashSet<IdentKinded> {
        let mut free_idents = FreeIdents::new();
        free_idents.visit_dty(self);
        free_idents.set
    }
}

impl Nat {
    fn bind_to(&self, ident: &Ident, constr_map: &mut ConstrainMap) -> TyResult<()> {
        match &self {
            _ if Self::occurs_check(&IdentKinded::new(ident, Kind::Nat), self) => {
                Err(TyError::InfiniteType)
            }
            _ => {
                constr_map
                    .nat_unifier
                    .values_mut()
                    .for_each(|n| SubstIdent::new(ident, self).visit_nat(n));
                if let Some(old) = constr_map
                    .nat_unifier
                    .insert(ident.name.clone(), self.clone())
                {
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

impl Constrainable for Nat {
    fn constrain(
        &self,
        _: &mut TyCtx,
        other: &Self,
        constr_map: &mut ConstrainMap,
    ) -> TyResult<()> {
        unify(self, other, constr_map)
    }

    fn free_idents(&self) -> HashSet<IdentKinded> {
        let mut free_idents = FreeIdents::new();
        free_idents.visit_nat(self);
        free_idents.set
    }
}

// FIXME: Add constrains?!
fn unify(n1: &Nat, n2: &Nat, constr_map: &mut ConstrainMap) -> TyResult<()> {
    if n1 == n2 {
        Ok(())
    } else {
        Err(TyError::CannotUnify)
    }
    //    match (n1, n2) {
    //        (Nat::Ident(i1), Nat::Ident(i2)) if i1 == i2 => Ok(()),
    //        (Nat::Ident(i), _) => n2.bind_to(i, constr_map),
    //        (_, Nat::Ident(i)) => n1.bind_to(i, constr_map),
    //        (Nat::Lit(l1), Nat::Lit(l2)) if l1 == l2 => Ok(()),
    //        (Nat::App(f1, ns1), Nat::App(f2, ns2)) if f1.name == f2.name => ns1
    //            .iter()
    //            .zip(ns2)
    //            .try_for_each(|(n1, n2)| unify(n1, n2, constr_map)),
    //        (Nat::BinOp(op1, n1, n2), Nat::BinOp(op2, m1, m2)) if op1 == op2 => {
    //            unify(n1, m1, constr_map)?;
    //            unify(n2, m2, constr_map)
    //        }
    //        _= >
    //    }
}

impl Memory {
    fn bind_to(&self, ident: &Ident, constr_map: &mut ConstrainMap) -> TyResult<()> {
        match &self {
            _ if Self::occurs_check(&IdentKinded::new(ident, Kind::Memory), self) => {
                Err(TyError::InfiniteType)
            }
            _ => {
                constr_map
                    .mem_unifier
                    .values_mut()
                    .for_each(|m| SubstIdent::new(ident, self).visit_mem(m));
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
                Ok(())
            }
        }
    }
}

impl Constrainable for Memory {
    fn constrain(
        &self,
        _: &mut TyCtx,
        other: &Self,
        constr_map: &mut ConstrainMap,
    ) -> TyResult<()> {
        match (self, other) {
            (Memory::Ident(i1), Memory::Ident(i2)) => Ok(()),
            (Memory::Ident(i), _) => other.bind_to(i, constr_map),
            (_, Memory::Ident(i)) => self.bind_to(i, constr_map),
            (mem1, mem2) if mem1 == mem2 => Ok(()),
            _ => Err(TyError::CannotUnify),
        }
    }

    fn free_idents(&self) -> HashSet<IdentKinded> {
        let mut free_idents = FreeIdents::new();
        free_idents.visit_mem(self);
        free_idents.set
    }
}

impl Provenance {
    fn bind_to(
        &self,
        ty_ctx: &mut TyCtx,
        ident: &Ident,
        constr_map: &mut ConstrainMap,
        polarity: BoundKind,
    ) -> TyResult<()> {
        match &self {
            _ if Self::occurs_check(&IdentKinded::new(ident, Kind::Provenance), self) => {
                Err(TyError::InfiniteType)
            }
            _ => {
                let (bounds, opposite_bounds) = match polarity {
                    BoundKind::Upper => (
                        &mut constr_map.prv_upper_bound,
                        &mut constr_map.prv_lower_bound,
                    ),
                    BoundKind::Lower => (
                        &mut constr_map.prv_lower_bound,
                        &mut constr_map.prv_upper_bound,
                    ),
                };
                if let Some(bs) = bounds.get_mut(&ident.name) {
                    bs.push(self.clone())
                } else {
                    bounds.insert(ident.name.clone(), vec![self.clone()]);
                }
                if let Some(opp_bs) = opposite_bounds.get(&ident.name) {
                    opp_bs
                        .clone()
                        .iter()
                        .try_for_each(|b| b.constrain(ty_ctx, self, constr_map))?;
                }

                // if let Some(old) = constr_map
                //     .prv_unifier
                //     .insert(ident.name.clone(), self.clone())
                // {
                //     if &old != self {
                //         panic!(
                //             "Attempting to bind to same variable name twice.\n\
                // Old value: `{:?}` replaced by new value: `{:?}`",
                //             old, self
                //         )
                //     }
                // }
                Ok(())
            }
        }
    }
}

impl Constrainable for Provenance {
    fn constrain(
        &self,
        ty_ctx: &mut TyCtx,
        other: &Self,
        constr_map: &mut ConstrainMap,
    ) -> TyResult<()> {
        match (self, other) {
            (Provenance::Ident(i1), Provenance::Ident(i2)) if i1 == i2 => Ok(()),
            (Provenance::Ident(i), _) => other.bind_to(ty_ctx, i, constr_map, BoundKind::Upper),
            (_, Provenance::Ident(i)) => self.bind_to(ty_ctx, i, constr_map, BoundKind::Lower),
            // FIXME probably wrong. How does unification work with subtyping?
            (Provenance::Value(r1), Provenance::Value(r2)) if r1 == r2 => Ok(()),
            _ => Err(TyError::CannotUnify),
        }
    }

    fn free_idents(&self) -> HashSet<IdentKinded> {
        let mut free_idents = FreeIdents::new();
        free_idents.visit_prv(self);
        free_idents.set
    }
}

struct IdentSubstitution {
    ty_map: HashMap<String, Ty>,
    dty_map: HashMap<String, DataTy>,
    nat_map: HashMap<String, Nat>,
    mem_map: HashMap<String, Memory>,
    prv_map: HashMap<String, Provenance>,
}

struct ApplySubst<'a> {
    subst: &'a IdentSubstitution,
}

impl<'a> ApplySubst<'a> {
    fn new(subst: &'a IdentSubstitution) -> Self {
        ApplySubst { subst }
    }
}

impl<'a> VisitMut for ApplySubst<'a> {
    fn visit_nat(&mut self, nat: &mut Nat) {
        match nat {
            Nat::Ident(ident) if self.subst.nat_map.contains_key(&ident.name) => {
                *nat = self.subst.nat_map.get(&ident.name).unwrap().clone();
            }
            _ => visit_mut::walk_nat(self, nat),
        }
    }

    fn visit_mem(&mut self, mem: &mut Memory) {
        match mem {
            Memory::Ident(ident) if self.subst.mem_map.contains_key(&ident.name) => {
                *mem = self.subst.mem_map.get(&ident.name).unwrap().clone();
            }
            _ => visit_mut::walk_mem(self, mem),
        }
    }

    fn visit_prv(&mut self, prv: &mut Provenance) {
        match prv {
            Provenance::Ident(ident) if self.subst.prv_map.contains_key(&ident.name) => {
                *prv = self.subst.prv_map.get(&ident.name).unwrap().clone()
            }
            _ => visit_mut::walk_prv(self, prv),
        }
    }

    fn visit_dty(&mut self, dty: &mut DataTy) {
        match &mut dty.dty {
            DataTyKind::Ident(ident) if self.subst.dty_map.contains_key(&ident.name) => {
                *dty = self.subst.dty_map.get(&ident.name).unwrap().clone()
            }
            _ => visit_mut::walk_dty(self, dty),
        }
    }

    fn visit_ty(&mut self, ty: &mut Ty) {
        match &mut ty.ty {
            TyKind::Ident(ident) if self.subst.ty_map.contains_key(&ident.name) => {
                *ty = self.subst.ty_map.get(&ident.name).unwrap().clone()
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