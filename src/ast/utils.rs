use crate::ast::visit::walk_list;
use crate::ast::visit::Visit;

use crate::ast::{
    visit, DataTy, DataTyKind, Expr, ExprKind, FunDef, Ident, IdentKinded, Kind, Memory, Nat,
    Provenance, Ty, TyKind,
};
use std::collections::HashSet;
use std::sync::atomic::{AtomicI32, Ordering};

static mut COUNTER: AtomicI32 = AtomicI32::new(0);

pub(crate) fn fresh_ident<F, R>(name: &str, ident_constr: F) -> R
where
    F: Fn(Ident) -> R,
{
    ident_constr(Ident::new_impli(&fresh_name(name)))
}

pub(crate) fn fresh_name(name: &str) -> String {
    let prefix = format!("${}", name);
    let i;
    unsafe {
        i = COUNTER.fetch_add(1, Ordering::SeqCst);
    }
    format!("{}_{}", prefix, i)
}

pub struct FreeKindedIdents {
    pub set: HashSet<IdentKinded>,
    pub bound_idents: HashSet<IdentKinded>,
}

impl FreeKindedIdents {
    pub fn new() -> Self {
        FreeKindedIdents {
            set: HashSet::new(),
            bound_idents: HashSet::new(),
        }
    }

    pub fn with_bound_idents(idents: HashSet<IdentKinded>) -> Self {
        FreeKindedIdents {
            set: HashSet::new(),
            bound_idents: idents,
        }
    }
}

impl Visit for FreeKindedIdents {
    fn visit_nat(&mut self, nat: &Nat) {
        match nat {
            Nat::Ident(ident) => {
                let ident_kinded = IdentKinded::new(ident, Kind::Nat);
                if !self.bound_idents.contains(&ident_kinded) {
                    self.set.extend(std::iter::once(ident_kinded))
                }
            }
            _ => visit::walk_nat(self, nat),
        }
    }

    fn visit_mem(&mut self, mem: &Memory) {
        match mem {
            Memory::Ident(ident) => {
                let ident_kinded = IdentKinded::new(ident, Kind::Memory);
                if !self.bound_idents.contains(&ident_kinded) {
                    self.set.extend(std::iter::once(ident_kinded))
                }
            }
            _ => visit::walk_mem(self, mem),
        }
    }

    fn visit_prv(&mut self, prv: &Provenance) {
        match prv {
            Provenance::Ident(ident) => {
                let ident_kinded = IdentKinded::new(ident, Kind::Provenance);
                if !self.bound_idents.contains(&ident_kinded) {
                    self.set.extend(std::iter::once(ident_kinded))
                }
            }
            _ => visit::walk_prv(self, prv),
        }
    }

    fn visit_dty(&mut self, dty: &DataTy) {
        match &dty.dty {
            DataTyKind::Ident(ident) => {
                let ident_kinded = IdentKinded::new(ident, Kind::DataTy);
                if !self.bound_idents.contains(&ident_kinded) {
                    self.set.extend(std::iter::once(ident_kinded))
                }
            }
            _ => visit::walk_dty(self, dty),
        }
    }

    fn visit_ty(&mut self, ty: &Ty) {
        match &ty.ty {
            TyKind::FnTy(fn_ty) => {
                if !fn_ty.generics.is_empty() {
                    panic!("Generic function types can not appear, only their instatiated counter parts.")
                }

                walk_list!(self, visit_ty, &fn_ty.param_tys);
                self.visit_ty(fn_ty.ret_ty.as_ref())
            }
            _ => visit::walk_ty(self, ty),
        }
    }

    fn visit_expr(&mut self, expr: &Expr) {
        match &expr.expr {
            ExprKind::ForNat(ident, collec, body) => {
                self.visit_nat(collec);
                let mut scoped_bound_idents = self.bound_idents.clone();
                scoped_bound_idents.extend(std::iter::once(IdentKinded::new(ident, Kind::Nat)));
                let mut inner_free_idents =
                    FreeKindedIdents::with_bound_idents(scoped_bound_idents);
                inner_free_idents.visit_expr(body);
                self.set.extend(inner_free_idents.set)
            }
            _ => visit::walk_expr(self, expr),
        }
    }
}

pub fn implicit_idents_without_rgns(f: &FunDef) -> Option<HashSet<Ident>> {
    struct ImplicitIdents(HashSet<Ident>);
    impl Visit for ImplicitIdents {
        fn visit_prv(&mut self, _prv: &Provenance) {
            // ignore
        }

        fn visit_ident(&mut self, ident: &Ident) {
            if ident.is_implicit {
                self.0.insert(ident.clone());
            }
        }
    }

    let mut impl_idents = ImplicitIdents(HashSet::new());
    impl_idents.visit_fun_def(f);
    if impl_idents.0.is_empty() {
        None
    } else {
        Some(impl_idents.0)
    }
}
