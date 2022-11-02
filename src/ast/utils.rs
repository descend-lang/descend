use crate::ast::visit::Visit;
use crate::ast::{
    visit, DataTy, DataTyKind, Expr, ExprKind, Ident, IdentKinded, Kind, Memory, Nat, Provenance,
    Ty, TyKind,
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
                    self.set
                        .extend(std::iter::once(IdentKinded::new(ident, Kind::Nat)))
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
                    self.set
                        .extend(std::iter::once(IdentKinded::new(ident, Kind::Memory)))
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
                    self.set
                        .extend(std::iter::once(IdentKinded::new(ident, Kind::Provenance)))
                }
            }
            _ => visit::walk_prv(self, prv),
        }
    }

    fn visit_ty(&mut self, ty: &Ty) {
        match &ty.ty {
            TyKind::Ident(ident) => {
                let ident_kinded = IdentKinded::new(ident, Kind::Ty);
                if !self.bound_idents.contains(&ident_kinded) {
                    self.set
                        .extend(std::iter::once(IdentKinded::new(ident, Kind::Ty)))
                }
            }
            _ => visit::walk_ty(self, ty),
        }
    }

    fn visit_dty(&mut self, dty: &DataTy) {
        match &dty.dty {
            DataTyKind::Ident(ident) => {
                self.set.insert(IdentKinded::new(ident, Kind::DataTy));
            }
            _ => visit::walk_dty(self, dty),
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

    //Visiting this items is not supported because this items can bound identifiers.
    //This would require corresponding checks in "visit_dty" etc.
    fn visit_item_def(&mut self, _: &super::Item) {
        unimplemented!()
    }
    fn visit_trait_def(&mut self, _: &super::TraitDef) {
        unimplemented!()
    }
    fn visit_struct_decl(&mut self, _: &super::StructDecl) {
        unimplemented!()
    }
    fn visit_impl_def(&mut self, _: &super::ImplDef) {
        unimplemented!()
    }
    fn visit_fun_def(&mut self, _: &super::FunDef) {
        unimplemented!()
    }
}
