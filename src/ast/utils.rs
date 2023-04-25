use crate::ast::visit::walk_list;
use crate::ast::visit::Visit;
use crate::ast::visit_mut::VisitMut;
use crate::ast::{
    visit, visit_mut, ArgKinded, DataTy, DataTyKind, Dim, ExecTy, Expr, ExprKind, FnTy, FunDef,
    Ident, IdentKinded, Kind, Memory, Nat, Provenance, Ty, TyKind,
};
use std::collections::{HashMap, HashSet};
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

pub fn implicit_idents(f: &FunDef) -> Option<HashSet<Ident>> {
    struct ImplicitIdents(HashSet<Ident>);
    impl Visit for ImplicitIdents {
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

pub trait VisitableMut {
    fn visit_mut<V: VisitMut>(&mut self, visitor: &mut V);
}
macro_rules! visitable_mut {
    ($t:ident, $f:ident) => {
        impl VisitableMut for $t {
            fn visit_mut<V: VisitMut>(&mut self, visitor: &mut V) {
                visitor.$f(self);
            }
        }
    };
}
visitable_mut!(Ty, visit_ty);
visitable_mut!(Expr, visit_expr);
visitable_mut!(ExecTy, visit_exec_ty);

pub fn subst_idents_kinded<'a, I, J, T: VisitableMut>(gen_params: I, k_args: J, t: &mut T)
where
    I: IntoIterator<Item = &'a IdentKinded>,
    J: IntoIterator<Item = &'a ArgKinded>,
{
    let subst_map = HashMap::from_iter(
        gen_params
            .into_iter()
            .map(|p| p.ident.name.as_ref())
            .zip(k_args),
    );
    let mut subst_idents_kinded = SubstIdentsKinded::new(&subst_map);
    t.visit_mut(&mut subst_idents_kinded);
}

struct SubstIdentsKinded<'a> {
    pub subst_map: &'a HashMap<&'a str, &'a ArgKinded>,
    pub bound_idents: HashSet<IdentKinded>,
}

impl<'a> SubstIdentsKinded<'a> {
    fn new(subst_map: &'a HashMap<&'a str, &'a ArgKinded>) -> Self {
        SubstIdentsKinded {
            subst_map,
            bound_idents: HashSet::new(),
        }
    }

    fn with_bound_idents(
        subst_map: &'a HashMap<&'a str, &'a ArgKinded>,
        bound_idents: HashSet<IdentKinded>,
    ) -> Self {
        SubstIdentsKinded {
            subst_map,
            bound_idents,
        }
    }
}

impl VisitMut for SubstIdentsKinded<'_> {
    fn visit_nat(&mut self, nat: &mut Nat) {
        match nat {
            Nat::Ident(ident) => {
                let ident_kinded = IdentKinded::new(ident, Kind::Nat);
                if !self.bound_idents.contains(&ident_kinded) {
                    if let Some(ArgKinded::Nat(nat_arg)) =
                        self.subst_map.get::<str>(ident.name.as_ref())
                    {
                        *nat = nat_arg.clone()
                    }
                }
            }
            _ => visit_mut::walk_nat(self, nat),
        }
    }

    fn visit_mem(&mut self, mem: &mut Memory) {
        match mem {
            Memory::Ident(ident) => {
                let ident_kinded = IdentKinded::new(ident, Kind::Memory);
                if !self.bound_idents.contains(&ident_kinded) {
                    if let Some(ArgKinded::Memory(mem_arg)) =
                        self.subst_map.get::<str>(ident.name.as_ref())
                    {
                        *mem = mem_arg.clone()
                    }
                }
            }
            _ => visit_mut::walk_mem(self, mem),
        }
    }

    fn visit_prv(&mut self, prv: &mut Provenance) {
        match prv {
            Provenance::Ident(ident) => {
                let ident_kinded = IdentKinded::new(ident, Kind::Provenance);
                if !self.bound_idents.contains(&ident_kinded) {
                    if let Some(ArgKinded::Provenance(prv_arg)) =
                        self.subst_map.get::<str>(ident.name.as_ref())
                    {
                        *prv = prv_arg.clone()
                    }
                }
            }
            _ => visit_mut::walk_prv(self, prv),
        }
    }

    fn visit_dty(&mut self, dty: &mut DataTy) {
        match &mut dty.dty {
            DataTyKind::Ident(ident) => {
                let ident_kinded = IdentKinded::new(ident, Kind::DataTy);
                if !self.bound_idents.contains(&ident_kinded) {
                    if let Some(ArgKinded::DataTy(dty_arg)) =
                        self.subst_map.get::<str>(ident.name.as_ref())
                    {
                        *dty = dty_arg.clone()
                    }
                }
            }
            _ => visit_mut::walk_dty(self, dty),
        }
    }

    fn visit_expr(&mut self, expr: &mut Expr) {
        match &mut expr.expr {
            ExprKind::ForNat(ident, collec, body) => {
                self.visit_nat(collec);
                let mut scoped_bound_idents = self.bound_idents.clone();
                scoped_bound_idents.extend(std::iter::once(IdentKinded::new(ident, Kind::Nat)));
                let mut subst_inner_kinded_idents =
                    SubstIdentsKinded::with_bound_idents(self.subst_map, scoped_bound_idents);
                subst_inner_kinded_idents.visit_expr(body);
            }
            _ => visit_mut::walk_expr(self, expr),
        }
    }

    fn visit_fun_def(&mut self, fun_def: &mut FunDef) {
        let fun_bound_idents = fun_def.generic_params.clone();
        let mut all_bound_idents = self.bound_idents.clone();
        all_bound_idents.extend(fun_bound_idents);
        let mut subst_fun_free_kind_idents =
            SubstIdentsKinded::with_bound_idents(self.subst_map, all_bound_idents);
        walk_list!(
            &mut subst_fun_free_kind_idents,
            visit_param_decl,
            &mut fun_def.param_decls
        );
        subst_fun_free_kind_idents.visit_dty(&mut fun_def.ret_dty);
        subst_fun_free_kind_idents.visit_ident_exec(&mut fun_def.exec_decl);
        walk_list!(
            subst_fun_free_kind_idents,
            visit_prv_rel,
            &mut fun_def.prv_rels
        );
        subst_fun_free_kind_idents.visit_block(&mut fun_def.body)
    }
}

pub trait Visitable {
    fn visit<V: Visit>(&self, visitor: &mut V);
}
macro_rules! visitable {
    ($t:ident, $f:ident) => {
        impl Visitable for $t {
            fn visit<V: Visit>(&self, visitor: &mut V) {
                visitor.$f(self);
            }
        }
    };
}
visitable!(Ty, visit_ty);
visitable!(FnTy, visit_fn_ty);
visitable!(DataTy, visit_dty);
visitable!(Memory, visit_mem);
visitable!(Provenance, visit_prv);
visitable!(ExecTy, visit_exec_ty);
visitable!(Dim, visit_dim);
visitable!(Expr, visit_expr);
visitable!(Nat, visit_nat);

pub fn free_kinded_idents<T: Visitable>(t: &T) -> HashSet<IdentKinded> {
    let mut free_kinded_idents = FreeKindedIdents::new();
    t.visit(&mut free_kinded_idents);
    free_kinded_idents.set
}

pub struct FreeKindedIdents {
    pub set: HashSet<IdentKinded>,
    pub bound_idents: HashSet<IdentKinded>,
}

impl FreeKindedIdents {
    fn new() -> Self {
        FreeKindedIdents {
            set: HashSet::new(),
            bound_idents: HashSet::new(),
        }
    }

    fn with_bound_idents(idents: HashSet<IdentKinded>) -> Self {
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
                    panic!(
                        "Generic function types can not appear,\
                        only their instatiated counter parts."
                    )
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
