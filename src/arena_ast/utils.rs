use crate::arena_ast::visit::walk_list;
use crate::arena_ast::visit::Visit;
use crate::arena_ast::visit_mut::walk_list as walk_list_mut;
use crate::arena_ast::visit_mut::VisitMut;
use crate::arena_ast::{
    visit, visit_mut, ArgKinded, BaseExec, DataTy, DataTyKind, Dim, ExecExpr, ExecExprKind, ExecTy,
    Expr, ExprKind, FnTy, FunDef, Ident, IdentExec, IdentKinded, Kind, Memory, Nat, ParamSig,
    Provenance, Ty, TyKind,
};
use std::collections::{HashMap, HashSet};
use std::sync::atomic::{AtomicI32, Ordering};

static mut COUNTER: AtomicI32 = AtomicI32::new(0);

pub(crate) fn fresh_ident<'a, F, R>(arena: &'a bumpalo::Bump, name: &str, ident_constr: F) -> R
where
    F: Fn(Ident) -> R,
{
    ident_constr(Ident::new_impli(&arena, &fresh_name(name)))
}

pub(crate) fn fresh_name(name: &str) -> String {
    let prefix = format!("${}", name);
    let i;
    unsafe {
        i = COUNTER.fetch_add(1, Ordering::SeqCst);
    }
    format!("{}_{}", prefix, i)
}

pub fn implicit_idents<'a>(f: &FunDef<'a>) -> Option<HashSet<Ident<'a>>> {
    struct ImplicitIdents<'b>(HashSet<Ident<'b>>);
    impl<'b> Visit<'b> for ImplicitIdents<'b> {
        fn visit_ident(&mut self, ident: &Ident<'b>) {
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

// utils.rs (or wherever you define this trait)
pub trait VisitableMut<'a> {
    fn visit_mut<V: VisitMut<'a>>(&mut self, visitor: &mut V, arena: &'a bumpalo::Bump);
}

macro_rules! visitable_mut {
    ($t:ident, $f:ident) => {
        impl<'a> VisitableMut<'a> for $t<'a> {
            fn visit_mut<V: VisitMut<'a>>(&mut self, visitor: &mut V, arena: &'a bumpalo::Bump) {
                visitor.$f(arena, self);
            }
        }
    };
}

visitable_mut!(Ty, visit_ty);
visitable_mut!(Expr, visit_expr);
visitable_mut!(ExecExpr, visit_exec_expr);
visitable_mut!(IdentExec, visit_ident_exec);
visitable_mut!(ParamSig, visit_param_sig);
visitable_mut!(FnTy, visit_fn_ty);

/*
 * gen_idents: a list of generic identifiers to be substituted (this list can be longer than
 *  gen_args. In that case, only the first gen_args.len() many identifiers are substituted.
 * gen_args: the kinded expressions that are substituting the generic identifiers
 * t: the term to substitute in
 */
pub fn subst_idents_kinded<'a, I, J, T: VisitableMut<'a>>(
    arena: &'a bumpalo::Bump,
    gen_idents: I,
    gen_args: J,
    t: &mut T,
) where
    I: IntoIterator<Item = &'a IdentKinded<'a>>,
    J: IntoIterator<Item = &'a ArgKinded<'a>>,
{
    let subst_map: HashMap<&'a str, &'a ArgKinded<'a>> = gen_idents
        .into_iter()
        .map(|p| p.ident.name.as_ref())
        .zip(gen_args)
        .collect();

    let mut v = SubstIdentsKinded::new(&subst_map);
    t.visit_mut(&mut v, arena);
}

pub fn subst_ident_exec<'a, T: VisitableMut<'a>>(
    arena: &'a bumpalo::Bump,
    ident: &'a Ident<'a>,
    exec: &'a ExecExpr<'a>,
    t: &mut T,
) {
    let mut subst_ident_exec = SubstIdentExec::new(ident, exec);
    t.visit_mut(&mut subst_ident_exec, arena);
}

/*
 * substitute kinded arguments for free identifiers
 *
 * When substituting within a function definition or function type, the generic parameters are
 * bound. In order to substitute generic identifiers with their arguments, the relevant generic
 * identifiers must be removed from the list, first.
 */
struct SubstIdentsKinded<'a, 'm> {
    pub subst_map: &'m HashMap<&'a str, &'a ArgKinded<'a>>,
    pub bound_idents: HashSet<IdentKinded<'a>>,
}

impl<'a, 'm> SubstIdentsKinded<'a, 'm> {
    fn new(subst_map: &'m HashMap<&'a str, &'a ArgKinded<'a>>) -> Self {
        Self {
            subst_map,
            bound_idents: HashSet::new(),
        }
    }

    fn with_bound_idents(&self, bound_idents: HashSet<IdentKinded<'a>>) -> Self {
        Self {
            subst_map: self.subst_map,
            bound_idents,
        }
    }
}

impl<'a, 'm> VisitMut<'a> for SubstIdentsKinded<'a, 'm> {
    fn visit_nat(&mut self, arena: &'a bumpalo::Bump, nat: &mut Nat<'a>) {
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
            _ => visit_mut::walk_nat(self, arena, nat),
        }
    }

    fn visit_mem(&mut self, arena: &'a bumpalo::Bump, mem: &mut Memory<'a>) {
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
            _ => visit_mut::walk_mem(self, arena, mem),
        }
    }

    fn visit_prv(&mut self, arena: &'a bumpalo::Bump, prv: &mut Provenance<'a>) {
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
            _ => visit_mut::walk_prv(self, arena, prv),
        }
    }

    fn visit_dty(&mut self, arena: &'a bumpalo::Bump, dty: &mut DataTy<'a>) {
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
            _ => visit_mut::walk_dty(self, arena, dty),
        }
    }

    // add generic paramters to list of bound identifiers
    fn visit_fn_ty(&mut self, arena: &'a bumpalo::Bump, fn_ty: &mut FnTy<'a>) {
        let fun_bound_idents = fn_ty.generics.clone();
        let mut all_bound_idents = self.bound_idents.clone();
        all_bound_idents.extend(fun_bound_idents);
        let mut visitor_subst_generic_ident =
            SubstIdentsKinded::with_bound_idents(self, all_bound_idents);
        walk_list_mut!(
            &mut visitor_subst_generic_ident,
            visit_param_sig,
            &mut fn_ty.param_sigs.as_mut_slice(),
            arena
        );
        if let Some(ident_exec) = &mut fn_ty.generic_exec {
            let mut owned = (*ident_exec.ty).clone();
            self.visit_exec_ty(&mut owned);
            ident_exec.ty = arena.alloc(owned);
        }

        visitor_subst_generic_ident.visit_exec_expr(arena, &mut fn_ty.exec);
        let mut ret_owned = (*fn_ty.ret_ty).clone();
        self.visit_ty(arena, &mut ret_owned);
        fn_ty.ret_ty = arena.alloc(ret_owned);
    }

    // only required to introduce a new scope of bound identifiers
    fn visit_expr(&mut self, arena: &'a bumpalo::Bump, expr: &mut Expr<'a>) {
        match &mut expr.expr {
            ExprKind::ForNat(ident, collec, body) => {
                let mut range_owned = (**collec).clone();
                self.visit_nat_range(arena, &mut range_owned);
                *collec = arena.alloc(range_owned);
                let mut scoped_bound_idents = self.bound_idents.clone();
                scoped_bound_idents.extend(std::iter::once(IdentKinded::new(ident, Kind::Nat)));
                let mut subst_inner_kinded_idents =
                    SubstIdentsKinded::with_bound_idents(self, scoped_bound_idents);
                let mut body_owned = (**body).clone();
                subst_inner_kinded_idents.visit_expr(arena, &mut body_owned);
                *body = arena.alloc(body_owned);
            }
            _ => visit_mut::walk_expr(self, arena, expr),
        }
    }

    // add generic paramters to list of bound identifiers
    fn visit_fun_def(&mut self, arena: &'a bumpalo::Bump, fun_def: &mut FunDef<'a>) {
        let fun_bound_idents = fun_def.generic_params.clone();
        let mut all_bound_idents = self.bound_idents.clone();
        all_bound_idents.extend(fun_bound_idents);
        let mut subst_fun_free_kind_idents =
            SubstIdentsKinded::with_bound_idents(self, all_bound_idents);
        walk_list_mut!(
            &mut subst_fun_free_kind_idents,
            visit_param_decl,
            &mut fun_def.param_decls.as_mut_slice(),
            arena
        );
        let mut ret_owned = (*fun_def.ret_dty).clone();
        self.visit_dty(arena, &mut ret_owned);
        fun_def.ret_dty = arena.alloc(ret_owned);
        for ident_exec in &mut fun_def.generic_exec {
            subst_fun_free_kind_idents.visit_ident_exec(arena, ident_exec);
        }
        subst_fun_free_kind_idents.visit_exec_expr(arena, &mut fun_def.exec);
        walk_list_mut!(
            subst_fun_free_kind_idents,
            visit_prv_rel,
            &mut fun_def.prv_rels.as_mut_slice(),
            arena
        );
        let mut body_owned = (*fun_def.body).clone();
        self.visit_block(arena, &mut body_owned);
        fun_def.body = arena.alloc(body_owned);
    }
}

/*
 * Substitue a generic exec identifier with specific exec.
 * This substitution ignores whehter an execution identifier is bound by a function type.
 */
struct SubstIdentExec<'a> {
    pub ident: &'a Ident<'a>,
    pub exec: &'a ExecExpr<'a>,
}

impl<'a> SubstIdentExec<'a> {
    fn new(ident: &'a Ident<'a>, exec: &'a ExecExpr<'a>) -> Self {
        SubstIdentExec { ident, exec }
    }
}

impl<'a> VisitMut<'a> for SubstIdentExec<'a> {
    fn visit_exec_expr(&mut self, arena: &'a bumpalo::Bump, exec_expr: &mut ExecExpr<'a>) {
        insert_for_ident(arena, self.exec, self.ident, exec_expr)
    }
}

fn insert_for_ident<'a>(
    bump: &'a bumpalo::Bump,
    exec: &ExecExpr<'a>,
    ident: &Ident<'a>,
    in_exec: &mut ExecExpr<'a>,
) {
    if let BaseExec::Ident(i) = &in_exec.exec.base {
        if i == ident {
            // Build merged path in this arena
            let mut merged = bumpalo::collections::Vec::new_in(bump);
            merged.extend(exec.exec.path.iter().cloned());
            merged.extend(in_exec.exec.path.iter().cloned());

            // New exec node allocated in arena
            let new_kind = bump.alloc(ExecExprKind {
                base: exec.exec.base.clone(),
                path: merged,
            });

            // Keep or drop the cached type (choose one)
            // let new_ty = in_exec.ty;         // keep it (may be stale)
            let new_ty = None; // safer: force re-tycheck later

            *in_exec = ExecExpr {
                exec: new_kind,
                ty: new_ty,
                span: in_exec.span,
            };
        }
    }
}

pub trait Visitable<'a> {
    fn visit<V: Visit<'a>>(&self, visitor: &mut V);
}
macro_rules! visitable {
    ($t:ident, $f:ident) => {
        impl<'a> Visitable<'a> for $t<'a> {
            fn visit<V: Visit<'a>>(&self, visitor: &mut V) {
                visitor.$f(self);
            }
        }
    };
}
visitable!(Ty, visit_ty);
visitable!(FnTy, visit_fn_ty);
visitable!(ParamSig, visit_param_sig);
visitable!(DataTy, visit_dty);
visitable!(Memory, visit_mem);
visitable!(Provenance, visit_prv);
visitable!(ExecExpr, visit_exec_expr);
visitable!(ExecTy, visit_exec_ty);
visitable!(Dim, visit_dim);
visitable!(Expr, visit_expr);
visitable!(Nat, visit_nat);

pub fn free_kinded_idents<'a, T: Visitable<'a>>(t: &T) -> HashSet<IdentKinded<'a>> {
    let mut free_kinded_idents = FreeKindedIdents::new();
    t.visit(&mut free_kinded_idents);
    free_kinded_idents.set
}

pub struct FreeKindedIdents<'a> {
    pub set: HashSet<IdentKinded<'a>>,
    pub bound_idents: HashSet<IdentKinded<'a>>,
}

impl<'a> FreeKindedIdents<'a> {
    fn new() -> Self {
        FreeKindedIdents {
            set: HashSet::new(),
            bound_idents: HashSet::new(),
        }
    }

    fn with_bound_idents(idents: HashSet<IdentKinded<'a>>) -> Self {
        FreeKindedIdents {
            set: HashSet::new(),
            bound_idents: idents,
        }
    }
}

impl<'a> Visit<'a> for FreeKindedIdents<'a> {
    fn visit_nat(&mut self, nat: &Nat<'a>) {
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

    fn visit_mem(&mut self, mem: &Memory<'a>) {
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

    fn visit_prv(&mut self, prv: &Provenance<'a>) {
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

    fn visit_dty(&mut self, dty: &DataTy<'a>) {
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

    fn visit_ty(&mut self, ty: &Ty<'a>) {
        match &ty.ty {
            TyKind::FnTy(fn_ty) => {
                if !fn_ty.generics.is_empty() {
                    panic!(
                        "Generic function types can not appear,\
                        only their instatiated counter parts."
                    )
                }

                walk_list!(self, visit_param_sig, &fn_ty.param_sigs);
                self.visit_ty(fn_ty.ret_ty)
            }
            _ => visit::walk_ty(self, ty),
        }
    }

    fn visit_expr(&mut self, expr: &Expr<'a>) {
        match &expr.expr {
            ExprKind::ForNat(ident, collec, body) => {
                self.visit_nat_range(collec);
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
