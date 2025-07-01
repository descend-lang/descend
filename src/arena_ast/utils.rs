use crate::arena_ast::visit::walk_list;
use crate::arena_ast::visit::Visit;
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

pub trait VisitableMut<'a> {
    fn visit_mut<V: VisitMut<'a>>(&mut self, visitor: &mut V);
}
macro_rules! visitable_mut {
    ($t:ident, $f:ident) => {
        impl<'a> VisitableMut<'a> for $t<'a> {
            fn visit_mut<V: VisitMut<'a>>(&mut self, visitor: &mut V) {
                visitor.$f(self);
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
pub fn subst_idents_kinded<'a, I, J, T: VisitableMut<'a>>(gen_idents: I, gen_args: J, t: &mut T)
where
    I: IntoIterator<Item = &'a IdentKinded<'a>>,
    J: IntoIterator<Item = &'a ArgKinded<'a>>,
{
    let subst_map = HashMap::from_iter(
        gen_idents
            .into_iter()
            .map(|p| p.ident.name.as_ref())
            .zip(gen_args),
    );
    let mut subst_idents_kinded = SubstIdentsKinded::new(subst_map);
    t.visit_mut(&mut subst_idents_kinded);
}

pub fn subst_ident_exec<'a, T: VisitableMut<'a>>(
    ident: &'a Ident<'a>,
    exec: &'a ExecExpr<'a>,
    t: &mut T,
) {
    let mut subst_ident_exec = SubstIdentExec::new(ident, exec);
    t.visit_mut(&mut subst_ident_exec);
}
/*
 * substitute kinded arguments for free identifiers
 *
 * When substituting within a function definition or function type, the generic parameters are
 * bound. In order to substitute generic identifiers with their arguments, the relevant generic
 * identifiers must be removed from the list, first.
 */
struct SubstIdentsKinded<'a> {
    pub subst_map: HashMap<&'a str, &'a ArgKinded<'a>>,
    pub bound_idents: HashSet<IdentKinded<'a>>,
}

impl<'a> SubstIdentsKinded<'a> {
    fn new(subst_map: HashMap<&'a str, &'a ArgKinded<'a>>) -> Self {
        SubstIdentsKinded {
            subst_map,
            bound_idents: HashSet::new(),
        }
    }

    fn with_bound_idents(
        subst_map: HashMap<&'a str, &'a ArgKinded<'a>>,
        bound_idents: HashSet<IdentKinded<'a>>,
    ) -> Self {
        SubstIdentsKinded {
            subst_map,
            bound_idents,
        }
    }
}

impl<'a> VisitMut<'a> for SubstIdentsKinded<'a> {
    fn visit_nat(&mut self, nat: &mut Nat<'a>) {
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

    fn visit_mem(&mut self, mem: &mut Memory<'a>) {
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

    fn visit_prv(&mut self, prv: &mut Provenance<'a>) {
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

    fn visit_dty(&mut self, dty: &mut DataTy<'a>) {
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

    // add generic paramters to list of bound identifiers
    fn visit_fn_ty(&mut self, fn_ty: &mut FnTy<'a>) {
        let fun_bound_idents = fn_ty.generics.clone();
        let mut all_bound_idents = self.bound_idents.clone();
        all_bound_idents.extend(fun_bound_idents);
        let mut visitor_subst_generic_ident =
            SubstIdentsKinded::with_bound_idents(self.subst_map, all_bound_idents);
        walk_list!(
            &mut visitor_subst_generic_ident,
            visit_param_sig,
            &mut fn_ty.param_sigs
        );
        for ident_exec in &mut fn_ty.generic_exec {
            visitor_subst_generic_ident.visit_exec_ty(&mut ident_exec.ty);
        }
        visitor_subst_generic_ident.visit_exec_expr(&mut fn_ty.exec);
        visitor_subst_generic_ident.visit_ty(&mut fn_ty.ret_ty);
    }

    // only required to introduce a new scope of bound identifiers
    fn visit_expr(&mut self, expr: &mut Expr<'a>) {
        match &mut expr.expr {
            ExprKind::ForNat(ident, collec, body) => {
                self.visit_nat_range(collec);
                let mut scoped_bound_idents = self.bound_idents.clone();
                scoped_bound_idents.extend(std::iter::once(IdentKinded::new(ident, Kind::Nat)));
                let mut subst_inner_kinded_idents =
                    SubstIdentsKinded::with_bound_idents(self.subst_map, scoped_bound_idents);
                subst_inner_kinded_idents.visit_expr(body);
            }
            _ => visit_mut::walk_expr(self, expr),
        }
    }

    // add generic paramters to list of bound identifiers
    fn visit_fun_def(&mut self, fun_def: &mut FunDef<'a>) {
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
        for ident_exec in &mut fun_def.generic_exec {
            subst_fun_free_kind_idents.visit_ident_exec(ident_exec);
        }
        subst_fun_free_kind_idents.visit_exec_expr(&mut fun_def.exec);
        walk_list!(
            subst_fun_free_kind_idents,
            visit_prv_rel,
            &mut fun_def.prv_rels
        );
        subst_fun_free_kind_idents.visit_block(&mut fun_def.body)
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
    fn visit_exec_expr(&mut self, bump: &'a bumpalo::Bump, exec_expr: &mut ExecExpr<'a>) {
        insert_for_ident(bump, self.exec, &self.ident, exec_expr)
    }
}

/**
fn insert_for_ident<'a>(exec: &ExecExpr<'a>, ident: &Ident<'a>, in_exec: &mut ExecExpr<'a>) {
    if let BaseExec::Ident(i) = &mut in_exec.exec.base {
        if i == ident {
            let mut subst_exec = exec.clone();
            subst_exec.exec.path.extend(in_exec.exec.path.clone());
            *in_exec = subst_exec;
        }
    }
}
*/

fn insert_for_ident<'a>(
    bump: &'a bumpalo::Bump,
    exec: &ExecExpr<'a>,
    ident: &Ident<'a>,
    in_exec: &mut ExecExpr<'a>,
) {
    if let BaseExec::Ident(i) = &in_exec.exec.base {
        if i == ident {
            let mut merged_path = exec.exec.path.clone();
            merged_path.extend(in_exec.exec.path.iter().cloned());

            let new_exec = bump.alloc(ExecExprKind {
                base: exec.exec.base.clone(),
                path: merged_path,
            });

            let new_exec_expr = ExecExpr {
                exec: new_exec,
                ty: in_exec.ty,
                span: in_exec.span,
            };

            *in_exec = new_exec_expr;
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
