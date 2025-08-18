use crate::arena_ast::*;

#[rustfmt::skip]
pub trait VisitMut<'a>: Sized {
    fn visit_binary_op_nat(&mut self, _op: &mut BinOpNat) {}
    fn visit_nat(&mut self, arena: &'a Bump, n: &mut Nat<'a>) { walk_nat(self, arena, n) }
    fn visit_nat_ref(&mut self, arena: &'a Bump, slot: &mut &'a Nat<'a>) {
        walk_nat_ref(self, arena, slot)
    }
    fn visit_nat_range(&mut self, arena: &'a Bump, nr: &mut NatRange<'a>) { walk_nat_range(self, arena, nr) }
    fn visit_ident_kinded(&mut self, arena: &'a Bump, id_kind: &mut IdentKinded<'a>) { walk_ident_kinded(self, arena, id_kind) }
    fn visit_ident_exec(&mut self, arena: &'a Bump, id_exec: &mut IdentExec<'a>) { walk_ident_exec(self, arena, id_exec) }
    fn visit_prv_rel(&mut self, arena: &'a Bump, prv_rel: &mut PrvRel<'a>) { walk_prv_rel(self, arena, prv_rel) }
    fn visit_exec_ty(&mut self, _exec: &mut ExecTy<'a>) {}
    fn visit_exec_ty_ref(&mut self, _arena: &'a bumpalo::Bump, _slot: &mut &'a ExecTy<'a>) {}
    fn visit_mem(&mut self, arena: &'a Bump, mem: &mut Memory<'a>) { walk_mem(self, arena, mem) }
    fn visit_prv(&mut self, arena: &'a Bump, prv: &mut Provenance<'a>) { walk_prv(self, arena, prv) }
    fn visit_scalar_ty(&mut self, _sty: &mut ScalarTy) {}
    fn visit_atomic_ty(&mut self, _aty: &mut AtomicTy) {}
    fn visit_dim_compo(&mut self, _dim_compo: &mut DimCompo) {}
    fn visit_dim(&mut self, arena: &'a Bump, dim: &mut Dim<'a>) { walk_dim(self, arena, dim) }
    fn visit_dim3d(&mut self, arena: &'a Bump, dim3d: &mut Dim3d<'a>) { walk_dim3d(self, arena, dim3d) }
    fn visit_dim2d(&mut self, arena: &'a Bump, dim2d: &mut Dim2d<'a>) { walk_dim2d(self, arena, dim2d) }
    fn visit_dim1d(&mut self, arena: &'a Bump, dim1d: &mut Dim1d<'a>) { walk_dim1d(self, arena, dim1d) }
    fn visit_ref(&mut self, arena: &'a Bump, reff: &mut RefDty<'a>) { walk_ref(self, arena, reff) }
    fn visit_dty(&mut self, arena: &'a Bump, dty: &mut DataTy<'a>) { walk_dty(self, arena, dty) }
    fn visit_fn_ty(&mut self, arena: &'a Bump, fn_ty: &mut FnTy<'a>) { walk_fn_ty(self, arena, fn_ty) }
    fn visit_nat_constr(&mut self, arena: &'a Bump, nat_constr: &mut NatConstr<'a>) { walk_nat_constr(self, arena, nat_constr) }
    fn visit_ty(&mut self, arena: &'a Bump, ty: &mut Ty<'a>) { walk_ty(self, arena, ty) }
    fn visit_view(&mut self, arena: &'a Bump, view: &mut View<'a>) { walk_view(self, arena, view) }
    fn visit_pl_expr(&mut self, arena: &'a Bump, pl_expr: &mut PlaceExpr<'a>) { walk_pl_expr(self, arena, pl_expr) }
    fn visit_arg_kinded(&mut self, arena: &'a Bump, arg_kinded: &mut ArgKinded<'a>) { walk_arg_kinded(self, arena, arg_kinded) }
    fn visit_kind(&mut self, _kind: &mut Kind) {}
    fn visit_binary_op(&mut self, _op: &mut BinOp) {}
    fn visit_unary_op(&mut self, _op: &mut UnOp) {}
    fn visit_own(&mut self, _own: &mut Ownership) {}
    fn visit_mutability(&mut self, _mutbl: &mut Mutability) {}
    fn visit_lit(&mut self, _lit: &mut Lit) {}
    fn visit_ident(&mut self, arena: &'a Bump, _ident: &mut Ident<'a>) {}
    fn visit_pattern(&mut self, arena: &'a Bump, pattern: &mut Pattern<'a>) { walk_pattern(self, arena, pattern) }
    fn visit_split(&mut self, arena: &'a Bump, split: &mut Split<'a>) { walk_split(self, arena, split) }
    fn visit_sched(&mut self, arena: &'a Bump, sched: &mut Sched<'a>) { walk_sched(self, arena, sched) }
    fn visit_expr(&mut self, arena: &'a Bump, expr: &mut Expr<'a>) { walk_expr(self, arena, expr) }
    fn visit_app_kernel(&mut self, arena: &'a Bump, app_kernel: &mut AppKernel<'a>) { walk_app_kernel(self, arena, app_kernel) }
    fn visit_block(&mut self, arena: &'a Bump, block: &mut Block<'a>) { walk_block(self, arena, block) }
    fn visit_split_proj(&mut self,arena: &'a Bump, exec_split: &mut TakeRange<'a>) { walk_split_proj(self, arena, exec_split) }
    fn visit_exec_expr(&mut self, arena: &'a Bump, exec_expr: &mut ExecExpr<'a>) { walk_exec_expr(self, arena, exec_expr) }
    fn visit_exec(&mut self, arena: &'a Bump, exec: &mut ExecExprKind<'a>) { walk_exec(self, arena, exec) }
    fn visit_exec_path_elem(&mut self, arena: &'a Bump, exec_path_elem: &mut ExecPathElem<'a>) { walk_exec_path_elem(self,  arena, exec_path_elem) }
    fn visit_param_decl(&mut self, arena: &'a Bump, param_decl: &mut ParamDecl<'a>) { walk_param_decl(self, arena, param_decl) }
    fn visit_fun_def(&mut self, arena: &'a Bump, fun_def: &mut FunDef<'a>) { walk_fun_def(self, arena, fun_def) }
    fn visit_fun_decl(&mut self, arena: &'a Bump, fun_decl: &mut FunDecl<'a>) { walk_fun_decl(self, arena, fun_decl) }
    fn visit_param_sig(&mut self, arena: &'a Bump, param_sig: &mut ParamSig<'a>) { walk_param_sig(self, arena, param_sig) }
    fn visit_field(&mut self, arena: &'a Bump, field: &mut (Ident<'a>, DataTy<'a>)) { walk_field(self, arena, field) }
}

// Taken from the Rust compiler
macro_rules! walk_list {
    ($visitor:expr, $method:ident, $list:expr, $arena:expr) => {
        for elem in $list.iter_mut() {
            $visitor.$method($arena, elem)
        }
    };
}
pub(crate) use walk_list;

pub fn walk_nat<'a, V: VisitMut<'a>>(visitor: &mut V, arena: &'a Bump, n: &mut Nat<'a>) {
    match n {
        Nat::Ident(ident) => visitor.visit_ident(arena, ident),
        Nat::BinOp(op, ref mut l, ref mut r) => {
            visitor.visit_binary_op_nat(op);
            visitor.visit_nat_ref(arena, l);
            visitor.visit_nat_ref(arena, r);
        }
        Nat::GridIdx
        | Nat::BlockIdx(_)
        | Nat::BlockDim(_)
        | Nat::ThreadIdx(_)
        | Nat::WarpGrpIdx
        | Nat::WarpIdx
        | Nat::LaneIdx
        | Nat::Lit(_) => {}
        Nat::App(func, args) => {
            visitor.visit_ident(arena, func);
            walk_list!(visitor, visit_nat, args.as_mut_slice(), arena)
        }
    }
}

pub fn walk_nat_ref<'a, V: VisitMut<'a>>(
    v: &mut V,
    arena: &'a bumpalo::Bump,
    slot: &mut &'a Nat<'a>,
) {
    match &*(*slot) {
        Nat::BinOp(op, l, r) => {
            let mut l_slot: &'a Nat<'a> = *l;
            let mut r_slot: &'a Nat<'a> = *r;

            v.visit_nat_ref(arena, &mut l_slot);
            v.visit_nat_ref(arena, &mut r_slot);

            let new = arena.alloc(Nat::BinOp(*op, l_slot, r_slot));
            *slot = new;
        }
        Nat::App(func, args) => {
            let mut rebuilt = bumpalo::collections::Vec::new_in(arena);
            rebuilt.reserve(args.len());
            for a in args.iter() {
                let mut owned = a.clone();
                v.visit_nat(arena, &mut owned);
                rebuilt.push(owned);
            }
            *slot = arena.alloc(Nat::App(func.clone(), rebuilt));
        }
        _ => {}
    }
}

pub fn walk_nat_range<'a, V: VisitMut<'a>>(
    visitor: &mut V,
    arena: &'a Bump,
    nr: &mut NatRange<'a>,
) {
    match nr {
        NatRange::Simple { lower, upper } => {
            visitor.visit_nat(arena, lower);
            visitor.visit_nat(arena, upper);
        }
        NatRange::Halved { upper } | NatRange::Doubled { upper } => visitor.visit_nat(arena, upper),
    }
}

pub fn walk_ident_kinded<'a, V: VisitMut<'a>>(
    visitor: &mut V,
    arena: &'a Bump,
    id_kind: &mut IdentKinded<'a>,
) {
    let IdentKinded { ident, kind } = id_kind;
    visitor.visit_ident(arena, ident);
    visitor.visit_kind(kind)
}

pub fn walk_ident_exec<'a, V: VisitMut<'a>>(
    visitor: &mut V,
    arena: &'a Bump,
    id_exec: &mut IdentExec<'a>,
) {
    let IdentExec { ident, ty } = id_exec;
    visitor.visit_ident(arena, ident);
    visitor.visit_exec_ty_ref(arena, ty)
}

pub fn walk_prv_rel<'a, V: VisitMut<'a>>(
    visitor: &mut V,
    arena: &'a Bump,
    prv_rel: &mut PrvRel<'a>,
) {
    let PrvRel { longer, shorter } = prv_rel;
    visitor.visit_ident(arena, longer);
    visitor.visit_ident(arena, shorter)
}

pub fn walk_mem<'a, V: VisitMut<'a>>(visitor: &mut V, arena: &'a Bump, mem: &mut Memory<'a>) {
    if let Memory::Ident(ident) = mem {
        visitor.visit_ident(arena, ident)
    }
}

pub fn walk_prv<'a, V: VisitMut<'a>>(visitor: &mut V, arena: &'a Bump, prv: &mut Provenance<'a>) {
    match prv {
        Provenance::Ident(ident) => visitor.visit_ident(arena, ident),
        Provenance::Value(_) => {}
    }
}

pub fn walk_dim3d<'a, V: VisitMut<'a>>(visitor: &mut V, arena: &'a Bump, dim3d: &mut Dim3d<'a>) {
    let Dim3d(n1, n2, n3) = dim3d;
    visitor.visit_nat(arena, n1);
    visitor.visit_nat(arena, n2);
    visitor.visit_nat(arena, n3);
}

pub fn walk_dim2d<'a, V: VisitMut<'a>>(visitor: &mut V, arena: &'a Bump, dim2d: &mut Dim2d<'a>) {
    let Dim2d(n1, n2) = dim2d;
    visitor.visit_nat(arena, n1);
    visitor.visit_nat(arena, n2);
}

pub fn walk_dim1d<'a, V: VisitMut<'a>>(visitor: &mut V, arena: &'a Bump, dim1d: &mut Dim1d<'a>) {
    let Dim1d(n) = dim1d;
    visitor.visit_nat(arena, n);
}

/**
pub fn walk_dim<'a, V: VisitMut<'a>>(visitor: &mut V, arena: &'a Bump, dim: &mut Dim<'a>) {
    match dim {
        Dim::XYZ(dim3d) => {
            visitor.visit_dim3d(arena, dim3d);
        }
        Dim::XY(dim2d) | Dim::XZ(dim2d) | Dim::YZ(dim2d) => {
            visitor.visit_dim2d(arena, dim2d);
        }
        Dim::X(dim1d) | Dim::Y(dim1d) | Dim::Z(dim1d) => visitor.visit_dim1d(arena, dim1d),
    }
}*/

pub fn walk_dim<'a, V: VisitMut<'a>>(v: &mut V, arena: &'a bumpalo::Bump, dim: &mut Dim<'a>) {
    let new_dim = match dim {
        Dim::XYZ(d3_ref) => {
            let mut d3 = (*(*d3_ref)).clone(); // owned, mutable
            v.visit_dim3d(arena, &mut d3);
            Dim::new_3d(arena, d3.0.clone(), d3.1.clone(), d3.2.clone())
        }
        Dim::XY(d2_ref) => {
            let mut d2 = (*(*d2_ref)).clone();
            v.visit_dim2d(arena, &mut d2);
            Dim::new_2d(arena, Dim::XY, d2.0.clone(), d2.1.clone())
        }
        Dim::XZ(d2_ref) => {
            let mut d2 = (*(*d2_ref)).clone();
            v.visit_dim2d(arena, &mut d2);
            Dim::new_2d(arena, Dim::XZ, d2.0.clone(), d2.1.clone())
        }
        Dim::YZ(d2_ref) => {
            let mut d2 = (*(*d2_ref)).clone();
            v.visit_dim2d(arena, &mut d2);
            Dim::new_2d(arena, Dim::YZ, d2.0.clone(), d2.1.clone())
        }
        Dim::X(d1_ref) => {
            let mut d1 = (*(*d1_ref)).clone();
            v.visit_dim1d(arena, &mut d1);
            Dim::new_1d(arena, Dim::X, d1.0.clone())
        }
        Dim::Y(d1_ref) => {
            let mut d1 = (*(*d1_ref)).clone();
            v.visit_dim1d(arena, &mut d1);
            Dim::new_1d(arena, Dim::Y, d1.0.clone())
        }
        Dim::Z(d1_ref) => {
            let mut d1 = (*(*d1_ref)).clone();
            v.visit_dim1d(arena, &mut d1);
            Dim::new_1d(arena, Dim::Z, d1.0.clone())
        }
    };
    *dim = new_dim;
}

pub fn walk_ref<'a, V: VisitMut<'a>>(visitor: &mut V, arena: &'a Bump, reff: &mut RefDty<'a>) {
    let RefDty { rgn, own, mem, dty } = reff;
    visitor.visit_prv(arena, rgn);
    visitor.visit_own(own);
    visitor.visit_mem(arena, mem);

    let mut owned = (*reff.dty).clone();
    visitor.visit_dty(arena, &mut owned);
    reff.dty = arena.alloc(owned);
}

pub fn walk_dty<'a, V: VisitMut<'a>>(visitor: &mut V, arena: &'a Bump, dty: &mut DataTy<'a>) {
    match &mut dty.dty {
        DataTyKind::Ident(ident) => visitor.visit_ident(arena, ident),
        DataTyKind::Scalar(sty) => visitor.visit_scalar_ty(sty),
        DataTyKind::Atomic(aty) => visitor.visit_atomic_ty(aty),
        DataTyKind::Tuple(elem_dtys) => walk_list!(visitor, visit_dty, elem_dtys, arena),
        DataTyKind::Struct(struct_decl_ref) => {
            let mut owned = (**struct_decl_ref).clone();
            visitor.visit_ident(arena, &mut owned.ident);
            walk_list!(visitor, visit_field, &mut owned.fields, arena);
            *struct_decl_ref = arena.alloc(owned);
        }
        DataTyKind::Array(dty_ref, n_ref) => {
            let mut elem = (**dty_ref).clone();
            visitor.visit_dty(arena, &mut elem);
            *dty_ref = arena.alloc(elem);

            let mut n = (*n_ref).clone();
            visitor.visit_nat(arena, &mut n);
            *n_ref = n;
        }
        DataTyKind::ArrayShape(dty_ref, n_ref) => {
            let mut elem = (**dty_ref).clone();
            visitor.visit_dty(arena, &mut elem);
            *dty_ref = arena.alloc(elem);

            let mut n = (*n_ref).clone();
            visitor.visit_nat(arena, &mut n);
            *n_ref = n;
        }
        DataTyKind::At(dty_ref, mem) => {
            let mut elem = (**dty_ref).clone();
            visitor.visit_dty(arena, &mut elem);
            *dty_ref = arena.alloc(elem);

            visitor.visit_mem(arena, mem);
        }
        DataTyKind::Ref(reff_ref) => {
            let mut r = (**reff_ref).clone();
            visitor.visit_ref(arena, &mut r);
            *reff_ref = arena.alloc(r);
        }
        DataTyKind::RawPtr(datayt_ref) => {
            let mut elem = (**datayt_ref).clone();
            visitor.visit_dty(arena, &mut elem);
            *datayt_ref = arena.alloc(elem);
        }

        DataTyKind::Dead(datayt_ref) => {
            let mut elem = (**datayt_ref).clone();
            visitor.visit_dty(arena, &mut elem);
            *datayt_ref = arena.alloc(elem);
        }
    }
}

pub fn walk_fn_ty<'a, V: VisitMut<'a>>(visitor: &mut V, arena: &'a Bump, fn_ty: &mut FnTy<'a>) {
    let FnTy {
        generics,
        generic_exec,
        param_sigs,
        exec,
        ret_ty,
        nat_constrs,
    } = fn_ty;
    walk_list!(visitor, visit_ident_kinded, generics, arena);
    for exec_decl in generic_exec {
        visitor.visit_ident_exec(arena, exec_decl)
    }
    walk_list!(visitor, visit_param_sig, param_sigs, arena);
    visitor.visit_exec_expr(arena, exec);
    let mut ret_ty_owned = (**ret_ty).clone();
    visitor.visit_ty(arena, &mut ret_ty_owned);
    *ret_ty = arena.alloc(ret_ty_owned);
    walk_list!(visitor, visit_nat_constr, nat_constrs, arena);
}

pub fn walk_nat_constr<'a, V: VisitMut<'a>>(
    visitor: &mut V,
    arena: &'a Bump,
    nat_constr: &mut NatConstr<'a>,
) {
    match nat_constr {
        NatConstr::True => {}
        NatConstr::Eq(l, r) => {
            let mut owned_l = (**l).clone();
            let mut owned_r = (**r).clone();
            visitor.visit_nat(arena, &mut owned_l);
            visitor.visit_nat(arena, &mut owned_r);
            *l = arena.alloc(owned_l);
            *r = arena.alloc(owned_r);
        }
        NatConstr::Lt(l, r) => {
            let mut owned_l = (**l).clone();
            let mut owned_r = (**r).clone();
            visitor.visit_nat(arena, &mut owned_l);
            visitor.visit_nat(arena, &mut owned_r);
            *l = arena.alloc(owned_l);
            *r = arena.alloc(owned_r);
        }
        NatConstr::And(l, r) => {
            let mut owned_l = (**l).clone();
            let mut owned_r = (**r).clone();
            visitor.visit_nat_constr(arena, &mut owned_l);
            visitor.visit_nat_constr(arena, &mut owned_r);
            *l = arena.alloc(owned_l);
            *r = arena.alloc(owned_r);
        }
        NatConstr::Or(l, r) => {
            let mut owned_l = (**l).clone();
            let mut owned_r = (**r).clone();
            visitor.visit_nat_constr(arena, &mut owned_l);
            visitor.visit_nat_constr(arena, &mut owned_r);
            *l = arena.alloc(owned_l);
            *r = arena.alloc(owned_r);
        }
    }
}

pub fn walk_ty<'a, V: VisitMut<'a>>(visitor: &mut V, arena: &'a bumpalo::Bump, ty: &mut Ty<'a>) {
    match &mut ty.ty {
        TyKind::Data(dty) => {
            let mut dty_owned = (**dty).clone();
            visitor.visit_dty(arena, &mut dty_owned);
            *dty = arena.alloc(dty_owned);
        }
        TyKind::FnTy(fn_slot) => {
            let src: &FnTy<'a> = *fn_slot;

            let mut owned = FnTy {
                generics: src.generics.clone(),
                generic_exec: src.generic_exec.clone(),
                param_sigs: src.param_sigs.clone(),
                exec: src.exec.clone(),
                ret_ty: src.ret_ty,
                nat_constrs: src.nat_constrs.clone(),
            };

            walk_list!(visitor, visit_ident_kinded, &mut owned.generics, arena);

            if let Some(ref mut ie) = owned.generic_exec {
                visitor.visit_ident_exec(arena, ie);
            }

            walk_list!(visitor, visit_param_sig, &mut owned.param_sigs, arena);
            visitor.visit_exec_expr(arena, &mut owned.exec);

            let mut ret_owned = (*owned.ret_ty).clone();
            visitor.visit_ty(arena, &mut ret_owned);
            owned.ret_ty = arena.alloc(ret_owned);

            walk_list!(visitor, visit_nat_constr, &mut owned.nat_constrs, arena);

            *fn_slot = arena.alloc(owned);
        }
    }
}

pub fn walk_view<'a, V: VisitMut<'a>>(visitor: &mut V, arena: &'a Bump, view: &mut View<'a>) {
    visitor.visit_ident(arena, &mut view.name);
    walk_list!(visitor, visit_arg_kinded, &mut view.gen_args, arena);
    for v in &mut view.args {
        visitor.visit_view(arena, v)
    }
}

/**
pub fn walk_pl_expr<'a, V: VisitMut<'a>>(
    visitor: &mut V,
    arena: &'a Bump,
    pl_expr: &mut PlaceExpr<'a>,
) {
    match &mut pl_expr.pl_expr {
        PlaceExprKind::Ident(ident) => visitor.visit_ident(arena, ident),
        PlaceExprKind::Deref(pl_expr) => visitor.visit_pl_expr(arena, pl_expr),
        PlaceExprKind::Select(p, distrib_exec) => {
            visitor.visit_pl_expr(arena, p);
            visitor.visit_exec_expr(arena, distrib_exec);
        }
        PlaceExprKind::Proj(pl_expr, _) => {
            visitor.visit_pl_expr(arena, pl_expr);
        }
        PlaceExprKind::FieldProj(pl_expr, field_name) => {
            visitor.visit_pl_expr(arena, pl_expr);
            visitor.visit_ident(arena, field_name);
        }
        PlaceExprKind::View(pl_expr, view) => {
            visitor.visit_pl_expr(arena, pl_expr);
            visitor.visit_view(arena, view);
        }
        PlaceExprKind::Idx(pl_expr, n) => {
            visitor.visit_pl_expr(arena, pl_expr);
            visitor.visit_nat(arena, n)
        }
    }
}
*/

pub fn walk_pl_expr<'a, V: VisitMut<'a>>(
    visitor: &mut V,
    arena: &'a bumpalo::Bump,
    pl_expr: &mut PlaceExpr<'a>,
) {
    match &mut pl_expr.pl_expr {
        PlaceExprKind::Ident(ident) => {
            visitor.visit_ident(arena, ident);
        }

        PlaceExprKind::Deref(inner_ref) => {
            let mut owned = (**inner_ref).clone();
            visitor.visit_pl_expr(arena, &mut owned);
            *inner_ref = arena.alloc(owned);
        }

        PlaceExprKind::Select(p_ref, exec_ref) => {
            let mut p_owned = (**p_ref).clone();
            visitor.visit_pl_expr(arena, &mut p_owned);
            *p_ref = arena.alloc(p_owned);

            let mut exec_owned = (**exec_ref).clone();
            visitor.visit_exec_expr(arena, &mut exec_owned);
            *exec_ref = arena.alloc(exec_owned);
        }

        PlaceExprKind::Proj(p_ref, _k) => {
            let mut p_owned = (**p_ref).clone();
            visitor.visit_pl_expr(arena, &mut p_owned);
            *p_ref = arena.alloc(p_owned);
        }

        PlaceExprKind::FieldProj(p_ref, field_ref) => {
            let mut p_owned = (**p_ref).clone();
            visitor.visit_pl_expr(arena, &mut p_owned);
            *p_ref = arena.alloc(p_owned);

            let mut field_owned = (**field_ref).clone();
            visitor.visit_ident(arena, &mut field_owned);
            *field_ref = arena.alloc(field_owned);
        }

        PlaceExprKind::View(p_ref, view_ref) => {
            let mut p_owned = (**p_ref).clone();
            visitor.visit_pl_expr(arena, &mut p_owned);
            *p_ref = arena.alloc(p_owned);

            let mut view_owned = (**view_ref).clone();
            visitor.visit_view(arena, &mut view_owned);
            *view_ref = arena.alloc(view_owned);
        }

        PlaceExprKind::Idx(p_ref, n_ref) => {
            let mut p_owned = (**p_ref).clone();
            visitor.visit_pl_expr(arena, &mut p_owned);
            *p_ref = arena.alloc(p_owned);

            let mut n_owned = (**n_ref).clone();
            visitor.visit_nat(arena, &mut n_owned);
            *n_ref = arena.alloc(n_owned);
        }
    }
}

pub fn walk_arg_kinded<'a, V: VisitMut<'a>>(
    visitor: &mut V,
    arena: &'a Bump,
    arg_kinded: &mut ArgKinded<'a>,
) {
    match arg_kinded {
        ArgKinded::Ident(ident) => visitor.visit_ident(arena, ident),
        ArgKinded::Nat(n) => visitor.visit_nat(arena, n),
        ArgKinded::Memory(mem) => visitor.visit_mem(arena, mem),
        ArgKinded::DataTy(dty) => visitor.visit_dty(arena, dty),
        ArgKinded::Provenance(prv) => visitor.visit_prv(arena, prv),
    }
}

pub fn walk_pattern<'a, V: VisitMut<'a>>(
    visitor: &mut V,
    arena: &'a Bump,
    pattern: &mut Pattern<'a>,
) {
    match pattern {
        Pattern::Ident(mutab, ident) => {
            visitor.visit_mutability(mutab);
            visitor.visit_ident(arena, ident);
        }
        Pattern::Tuple(patterns) => {
            walk_list!(visitor, visit_pattern, patterns, arena)
        }
        Pattern::Wildcard => {}
    }
}

pub fn walk_split<'a, V: VisitMut<'a>>(visitor: &mut V, arena: &'a Bump, indep: &mut Split<'a>) {
    let Split {
        dim_compo,
        pos,
        split_exec,
        branch_idents,
        branch_bodies,
    } = indep;
    visitor.visit_dim_compo(dim_compo);
    visitor.visit_nat(arena, pos);
    let mut split_exec_owned = (**split_exec).clone();
    visitor.visit_exec_expr(arena, &mut split_exec_owned);
    *split_exec = arena.alloc(split_exec_owned);
    walk_list!(visitor, visit_ident, branch_idents, arena);
    walk_list!(visitor, visit_expr, branch_bodies, arena);
}

pub fn walk_sched<'a, V: VisitMut<'a>>(visitor: &mut V, arena: &'a Bump, sched: &mut Sched<'a>) {
    let Sched {
        dim,
        inner_exec_ident,
        sched_exec,
        body,
    } = sched;
    visitor.visit_dim_compo(dim);
    for ident in inner_exec_ident {
        visitor.visit_ident(arena, ident)
    }
    let mut sched_exec_owned = (**sched_exec).clone();
    visitor.visit_exec_expr(arena, &mut sched_exec_owned);
    *sched_exec = arena.alloc(sched_exec_owned);

    let mut body_owned = (**body).clone();
    visitor.visit_block(arena, &mut body_owned);
    *body = arena.alloc(body_owned);
}

pub fn walk_expr<'a, V: VisitMut<'a>>(visitor: &mut V, arena: &'a Bump, expr: &mut Expr<'a>) {
    // For now, only visit ExprKind
    match &mut expr.expr {
        ExprKind::Lit(l) => visitor.visit_lit(l),
        ExprKind::PlaceExpr(pl_ref) => {
            let mut owned = (**pl_ref).clone();
            visitor.visit_pl_expr(arena, &mut owned);
            *pl_ref = arena.alloc(owned);
        }
        ExprKind::Ref(_, own, pl_ref) => {
            visitor.visit_own(own);
            let mut owned = (**pl_ref).clone();
            visitor.visit_pl_expr(arena, &mut owned);
            *pl_ref = arena.alloc(owned);
        }
        ExprKind::Block(block_ref) => {
            let mut owned = (**block_ref).clone();
            visitor.visit_block(arena, &mut owned);
            *block_ref = arena.alloc(owned);
        }
        ExprKind::LetUninit(maybe_exec_expr, ident_ref, ty_ref) => {
            if let Some(slot) = maybe_exec_expr.as_mut() {
                let mut owned = (**slot).clone();
                visitor.visit_exec_expr(arena, &mut owned);
                *slot = arena.alloc(owned);
            }

            visitor.visit_ident(arena, ident_ref);

            let mut ty_owned = (**ty_ref).clone();
            visitor.visit_ty(arena, &mut ty_owned);
            *ty_ref = arena.alloc(ty_owned);
        }
        ExprKind::Let(pattern, ty_opt, e) => {
            visitor.visit_pattern(arena, pattern);
            if let Some(slot) = ty_opt.as_mut() {
                let mut ty_owned = (**slot).clone();
                visitor.visit_ty(arena, &mut ty_owned);
                *slot = arena.alloc(ty_owned);
            }
            let mut e_owned = (**e).clone();
            visitor.visit_expr(arena, &mut e_owned);
            *e = arena.alloc(e_owned);
        }
        ExprKind::Assign(pl_expr, expr) => {
            let mut pl_expr_owned = (**pl_expr).clone();
            let mut expr_owned = (**expr).clone();
            visitor.visit_pl_expr(arena, &mut pl_expr_owned);
            visitor.visit_expr(arena, &mut expr_owned);
            *pl_expr = arena.alloc(pl_expr_owned);
            *expr = arena.alloc(expr_owned);
        }
        ExprKind::IdxAssign(pl_expr, idx, expr) => {
            let mut pl_expr_owned = (**pl_expr).clone();
            let mut expr_owned = (**expr).clone();
            visitor.visit_pl_expr(arena, &mut pl_expr_owned);
            visitor.visit_nat(arena, idx);
            visitor.visit_expr(arena, &mut expr_owned);
            *pl_expr = arena.alloc(pl_expr_owned);
            *expr = arena.alloc(expr_owned);
        }
        ExprKind::Seq(es) => {
            for e in es {
                visitor.visit_expr(arena, e)
            }
        }
        // ExprKind::Lambda(params, exec_decl, dty, expr) => {
        //     walk_list!(visitor, visit_param_decl, params);
        //     visitor.visit_ident_exec(exec_decl);
        //     visitor.visit_dty(dty);
        //     visitor.visit_expr(expr)
        // }
        ExprKind::App(f, gen_args, args) => {
            let mut f_owned = (**f).clone();
            visitor.visit_ident(arena, &mut f_owned);
            *f = arena.alloc(f_owned);
            walk_list!(visitor, visit_arg_kinded, gen_args, arena);
            walk_list!(visitor, visit_expr, args, arena);
        }
        ExprKind::DepApp(f, gen_args) => {
            visitor.visit_ident(arena, f);
            walk_list!(visitor, visit_arg_kinded, gen_args, arena);
        }
        ExprKind::AppKernel(app_kernel_ref) => {
            let src: &AppKernel<'a> = *app_kernel_ref;

            let mut tmp = AppKernel {
                grid_dim: src.grid_dim.clone(),
                block_dim: src.block_dim.clone(),
                shared_mem_dtys: src.shared_mem_dtys.clone(),
                shared_mem_prvs: src.shared_mem_prvs.clone(),
                fun_ident: {
                    let mut id = (*src.fun_ident).clone();
                    visitor.visit_ident(arena, &mut id);
                    arena.alloc(id)
                },
                gen_args: {
                    let mut v = src.gen_args.clone();
                    for a in v.iter_mut() {
                        visitor.visit_arg_kinded(arena, a);
                    }
                    v
                },
                args: {
                    let mut v = src.args.clone();
                    for e in v.iter_mut() {
                        visitor.visit_expr(arena, e);
                    }
                    v
                },
            };

            visitor.visit_dim(arena, &mut tmp.grid_dim);
            visitor.visit_dim(arena, &mut tmp.block_dim);
            for d in tmp.shared_mem_dtys.iter_mut() {
                visitor.visit_dty(arena, d);
            }

            *app_kernel_ref = arena.alloc(tmp);
        }
        ExprKind::IfElse(cond_ref, tt_ref, ff_ref) => {
            let mut cond = (**cond_ref).clone();
            let mut tt = (**tt_ref).clone();
            let mut ff = (**ff_ref).clone();
            visitor.visit_expr(arena, &mut cond);
            visitor.visit_expr(arena, &mut tt);
            visitor.visit_expr(arena, &mut ff);
            *cond_ref = arena.alloc(cond);
            *tt_ref = arena.alloc(tt);
            *ff_ref = arena.alloc(ff)
        }
        ExprKind::If(cond, tt) => {
            let mut cond_owned = (**cond).clone();
            let mut tt_owned = (**tt).clone();
            visitor.visit_expr(arena, &mut cond_owned);
            visitor.visit_expr(arena, &mut tt_owned);
            *cond = arena.alloc(cond_owned);
            *tt = arena.alloc(tt_owned);
        }
        ExprKind::Array(elems) => {
            walk_list!(visitor, visit_expr, elems, arena);
        }
        ExprKind::Tuple(elems) => {
            walk_list!(visitor, visit_expr, elems, arena);
        }
        ExprKind::For(ident, coll_ref, body_ref) => {
            visitor.visit_ident(arena, ident);
            let mut coll = (**coll_ref).clone();
            let mut body = (**body_ref).clone();
            visitor.visit_expr(arena, &mut coll);
            visitor.visit_expr(arena, &mut body);
            *coll_ref = arena.alloc(coll);
            *body_ref = arena.alloc(body);
        }
        ExprKind::Split(split_ref) => {
            let src: &Split<'a> = *split_ref;

            let mut dim = src.dim_compo;
            visitor.visit_dim_compo(&mut dim);

            let mut pos = src.pos.clone();
            visitor.visit_nat(arena, &mut pos);

            let mut exec_owned = (*src.split_exec).clone();
            visitor.visit_exec_expr(arena, &mut exec_owned);
            let exec_ref: &'a ExecExpr<'a> = arena.alloc(exec_owned);

            let mut branch_idents = src.branch_idents.clone();
            for id in branch_idents.iter_mut() {
                visitor.visit_ident(arena, id);
            }

            let mut branch_bodies = src.branch_bodies.clone();
            for body in branch_bodies.iter_mut() {
                visitor.visit_expr(arena, body);
            }

            let new_split = Split {
                dim_compo: dim,
                pos,
                split_exec: exec_ref,
                branch_idents,
                branch_bodies,
            };
            *split_ref = arena.alloc(new_split);
        }
        ExprKind::Sched(sched) => {
            let mut sched_owned = (**sched).clone();
            visitor.visit_sched(arena, &mut sched_owned);
            *sched = arena.alloc(sched_owned);
        }
        ExprKind::ForNat(ident, range, body) => {
            visitor.visit_ident(arena, ident);
            let mut range_owned = (**range).clone();
            let mut body_owned = (**body).clone();
            visitor.visit_nat_range(arena, &mut range_owned);
            visitor.visit_expr(arena, &mut body_owned);
            *range = arena.alloc(range_owned);
            *body = arena.alloc(body_owned);
        }
        ExprKind::While(cond, body) => {
            let mut cond_owned = (**cond).clone();
            let mut body_owned = (**body).clone();
            visitor.visit_expr(arena, &mut cond_owned);
            visitor.visit_expr(arena, &mut body_owned);
            *cond = arena.alloc(cond_owned);
            *body = arena.alloc(body_owned);
        }
        ExprKind::BinOp(op, l, r) => {
            visitor.visit_binary_op(op);
            let mut l_owned = (**l).clone();
            let mut r_owned = (**r).clone();
            visitor.visit_expr(arena, &mut l_owned);
            visitor.visit_expr(arena, &mut r_owned);
            *l = arena.alloc(l_owned);
            *r = arena.alloc(r_owned);
        }
        ExprKind::UnOp(op, expr) => {
            visitor.visit_unary_op(op);
            let mut expr_owned = (**expr).clone();
            visitor.visit_expr(arena, &mut expr_owned);
            *expr = arena.alloc(expr_owned);
        }
        ExprKind::Sync(exec) => {
            for e in exec {
                visitor.visit_exec_expr(arena, e)
            }
        }
        ExprKind::Unsafe(expr) => {
            let mut expr_owned = (**expr).clone();
            visitor.visit_expr(arena, &mut expr_owned);
            *expr = arena.alloc(expr_owned);
        }
        ExprKind::Cast(expr, dty) => {
            let mut expr_owned = (**expr).clone();
            let mut dty_owned = (**dty).clone();
            visitor.visit_expr(arena, &mut expr_owned);
            visitor.visit_dty(arena, &mut dty_owned);
            *expr = arena.alloc(expr_owned);
            *dty = arena.alloc(dty_owned);
        }
        ExprKind::Range(_, _) | ExprKind::Hole => (),
    }
}

pub fn walk_app_kernel<'a, V: VisitMut<'a>>(
    visitor: &mut V,
    arena: &'a Bump,
    app_kernel: &mut AppKernel<'a>,
) {
    let AppKernel {
        grid_dim,
        block_dim,
        shared_mem_dtys,
        shared_mem_prvs: _,
        fun_ident,
        gen_args,
        args,
    } = app_kernel;
    visitor.visit_dim(arena, grid_dim);
    visitor.visit_dim(arena, block_dim);
    for dty in shared_mem_dtys {
        visitor.visit_dty(arena, dty);
    }
    let mut fun_owned = (**fun_ident).clone();
    visitor.visit_ident(arena, &mut fun_owned);
    *fun_ident = arena.alloc(fun_owned);
    for garg in gen_args {
        visitor.visit_arg_kinded(arena, garg);
    }
    for arg in args {
        visitor.visit_expr(arena, arg);
    }
}

pub fn walk_block<'a, V: VisitMut<'a>>(visitor: &mut V, arena: &'a Bump, block: &mut Block<'a>) {
    let Block { body, .. } = block;
    let mut body_owned = (**body).clone();
    visitor.visit_expr(arena, &mut body_owned);
    *body = arena.alloc(body_owned);
}

pub fn walk_split_proj<'a, V: VisitMut<'a>>(
    visitor: &mut V,
    arena: &'a Bump,
    split_proj: &mut TakeRange<'a>,
) {
    let TakeRange {
        split_dim,
        pos,
        left_or_right: _,
    } = split_proj;
    visitor.visit_dim_compo(split_dim);
    visitor.visit_nat(arena, pos);
}

/**
pub fn walk_exec_expr<'a, V: VisitMut<'a>>(
    visitor: &mut V,
    arena: &'a Bump,
    exec_expr: &mut ExecExpr<'a>,
) {
    visitor.visit_exec(arena, &mut exec_expr.exec);
    for t in &mut exec_expr.ty {
        visitor.visit_exec_ty(t);
    }
}
*/

pub fn walk_exec_expr<'a, V: VisitMut<'a>>(
    visitor: &mut V,
    arena: &'a bumpalo::Bump,
    exec_expr: &mut ExecExpr<'a>,
) {
    let mut exec_owned = (*exec_expr.exec).clone();
    visitor.visit_exec(arena, &mut exec_owned);
    exec_expr.exec = arena.alloc(exec_owned);

    if let Some(ty_ref) = &mut exec_expr.ty {
        let mut ty_owned = (**ty_ref).clone();
        visitor.visit_exec_ty(&mut ty_owned);
        *ty_ref = arena.alloc(ty_owned);
    }
}

pub fn walk_exec<'a, V: VisitMut<'a>>(
    visitor: &mut V,
    arena: &'a Bump,
    exec: &mut ExecExprKind<'a>,
) {
    let ExecExprKind { base, path } = exec;
    match base {
        BaseExec::CpuThread => (),
        BaseExec::Ident(ident) => visitor.visit_ident(arena, ident),
        BaseExec::GpuGrid(gdim, bdim) => {
            let mut gdim_owned = (**gdim).clone();
            let mut bdim_owned = (**bdim).clone();
            visitor.visit_dim(arena, &mut gdim_owned);
            visitor.visit_dim(arena, &mut bdim_owned);
            *gdim = arena.alloc(gdim_owned);
            *bdim = arena.alloc(bdim_owned);
        }
    };
    for e in path {
        visitor.visit_exec_path_elem(arena, e)
    }
}

pub fn walk_exec_path_elem<'a, V: VisitMut<'a>>(
    visitor: &mut V,
    arena: &'a Bump,
    exec_path_elem: &mut ExecPathElem<'a>,
) {
    match exec_path_elem {
        ExecPathElem::TakeRange(split_proj) => {
            let mut split_proj_owned = (**split_proj).clone();
            visitor.visit_split_proj(arena, &mut split_proj_owned);
            *split_proj = arena.alloc(split_proj_owned);
        }
        ExecPathElem::ForAll(dim_compo) => visitor.visit_dim_compo(dim_compo),
        ExecPathElem::ToWarps => {}
        ExecPathElem::ToThreads(dim_compo) => visitor.visit_dim_compo(dim_compo),
    }
}

pub fn walk_param_decl<'a, V: VisitMut<'a>>(
    visitor: &mut V,
    arena: &'a Bump,
    param_decl: &mut ParamDecl<'a>,
) {
    let ParamDecl {
        ident,
        ty,
        mutbl,
        exec_expr,
    } = param_decl;
    visitor.visit_ident(arena, ident);
    if let Some(tty) = ty {
        let mut tty_owned = (**tty).clone();
        visitor.visit_ty(arena, &mut tty_owned);
        *tty = arena.alloc(tty_owned);
    }
    visitor.visit_mutability(mutbl);
    for ex in exec_expr {
        visitor.visit_exec_expr(arena, ex);
    }
}

pub fn walk_fun_def<'a, V: VisitMut<'a>>(
    visitor: &mut V,
    arena: &'a Bump,
    fun_def: &mut FunDef<'a>,
) {
    let FunDef {
        ident: _,
        generic_params,
        generic_exec,
        param_decls: params,
        ret_dty,
        exec,
        prv_rels,
        body,
    } = fun_def;
    walk_list!(visitor, visit_ident_kinded, generic_params, arena);
    for exec_decl in generic_exec {
        visitor.visit_ident_exec(arena, exec_decl);
    }
    walk_list!(visitor, visit_param_decl, params, arena);
    let mut ret_dty_owned = (**ret_dty).clone();
    visitor.visit_dty(arena, &mut ret_dty_owned);
    *ret_dty = arena.alloc(ret_dty_owned);

    visitor.visit_exec_expr(arena, exec);
    walk_list!(visitor, visit_prv_rel, prv_rels, arena);

    let mut body_owned = (**body).clone();
    visitor.visit_block(arena, &mut body_owned);
    *body = arena.alloc(body_owned);
}

pub fn walk_fun_decl<'a, V: VisitMut<'a>>(
    visitor: &mut V,
    arena: &'a Bump,
    fun_decl: &mut FunDecl<'a>,
) {
    let FunDecl {
        ident: _,
        generic_params,
        generic_exec,
        param_decls: params,
        ret_dty,
        exec,
        prv_rels,
    } = fun_decl;
    walk_list!(visitor, visit_ident_kinded, generic_params, arena);
    for exec_decl in generic_exec {
        visitor.visit_ident_exec(arena, exec_decl);
    }
    walk_list!(visitor, visit_param_decl, params, arena);
    let mut ret_dty_owned = (**ret_dty).clone();
    visitor.visit_dty(arena, &mut ret_dty_owned);
    *ret_dty = arena.alloc(ret_dty_owned);
    visitor.visit_exec_expr(arena, exec);
    walk_list!(visitor, visit_prv_rel, prv_rels, arena);
}

pub fn walk_param_sig<'a, V: VisitMut<'a>>(
    visitor: &mut V,
    arena: &'a Bump,
    param_sig: &mut ParamSig<'a>,
) {
    let ParamSig { exec_expr, ty } = param_sig;
    visitor.visit_exec_expr(arena, exec_expr);
    let mut ty_owned = (**ty).clone();
    visitor.visit_ty(arena, &mut ty_owned);
    *ty = arena.alloc(ty_owned);
}

pub fn walk_field<'a, V: VisitMut<'a>>(
    visitor: &mut V,
    arena: &'a Bump,
    field: &mut (Ident<'a>, DataTy<'a>),
) {
    let (ident, dty) = field;
    visitor.visit_ident(arena, ident);
    visitor.visit_dty(arena, dty);
}
