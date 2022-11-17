use crate::ast::*;

#[rustfmt::skip]
pub trait Visit: Sized {
    fn visit_binary_op_nat(&mut self, _op: &BinOpNat) {}
    fn visit_nat(&mut self, n: &Nat) { walk_nat(self, n) }
    fn visit_ident_kinded(&mut self, id_kind: &IdentKinded) { walk_ident_kinded(self, id_kind) }
    fn visit_ident_exec(&mut self, ident_exec: &IdentExec) { walk_ident_exec(self, ident_exec) }
    fn visit_prv_rel(&mut self, prv_rel: &PrvRel) { walk_prv_rel(self, prv_rel) }
    fn visit_exec_ty(&mut self, _exec: &ExecTy) {}
    fn visit_mem(&mut self, mem: &Memory) { walk_mem(self, mem) }
    fn visit_prv(&mut self, prv: &Provenance) { walk_prv(self, prv) }
    fn visit_scalar_ty(&mut self, _sty: &ScalarTy) {}
    fn visit_dim_compo(&mut self, _dim_compo: &DimCompo) { }
    fn visit_dim(&mut self, dim: &Dim) { walk_dim(self, dim) }
    fn visit_dim3d(&mut self, dim3d: &Dim3d) { walk_dim3d(self, dim3d) }
    fn visit_dim2d(&mut self, dim2d: &Dim2d) { walk_dim2d(self, dim2d) }
    fn visit_dim1d(&mut self, dim1d: &Dim1d) { walk_dim1d(self, dim1d) }
    fn visit_ref(&mut self, reff: &RefDty) { walk_ref(self, reff) }
    fn visit_dty(&mut self, dty: &DataTy) { walk_dty(self, dty) }
    fn visit_fn_ty(&mut self, fn_ty: &FnTy) { walk_fn_ty(self, fn_ty) }
    fn visit_ty(&mut self, ty: &Ty) { walk_ty(self, ty) }
    fn visit_pl_expr(&mut self, pl_expr: &PlaceExpr) { walk_pl_expr(self, pl_expr) }
    fn visit_arg_kinded(&mut self, arg_kinded: &ArgKinded) { walk_arg_kinded(self, arg_kinded) }
    fn visit_kind(&mut self, _kind: &Kind) {}
    fn visit_binary_op(&mut self, _op: &BinOp) {}
    fn visit_unary_op(&mut self, _op: &UnOp) {}
    fn visit_own(&mut self, _own: &Ownership) {}
    fn visit_mutability(&mut self, _mutbl: &Mutability) {}
    fn visit_lit(&mut self, _lit: &Lit) {}
    fn visit_ident(&mut self, _ident: &Ident) {}
    fn visit_pattern(&mut self, pattern: &Pattern) { walk_pattern(self, pattern) }
    fn visit_indep(&mut self, par_branch: &Indep) { walk_indep(self, par_branch) }
    fn visit_par_for(&mut self, par_for: &Sched) { walk_par_for(self, par_for) }
    fn visit_expr_split(&mut self, expr_split: &ExprSplit) { walk_expr_split(self, expr_split) }
    fn visit_expr(&mut self, expr: &Expr) { walk_expr(self, expr) }
    fn visit_split_proj(&mut self, exec_split: &SplitProj) { walk_split_proj(self, exec_split) }
    fn visit_exec_expr(&mut self, exec_expr: &ExecExpr) { walk_exec_expr(self, exec_expr) }
    fn visit_exec(&mut self, exec: &Exec) { walk_exec(self, exec) }
    fn visit_param_decl(&mut self, param_decl: &ParamDecl) { walk_param_decl(self, param_decl) }
    fn visit_fun_def(&mut self, fun_def: &FunDef) { walk_fun_def(self, fun_def) }
}

macro_rules! walk_list {
    ($visitor: expr, $method: ident, $list: expr) => {
        for elem in $list {
            $visitor.$method(elem)
        }
    };
}
pub(crate) use walk_list;

pub fn walk_nat<V: Visit>(visitor: &mut V, n: &Nat) {
    match n {
        Nat::Ident(ident) => visitor.visit_ident(ident),
        Nat::BinOp(op, l, r) => {
            visitor.visit_binary_op_nat(op);
            visitor.visit_nat(l);
            visitor.visit_nat(r)
        }
        Nat::GridIdx | Nat::BlockIdx(_) | Nat::BlockDim(_) | Nat::ThreadIdx(_) | Nat::Lit(_) => {}
        Nat::App(func, args) => {
            visitor.visit_ident(func);
            walk_list!(visitor, visit_nat, args.as_ref())
        }
    }
}

pub fn walk_ident_kinded<V: Visit>(visitor: &mut V, id_kind: &IdentKinded) {
    let IdentKinded { ident, kind } = id_kind;
    visitor.visit_ident(ident);
    visitor.visit_kind(kind)
}

pub fn walk_ident_exec<V: Visit>(visitor: &mut V, id_exec: &IdentExec) {
    let IdentExec { ident, ty } = id_exec;
    visitor.visit_ident(ident);
    visitor.visit_exec_ty(ty)
}

pub fn walk_prv_rel<V: Visit>(visitor: &mut V, prv_rel: &PrvRel) {
    let PrvRel { longer, shorter } = prv_rel;
    visitor.visit_ident(longer);
    visitor.visit_ident(shorter)
}

pub fn walk_mem<V: Visit>(visitor: &mut V, mem: &Memory) {
    if let Memory::Ident(ident) = mem {
        visitor.visit_ident(ident)
    }
}

pub fn walk_prv<V: Visit>(visitor: &mut V, prv: &Provenance) {
    match prv {
        Provenance::Ident(ident) => visitor.visit_ident(ident),
        Provenance::Value(_) => {}
    }
}

pub fn walk_dim3d<V: Visit>(visitor: &mut V, dim3d: &Dim3d) {
    let Dim3d(n1, n2, n3) = dim3d;
    visitor.visit_nat(n1);
    visitor.visit_nat(n2);
    visitor.visit_nat(n3);
}

pub fn walk_dim2d<V: Visit>(visitor: &mut V, dim2d: &Dim2d) {
    let Dim2d(n1, n2) = dim2d;
    visitor.visit_nat(n1);
    visitor.visit_nat(n2);
}

pub fn walk_dim1d<V: Visit>(visitor: &mut V, dim1d: &Dim1d) {
    let Dim1d(n) = dim1d;
    visitor.visit_nat(n);
}

pub fn walk_dim<V: Visit>(visitor: &mut V, dim: &Dim) {
    match dim {
        Dim::XYZ(dim3d) => {
            visitor.visit_dim3d(dim3d);
        }
        Dim::XY(dim2d) | Dim::XZ(dim2d) | Dim::YZ(dim2d) => {
            visitor.visit_dim2d(dim2d);
        }
        Dim::X(dim1d) | Dim::Y(dim1d) | Dim::Z(dim1d) => visitor.visit_dim1d(dim1d),
    }
}

pub fn walk_ref<V: Visit>(visitor: &mut V, reff: &RefDty) {
    let RefDty { rgn, own, mem, dty } = reff;
    visitor.visit_prv(rgn);
    visitor.visit_own(own);
    visitor.visit_mem(mem);
    visitor.visit_dty(dty);
}

pub fn walk_dty<V: Visit>(visitor: &mut V, dty: &DataTy) {
    match &dty.dty {
        DataTyKind::Ident(ident) => visitor.visit_ident(ident),
        DataTyKind::Scalar(sty) => visitor.visit_scalar_ty(sty),
        DataTyKind::Atomic(aty) => visitor.visit_scalar_ty(aty),
        DataTyKind::Tuple(elem_dtys) => walk_list!(visitor, visit_dty, elem_dtys),
        DataTyKind::Array(dty, n) => {
            visitor.visit_dty(dty);
            visitor.visit_nat(n)
        }
        DataTyKind::ArrayShape(dty, n) => {
            visitor.visit_dty(dty);
            visitor.visit_nat(n);
        }
        DataTyKind::At(dty, mem) => {
            visitor.visit_dty(dty);
            visitor.visit_mem(mem)
        }
        DataTyKind::Ref(reff) => {
            visitor.visit_ref(reff);
        }
        DataTyKind::RawPtr(dty) => visitor.visit_dty(dty),
        DataTyKind::Range => {}
        DataTyKind::Dead(dty) => visitor.visit_dty(dty),
    }
}

pub fn walk_fn_ty<V: Visit>(visitor: &mut V, fn_ty: &FnTy) {
    let FnTy {
        generics,
        param_tys,
        exec_ty,
        ret_ty,
    } = fn_ty;
    walk_list!(visitor, visit_ident_kinded, generics);
    walk_list!(visitor, visit_ty, param_tys);
    visitor.visit_exec_ty(exec_ty);
    visitor.visit_ty(ret_ty);
}

pub fn walk_ty<V: Visit>(visitor: &mut V, ty: &Ty) {
    match &ty.ty {
        TyKind::Data(dty) => visitor.visit_dty(dty),
        TyKind::FnTy(fn_ty) => {
            visitor.visit_fn_ty(fn_ty);
        }
    }
}

pub fn walk_pl_expr<V: Visit>(visitor: &mut V, pl_expr: &PlaceExpr) {
    match &pl_expr.pl_expr {
        PlaceExprKind::Ident(ident) => visitor.visit_ident(ident),
        PlaceExprKind::Deref(pl_expr) => visitor.visit_pl_expr(pl_expr),
        PlaceExprKind::Proj(pl_expr, _) => {
            visitor.visit_pl_expr(pl_expr);
        }
    }
}

pub fn walk_arg_kinded<V: Visit>(visitor: &mut V, arg_kinded: &ArgKinded) {
    match arg_kinded {
        ArgKinded::Ident(ident) => visitor.visit_ident(ident),
        ArgKinded::Nat(n) => visitor.visit_nat(n),
        ArgKinded::Memory(mem) => visitor.visit_mem(mem),
        ArgKinded::DataTy(dty) => visitor.visit_dty(dty),
        ArgKinded::Provenance(prv) => visitor.visit_prv(prv),
    }
}

pub fn walk_pattern<V: Visit>(visitor: &mut V, pattern: &Pattern) {
    match pattern {
        Pattern::Ident(mutab, ident) => {
            visitor.visit_mutability(mutab);
            visitor.visit_ident(ident);
        }
        Pattern::Tuple(patterns) => {
            walk_list!(visitor, visit_pattern, patterns)
        }
        Pattern::Wildcard => {}
    }
}

pub fn walk_indep<V: Visit>(visitor: &mut V, indep: &Indep) {
    let Indep {
        dim_compo,
        pos,
        exec,
        branch_idents,
        branch_bodies,
    } = indep;
    visitor.visit_dim_compo(dim_compo);
    visitor.visit_nat(pos);
    visitor.visit_exec_expr(exec);
    walk_list!(visitor, visit_ident, branch_idents);
    walk_list!(visitor, visit_expr, branch_bodies);
}

pub fn walk_par_for<V: Visit>(visitor: &mut V, par_for: &Sched) {
    let Sched {
        decls,
        dim,
        exec_ident: inner_exec,
        exec,
        input_idents,
        input_views,
        body,
    } = par_for;
    visitor.visit_dim_compo(dim);
    for d in decls {
        walk_list!(visitor, visit_expr, d)
    }
    for ident in inner_exec {
        visitor.visit_ident(ident)
    }
    visitor.visit_exec_expr(exec);
    walk_list!(visitor, visit_ident, input_idents);
    walk_list!(visitor, visit_expr, input_views);
    visitor.visit_expr(body);
}

pub fn walk_expr_split<V: Visit>(visitor: &mut V, expr_split: &ExprSplit) {
    let ExprSplit {
        lrgn: _lrgn,
        rrgn: _rgn,
        own,
        pos,
        view,
    } = expr_split;
    visitor.visit_own(own);
    visitor.visit_nat(pos);
    visitor.visit_pl_expr(view);
}

pub fn walk_expr<V: Visit>(visitor: &mut V, expr: &Expr) {
    // For now, only visit ExprKind
    match &expr.expr {
        ExprKind::Lit(l) => visitor.visit_lit(l),
        ExprKind::PlaceExpr(pl_expr) => visitor.visit_pl_expr(pl_expr),
        ExprKind::Index(pl_expr, n) => {
            visitor.visit_pl_expr(pl_expr);
            visitor.visit_nat(n)
        }
        ExprKind::Ref(_, own, pl_expr) => {
            visitor.visit_own(own);
            visitor.visit_pl_expr(pl_expr);
        }
        ExprKind::Block(_, expr) => visitor.visit_expr(expr),
        ExprKind::LetUninit(ident, ty) => {
            visitor.visit_ident(ident);
            visitor.visit_ty(ty);
        }
        ExprKind::Let(pattern, ty, e) => {
            visitor.visit_pattern(pattern);
            for ty in ty.as_ref() {
                visitor.visit_ty(ty);
            }
            visitor.visit_expr(e);
        }
        ExprKind::BorrowIndex(_, own, pl_expr, n) => {
            visitor.visit_own(own);
            visitor.visit_pl_expr(pl_expr);
            visitor.visit_nat(n)
        }
        ExprKind::Assign(pl_expr, expr) => {
            visitor.visit_pl_expr(pl_expr);
            visitor.visit_expr(expr)
        }
        ExprKind::IdxAssign(pl_expr, idx, expr) => {
            visitor.visit_pl_expr(pl_expr);
            visitor.visit_nat(idx);
            visitor.visit_expr(expr);
        }
        ExprKind::Seq(es) => {
            for e in es {
                visitor.visit_expr(e)
            }
        }
        ExprKind::Lambda(params, exec_decl, dty, expr) => {
            walk_list!(visitor, visit_param_decl, params);
            visitor.visit_ident_exec(exec_decl);
            visitor.visit_dty(dty);
            visitor.visit_expr(expr)
        }
        ExprKind::App(f, gen_args, args) => {
            visitor.visit_expr(f);
            walk_list!(visitor, visit_arg_kinded, gen_args);
            walk_list!(visitor, visit_expr, args);
        }
        ExprKind::DepApp(f, gen_args) => {
            visitor.visit_expr(f);
            walk_list!(visitor, visit_arg_kinded, gen_args);
        }
        ExprKind::IfElse(cond, tt, ff) => {
            visitor.visit_expr(cond);
            visitor.visit_expr(tt);
            visitor.visit_expr(ff)
        }
        ExprKind::If(cond, tt) => {
            visitor.visit_expr(cond);
            visitor.visit_expr(tt)
        }
        ExprKind::Array(elems) => {
            walk_list!(visitor, visit_expr, elems);
        }
        ExprKind::Tuple(elems) => {
            walk_list!(visitor, visit_expr, elems);
        }
        ExprKind::Proj(e, _) => visitor.visit_expr(e),
        ExprKind::For(ident, coll, body) => {
            visitor.visit_ident(ident);
            visitor.visit_expr(coll);
            visitor.visit_expr(body);
        }
        ExprKind::Indep(par_branch) => {
            visitor.visit_indep(par_branch);
        }
        ExprKind::Sched(par_for) => {
            visitor.visit_par_for(par_for);
        }
        ExprKind::ForNat(ident, range, body) => {
            visitor.visit_ident(ident);
            visitor.visit_nat(range);
            visitor.visit_expr(body)
        }
        ExprKind::While(cond, body) => {
            visitor.visit_expr(cond);
            visitor.visit_expr(body);
        }
        ExprKind::BinOp(op, l, r) => {
            visitor.visit_binary_op(op);
            visitor.visit_expr(l);
            visitor.visit_expr(r)
        }
        ExprKind::UnOp(op, expr) => {
            visitor.visit_unary_op(op);
            visitor.visit_expr(expr)
        }
        ExprKind::Split(expr_split) => {
            visitor.visit_expr_split(expr_split);
        }
        ExprKind::Idx(e, i) => {
            visitor.visit_expr(e);
            visitor.visit_nat(i);
        }
        ExprKind::Deref(expr) => visitor.visit_expr(expr),
        ExprKind::Range(_, _) => (),
    }
}

pub fn walk_split_proj<V: Visit>(visitor: &mut V, split_proj: &SplitProj) {
    let SplitProj {
        split_dim,
        pos,
        proj: _,
    } = split_proj;
    visitor.visit_dim_compo(split_dim);
    visitor.visit_nat(pos);
}

pub fn walk_exec_expr<V: Visit>(visitor: &mut V, exec_expr: &ExecExpr) {
    visitor.visit_exec(&exec_expr.exec);
    for t in &exec_expr.ty {
        visitor.visit_exec_ty(t);
    }
}

pub fn walk_exec<V: Visit>(visitor: &mut V, exec: &Exec) {
    let Exec { base, path } = exec;
    match base {
        BaseExec::CpuThread => (),
        BaseExec::Ident(ident) => visitor.visit_ident(ident),
        BaseExec::GpuGrid(gdim, bdim) => {
            visitor.visit_dim(gdim);
            visitor.visit_dim(bdim);
        }
    };
    for e in path {
        match e {
            ExecPathElem::SplitProj(split_proj) => visitor.visit_split_proj(split_proj),
            ExecPathElem::Distrib(dim_compo) => visitor.visit_dim_compo(dim_compo),
        }
    }
}

pub fn walk_param_decl<V: Visit>(visitor: &mut V, param_decl: &ParamDecl) {
    let ParamDecl { ident, ty, mutbl } = param_decl;
    visitor.visit_ident(ident);
    if let Some(tty) = ty {
        visitor.visit_ty(tty);
    }
    visitor.visit_mutability(mutbl)
}

pub fn walk_fun_def<V: Visit>(visitor: &mut V, fun_def: &FunDef) {
    let FunDef {
        ident: _,
        generic_params,
        param_decls: params,
        ret_dty,
        exec_decl,
        prv_rels,
        body_expr,
    } = fun_def;
    walk_list!(visitor, visit_ident_kinded, generic_params);
    walk_list!(visitor, visit_param_decl, params);
    visitor.visit_dty(ret_dty);
    visitor.visit_ident_exec(exec_decl);
    walk_list!(visitor, visit_prv_rel, prv_rels);
    visitor.visit_expr(body_expr)
}
