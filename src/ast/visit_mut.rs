use crate::ast::*;

#[rustfmt::skip]
pub trait VisitMut: Sized {
    fn visit_binary_op_nat(&mut self, _op: &mut BinOpNat) {}
    fn visit_nat(&mut self, n: &mut Nat) { walk_nat(self, n) }
    fn visit_ident_kinded(&mut self, id_kind: &mut IdentKinded) { walk_ident_kinded(self, id_kind) }
    fn visit_ident_exec(&mut self, id_exec: &mut IdentExec) { walk_ident_exec(self, id_exec) }
    fn visit_prv_rel(&mut self, prv_rel: &mut PrvRel) { walk_prv_rel(self, prv_rel) }
    fn visit_exec_ty(&mut self, _exec: &mut ExecTy) {}
    fn visit_mem(&mut self, mem: &mut Memory) { walk_mem(self, mem) }
    fn visit_prv(&mut self, prv: &mut Provenance) { walk_prv(self, prv) }
    fn visit_scalar_ty(&mut self, _sty: &mut ScalarTy) {}
    fn visit_dim_compo(&mut self, _dim_compo: &mut DimCompo) { }
    fn visit_dim(&mut self, dim: &mut Dim) { walk_dim(self, dim) }
    fn visit_dim3d(&mut self, dim3d: &mut Dim3d) { walk_dim3d(self, dim3d) }
    fn visit_dim2d(&mut self, dim2d: &mut Dim2d) { walk_dim2d(self, dim2d) }
    fn visit_dim1d(&mut self, dim1d: &mut Dim1d) { walk_dim1d(self, dim1d) }
    fn visit_ref(&mut self, reff: &mut RefDty) { walk_ref(self, reff) }
    fn visit_dty(&mut self, dty: &mut DataTy) { walk_dty(self, dty) }
    fn visit_fn_ty(&mut self, fn_ty: &mut FnTy) { walk_fn_ty(self, fn_ty) }
    fn visit_ty(&mut self, ty: &mut Ty) { walk_ty(self, ty) }
    fn visit_view(&mut self, view: &mut View) { walk_view(self, view) }
    fn visit_pl_expr(&mut self, pl_expr: &mut PlaceExpr) { walk_pl_expr(self, pl_expr) }
    fn visit_arg_kinded(&mut self, arg_kinded: &mut ArgKinded) { walk_arg_kinded(self, arg_kinded) }
    fn visit_kind(&mut self, _kind: &mut Kind) {}
    fn visit_binary_op(&mut self, _op: &mut BinOp) {}
    fn visit_unary_op(&mut self, _op: &mut UnOp) {}
    fn visit_own(&mut self, _own: &mut Ownership) {}
    fn visit_mutability(&mut self, _mutbl: &mut Mutability) {}
    fn visit_lit(&mut self, _lit: &mut Lit) {}
    fn visit_ident(&mut self, _ident: &mut Ident) {}
    fn visit_pattern(&mut self, pattern: &mut Pattern) { walk_pattern(self, pattern) }
    fn visit_indep(&mut self, indep: &mut Indep) { walk_indep(self, indep) }
    fn visit_sched(&mut self, sched: &mut Sched) { walk_sched(self, sched) }
    fn visit_expr(&mut self, expr: &mut Expr) { walk_expr(self, expr) }
    fn visit_app_kernel(&mut self, app_kernel: &mut AppKernel) { walk_app_kernel(self, app_kernel) }
    fn visit_block(&mut self, block: &mut Block) { walk_block(self, block) }
    fn visit_split_proj(&mut self, exec_split: &mut SplitProj) { walk_split_proj(self, exec_split) }
    fn visit_exec_expr(&mut self, exec_expr: &mut ExecExpr) { walk_exec_expr(self, exec_expr) }
    fn visit_exec(&mut self, exec: &mut Exec) { walk_exec(self, exec) }
    fn visit_param_decl(&mut self, param_decl: &mut ParamDecl) { walk_param_decl(self, param_decl) }
    fn visit_fun_def(&mut self, fun_def: &mut FunDef) { walk_fun_def(self, fun_def) }
    fn visit_refine(&mut self, refine: &mut Refinement) { walk_refine(self, refine) }
    fn visit_pred(&mut self, pred: &mut Predicate) { walk_pred(self, pred) }
}

// Taken from the Rust compiler
macro_rules! walk_list {
    ($visitor: expr, $method: ident, $list: expr) => {
        for elem in $list {
            $visitor.$method(elem)
        }
    };
}
pub(crate) use walk_list;

pub fn walk_nat<V: VisitMut>(visitor: &mut V, n: &mut Nat) {
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
            walk_list!(visitor, visit_nat, args.as_mut())
        }
    }
}

pub fn walk_ident_kinded<V: VisitMut>(visitor: &mut V, id_kind: &mut IdentKinded) {
    let IdentKinded { ident, kind } = id_kind;
    visitor.visit_ident(ident);
    visitor.visit_kind(kind)
}

pub fn walk_ident_exec<V: VisitMut>(visitor: &mut V, id_exec: &mut IdentExec) {
    let IdentExec { ident, ty } = id_exec;
    visitor.visit_ident(ident);
    visitor.visit_exec_ty(ty)
}

pub fn walk_prv_rel<V: VisitMut>(visitor: &mut V, prv_rel: &mut PrvRel) {
    let PrvRel { longer, shorter } = prv_rel;
    visitor.visit_ident(longer);
    visitor.visit_ident(shorter)
}

pub fn walk_mem<V: VisitMut>(visitor: &mut V, mem: &mut Memory) {
    if let Memory::Ident(ident) = mem {
        visitor.visit_ident(ident)
    }
}

pub fn walk_prv<V: VisitMut>(visitor: &mut V, prv: &mut Provenance) {
    match prv {
        Provenance::Ident(ident) => visitor.visit_ident(ident),
        Provenance::Value(_) => {}
    }
}

pub fn walk_dim3d<V: VisitMut>(visitor: &mut V, dim3d: &mut Dim3d) {
    let Dim3d(n1, n2, n3) = dim3d;
    visitor.visit_ident(n1);
    visitor.visit_ident(n2);
    visitor.visit_ident(n3);
}

pub fn walk_dim2d<V: VisitMut>(visitor: &mut V, dim2d: &mut Dim2d) {
    let Dim2d(n1, n2) = dim2d;
    visitor.visit_ident(n1);
    visitor.visit_ident(n2);
}

pub fn walk_dim1d<V: VisitMut>(visitor: &mut V, dim1d: &mut Dim1d) {
    let Dim1d(n) = dim1d;
    visitor.visit_ident(n);
}

pub fn walk_dim<V: VisitMut>(visitor: &mut V, dim: &mut Dim) {
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

pub fn walk_ref<V: VisitMut>(visitor: &mut V, reff: &mut RefDty) {
    let RefDty { rgn, own, mem, dty } = reff;
    visitor.visit_prv(rgn);
    visitor.visit_own(own);
    visitor.visit_mem(mem);
    visitor.visit_dty(dty);
}

pub fn walk_pred<V: VisitMut>(visitor: &mut V, pred: &mut Predicate) {
    match pred {
        Predicate::Ident(ident) => visitor.visit_ident(ident),
        Predicate::Add(pl, pr) | Predicate::And(pl, pr) | Predicate::Or(pl, pr) => {
            visitor.visit_pred(pl);
            visitor.visit_pred(pr);
        }
        Predicate::ConstMul(_, pred) | Predicate::Not(pred) => {
            visitor.visit_pred(pred);
        }
        Predicate::IfElse(cond, tt, ff) => {
            visitor.visit_pred(cond);
            visitor.visit_pred(tt);
            visitor.visit_pred(ff);
        }
        Predicate::Uninterp(ident, preds) => {
            visitor.visit_ident(ident);
            walk_list!(visitor, visit_pred, preds);
        }
        Predicate::Num(_) | Predicate::True | Predicate::False => {}
    }
}

pub fn walk_refine<V: VisitMut>(visitor: &mut V, refine: &mut Refinement) {
    visitor.visit_ident(&mut refine.ident);
    visitor.visit_pred(&mut refine.pred);
}

pub fn walk_dty<V: VisitMut>(visitor: &mut V, dty: &mut DataTy) {
    match &mut dty.dty {
        DataTyKind::Ident(ident) => visitor.visit_ident(ident),
        DataTyKind::Scalar(sty) => visitor.visit_scalar_ty(sty),
        DataTyKind::Atomic(aty) => visitor.visit_scalar_ty(aty),
        DataTyKind::Tuple(elem_dtys) => walk_list!(visitor, visit_dty, elem_dtys),
        DataTyKind::Array(dty, n) => {
            visitor.visit_dty(dty);
            visitor.visit_ident(n)
        }
        DataTyKind::ArrayShape(dty, n) => {
            visitor.visit_dty(dty);
            visitor.visit_ident(n);
        }
        DataTyKind::At(dty, mem) => {
            visitor.visit_dty(dty);
            visitor.visit_mem(mem)
        }
        DataTyKind::Ref(reff) => {
            visitor.visit_ref(reff);
        }
        DataTyKind::Refine(_, refine) => visitor.visit_refine(refine),
        DataTyKind::RawPtr(dty) => visitor.visit_dty(dty),
        DataTyKind::Range => {}
        DataTyKind::Dead(dty) => visitor.visit_dty(dty),
    }
}

pub fn walk_fn_ty<V: VisitMut>(visitor: &mut V, fn_ty: &mut FnTy) {
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

pub fn walk_ty<V: VisitMut>(visitor: &mut V, ty: &mut Ty) {
    match &mut ty.ty {
        TyKind::Data(dty) => visitor.visit_dty(dty),
        TyKind::FnTy(fn_ty) => {
            visitor.visit_fn_ty(fn_ty);
        }
    }
}

pub fn walk_view<V: VisitMut>(visitor: &mut V, view: &mut View) {
    visitor.visit_ident(&mut view.name);
    walk_list!(visitor, visit_arg_kinded, &mut view.gen_args);
    for v in &mut view.args {
        visitor.visit_view(v)
    }
}

pub fn walk_pl_expr<V: VisitMut>(visitor: &mut V, pl_expr: &mut PlaceExpr) {
    match &mut pl_expr.pl_expr {
        PlaceExprKind::Ident(ident) => visitor.visit_ident(ident),
        PlaceExprKind::Deref(pl_expr) => visitor.visit_pl_expr(pl_expr),
        PlaceExprKind::Select(p, distrib_exec) => {
            visitor.visit_pl_expr(p);
            visitor.visit_exec_expr(distrib_exec);
        }
        PlaceExprKind::Proj(pl_expr, _) => {
            visitor.visit_pl_expr(pl_expr);
        }
        PlaceExprKind::View(pl_expr, view) => {
            visitor.visit_pl_expr(pl_expr);
            visitor.visit_view(view);
        }
        PlaceExprKind::Idx(pl_expr, n) => {
            visitor.visit_pl_expr(pl_expr);
            visitor.visit_nat(n)
        }
    }
}

pub fn walk_arg_kinded<V: VisitMut>(visitor: &mut V, arg_kinded: &mut ArgKinded) {
    match arg_kinded {
        ArgKinded::Ident(ident) => visitor.visit_ident(ident),
        ArgKinded::Nat(n) => visitor.visit_nat(n),
        ArgKinded::Memory(mem) => visitor.visit_mem(mem),
        ArgKinded::DataTy(dty) => visitor.visit_dty(dty),
        ArgKinded::Provenance(prv) => visitor.visit_prv(prv),
    }
}

pub fn walk_pattern<V: VisitMut>(visitor: &mut V, pattern: &mut Pattern) {
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

pub fn walk_indep<V: VisitMut>(visitor: &mut V, indep: &mut Indep) {
    let Indep {
        dim_compo,
        pos,
        split_exec,
        branch_idents,
        branch_bodies,
    } = indep;
    visitor.visit_dim_compo(dim_compo);
    visitor.visit_nat(pos);
    visitor.visit_exec_expr(split_exec);
    walk_list!(visitor, visit_ident, branch_idents);
    walk_list!(visitor, visit_expr, branch_bodies);
}

pub fn walk_sched<V: VisitMut>(visitor: &mut V, sched: &mut Sched) {
    let Sched {
        dim,
        inner_exec_ident,
        sched_exec,
        body,
    } = sched;
    visitor.visit_dim_compo(dim);
    for ident in inner_exec_ident {
        visitor.visit_ident(ident)
    }
    visitor.visit_exec_expr(sched_exec);
    visitor.visit_block(body);
}

pub fn walk_expr<V: VisitMut>(visitor: &mut V, expr: &mut Expr) {
    // For now, only visit ExprKind
    match &mut expr.expr {
        ExprKind::Lit(l) => visitor.visit_lit(l),
        ExprKind::PlaceExpr(pl_expr) => visitor.visit_pl_expr(pl_expr),

        ExprKind::Ref(_, own, pl_expr) => {
            visitor.visit_own(own);
            visitor.visit_pl_expr(pl_expr);
        }
        ExprKind::Block(block) => visitor.visit_block(block),
        ExprKind::LetUninit(ident, dty) => {
            visitor.visit_ident(ident);
            visitor.visit_dty(dty);
        }
        ExprKind::Let(pattern, dty, e) => {
            visitor.visit_pattern(pattern);
            for dty in dty.as_mut() {
                visitor.visit_dty(dty);
            }
            visitor.visit_expr(e);
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
        ExprKind::AppKernel(app_kernel) => visitor.visit_app_kernel(app_kernel),
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
        ExprKind::For(ident, coll, body) => {
            visitor.visit_ident(ident);
            visitor.visit_expr(coll);
            visitor.visit_expr(body);
        }
        ExprKind::Indep(par_branch) => {
            visitor.visit_indep(par_branch);
        }
        ExprKind::Sched(sched) => {
            visitor.visit_sched(sched);
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
        ExprKind::Sync(exec) => {
            for e in exec {
                visitor.visit_exec_expr(e)
            }
        }
        ExprKind::Range(_, _) => (),
    }
}

pub fn walk_app_kernel<V: VisitMut>(visitor: &mut V, app_kernel: &mut AppKernel) {
    let AppKernel {
        grid_dim,
        block_dim,
        shared_mem_dtys,
        shared_mem_prvs: _,
        fun,
        gen_args,
        args,
    } = app_kernel;
    visitor.visit_dim(grid_dim);
    visitor.visit_dim(block_dim);
    for dty in shared_mem_dtys {
        visitor.visit_dty(dty);
    }
    visitor.visit_expr(fun);
    for garg in gen_args {
        visitor.visit_arg_kinded(garg);
    }
    for arg in args {
        visitor.visit_expr(arg);
    }
}

pub fn walk_block<V: VisitMut>(visitor: &mut V, block: &mut Block) {
    let Block { body, .. } = block;
    visitor.visit_expr(body);
}

pub fn walk_split_proj<V: VisitMut>(visitor: &mut V, split_proj: &mut SplitProj) {
    let SplitProj {
        split_dim,
        pos,
        proj: _,
    } = split_proj;
    visitor.visit_dim_compo(split_dim);
    visitor.visit_nat(pos);
}

pub fn walk_exec_expr<V: VisitMut>(visitor: &mut V, exec_expr: &mut ExecExpr) {
    visitor.visit_exec(&mut exec_expr.exec);
    for t in &mut exec_expr.ty {
        visitor.visit_exec_ty(t);
    }
}

pub fn walk_exec<V: VisitMut>(visitor: &mut V, exec: &mut Exec) {
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
            ExecPathElem::ToThreads(dim_compo) => visitor.visit_dim_compo(dim_compo),
        }
    }
}

pub fn walk_param_decl<V: VisitMut>(visitor: &mut V, param_decl: &mut ParamDecl) {
    let ParamDecl { ident, dty, mutbl } = param_decl;
    visitor.visit_ident(ident);
    if let Some(ddty) = dty {
        visitor.visit_dty(ddty);
    }
    visitor.visit_mutability(mutbl)
}

pub fn walk_fun_def<V: VisitMut>(visitor: &mut V, fun_def: &mut FunDef) {
    let FunDef {
        ident: _,
        generic_params,
        param_decls: params,
        ret_dty,
        exec_decl,
        prv_rels,
        body,
    } = fun_def;
    walk_list!(visitor, visit_ident_kinded, generic_params);
    walk_list!(visitor, visit_param_decl, params);
    visitor.visit_dty(ret_dty);
    visitor.visit_ident_exec(exec_decl);
    walk_list!(visitor, visit_prv_rel, prv_rels);
    visitor.visit_block(body)
}
