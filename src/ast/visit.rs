use crate::ast::*;

#[rustfmt::skip]
pub trait Visit: Sized {
    fn visit_binary_op_nat(&mut self, _op: &BinOpNat) {}
    fn visit_nat(&mut self, n: &Nat) { walk_nat(self, n) }
    fn visit_ident_kinded(&mut self, id_kind: &IdentKinded) { walk_ident_kinded(self, id_kind)}
    fn visit_prv_rel(&mut self, prv_rel: &PrvRel) { walk_prv_rel(self, prv_rel) }
    fn visit_exec(&mut self, _exec: &Exec) {}
    fn visit_mem(&mut self, mem: &Memory) { walk_mem(self, mem) }
    fn visit_prv(&mut self, prv: &Provenance) { walk_prv(self, prv) }
    fn visit_scalar_ty(&mut self, _sty: &ScalarTy) {}
    fn visit_th_hierchy(&mut self, th_hierchy: &ThreadHierchyTy) { walk_th_hierchy(self, th_hierchy) }
    fn visit_dty(&mut self, dty: &DataTy) { walk_dty(self, dty) }
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
    fn visit_expr(&mut self, expr: &Expr) { walk_expr(self, expr) }
    fn visit_param_decl(&mut self, param_decl: &ParamDecl) { walk_param_decl(self, param_decl) }
    fn visit_fun_def(&mut self, fun_def: &FunDef) { walk_fun_def(self, fun_def) }
}

// Taken from the Rust compiler
macro_rules! walk_list {
    ($visitor: expr, $method: ident, $list: expr) => {
        for elem in $list {
            $visitor.$method(elem)
        }
    };
}

pub fn walk_nat<V: Visit>(visitor: &mut V, n: &Nat) {
    match n {
        Nat::Ident(ident) => visitor.visit_ident(ident),
        Nat::BinOp(op, l, r) => {
            visitor.visit_binary_op_nat(op);
            visitor.visit_nat(l);
            visitor.visit_nat(r)
        }
        Nat::Lit(_) => {}
        Nat::App(func, args) => {
            visitor.visit_ident(func);
            walk_list!(visitor, visit_nat, args)
        }
    }
}

pub fn walk_ident_kinded<V: Visit>(visitor: &mut V, id_kind: &IdentKinded) {
    let IdentKinded { ident, kind } = id_kind;
    visitor.visit_ident(ident);
    visitor.visit_kind(kind)
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

pub fn walk_th_hierchy<V: Visit>(visitor: &mut V, th_hierchy: &ThreadHierchyTy) {
    match th_hierchy {
        ThreadHierchyTy::BlockGrp(n1, n2, n3, m1, m2, m3) => {
            visitor.visit_nat(n1);
            visitor.visit_nat(n2);
            visitor.visit_nat(n3);
            visitor.visit_nat(m1);
            visitor.visit_nat(m2);
            visitor.visit_nat(m3);
        }
        ThreadHierchyTy::ThreadGrp(n1, n2, n3) => {
            visitor.visit_nat(n1);
            visitor.visit_nat(n2);
            visitor.visit_nat(n3);
        }
        ThreadHierchyTy::WarpGrp(n) => visitor.visit_nat(n),
        ThreadHierchyTy::Warp => {}
    }
}

pub fn walk_dty<V: Visit>(visitor: &mut V, dty: &DataTy) {
    match dty {
        DataTy::Ident(ident) => visitor.visit_ident(ident),
        DataTy::Scalar(sty) => visitor.visit_scalar_ty(sty),
        DataTy::Atomic(aty) => visitor.visit_scalar_ty(aty),
        DataTy::ThreadHierchy(th_hy) => visitor.visit_th_hierchy(th_hy),
        DataTy::Tuple(elem_dtys) => walk_list!(visitor, visit_dty, elem_dtys),
        DataTy::Array(dty, n) => {
            visitor.visit_dty(dty);
            visitor.visit_nat(n)
        }
        DataTy::ArrayShape(dty, n) => {
            visitor.visit_dty(dty);
            visitor.visit_nat(n);
        }
        DataTy::At(dty, mem) => {
            visitor.visit_dty(dty);
            visitor.visit_mem(mem)
        }
        DataTy::Ref(prv, own, mem, dty) => {
            visitor.visit_prv(prv);
            visitor.visit_own(own);
            visitor.visit_mem(mem);
            visitor.visit_dty(dty)
        }
        DataTy::RawPtr(dty) => visitor.visit_dty(dty),
        DataTy::Range => (),
        DataTy::Dead(dty) => visitor.visit_dty(dty),
    }
}

pub fn walk_ty<V: Visit>(visitor: &mut V, ty: &Ty) {
    match &ty.ty {
        TyKind::Data(dty) => visitor.visit_dty(dty),
        TyKind::TupleView(elem_tys) => walk_list!(visitor, visit_ty, elem_tys),
        TyKind::Fn(gen_params, params, exec, ret_ty) => {
            walk_list!(visitor, visit_ident_kinded, gen_params);
            walk_list!(visitor, visit_ty, params);
            visitor.visit_exec(exec);
            visitor.visit_ty(ret_ty)
        }
        TyKind::Ident(ident) => visitor.visit_ident(ident),
        TyKind::Dead(ty) => visitor.visit_ty(ty),
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
        ArgKinded::Ty(ty) => visitor.visit_ty(ty),
        ArgKinded::DataTy(dty) => visitor.visit_dty(dty),
        ArgKinded::Provenance(prv) => visitor.visit_prv(prv),
    }
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
        ExprKind::Let(mutabl, ident, ty, e) => {
            visitor.visit_mutability(mutabl);
            visitor.visit_ident(ident);
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
        ExprKind::Lambda(params, exec, dty, expr) => {
            walk_list!(visitor, visit_param_decl, params);
            visitor.visit_exec(exec);
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
        ExprKind::ParForWith(decls, par_elem, parall_collec, input_elems, input, body) => {
            for d in decls {
                walk_list!(visitor, visit_expr, d)
            }
            for ident in par_elem {
                visitor.visit_ident(ident)
            }
            visitor.visit_expr(parall_collec);
            walk_list!(visitor, visit_ident, input_elems);
            walk_list!(visitor, visit_expr, input);
            visitor.visit_expr(body)
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
        ExprKind::TupleView(elems) => {
            walk_list!(visitor, visit_expr, elems);
        }
        ExprKind::Split(_prv_val1, _prv_val2, own, s, view) => {
            visitor.visit_own(own);
            visitor.visit_nat(s);
            visitor.visit_pl_expr(view);
        }
        ExprKind::Idx(e, i) => {
            visitor.visit_expr(e);
            visitor.visit_nat(i);
        }
        ExprKind::Deref(expr) => visitor.visit_expr(expr),
        ExprKind::Range(_, _) => (),
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
        name: _,
        generic_params,
        param_decls: params,
        ret_dty,
        exec,
        prv_rels,
        body_expr,
    } = fun_def;
    walk_list!(visitor, visit_ident_kinded, generic_params);
    walk_list!(visitor, visit_param_decl, params);
    visitor.visit_dty(ret_dty);
    visitor.visit_exec(exec);
    walk_list!(visitor, visit_prv_rel, prv_rels);
    visitor.visit_expr(body_expr)
}
