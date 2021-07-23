use crate::ast::internal::*;
use crate::ast::*;

// TODO check if at least some of the functions that do not do anythng can be removed
#[rustfmt::skip]
pub trait Visitor: Sized {
    fn visit_binary_op_nat(&mut self, _op: &mut BinOpNat) {}
    fn visit_nat(&mut self, n: &mut Nat) { walk_nat(self, n) }
    fn visit_ident_kinded(&mut self, id_kind: &mut IdentKinded) { walk_ident_kinded(self, id_kind)}
    fn visit_prv_rel(&mut self, prv_rel: &mut PrvRel) { walk_prv_rel(self, prv_rel) }
    fn visit_exec(&mut self, _exec: &mut Exec) {}
    fn visit_mem(&mut self, mem: &mut Memory) { walk_mem(self, mem) }
    fn visit_prv(&mut self, prv: &mut Provenance) { walk_prv(self, prv) }
    fn visit_scalar_ty(&mut self, _sty: &mut ScalarTy) {}
    fn visit_vty(&mut self, vty: &mut ViewTy) { walk_vty(self, vty) }
    fn visit_th_hierchy(&mut self, th_hierchy: &mut ThreadHierchyTy) { walk_th_hierchy(self, th_hierchy) }
    fn visit_dty(&mut self, dty: &mut DataTy) { walk_dty(self, dty) }
    fn visit_ty(&mut self, ty: &mut Ty) { walk_ty(self, ty) }
    fn visit_pl_expr(&mut self, pl_expr: &mut PlaceExpr) { walk_pl_expr(self, pl_expr) }
    fn visit_arg_kinded(&mut self, arg_kinded: &mut ArgKinded) { walk_arg_kinded(self, arg_kinded) }
    fn visit_kind(&mut self, _kind: &mut Kind) {}
    fn visit_binary_op(&mut self, _op: &mut BinOp) {}
    fn visit_unary_op(&mut self, _op: &mut UnOp) {}
    fn visit_own(&mut self, _own: &mut Ownership) {}
    fn visit_mutability(&mut self, _mutbl: &mut Mutability) {}
    fn visit_lit(&mut self, _lit: &mut Lit) {}
    fn visit_ident(&mut self, _ident: &mut Ident) {}
    fn visit_expr(&mut self, expr: &mut Expr) { walk_expr(self, expr) }
    fn visit_param_decl(&mut self, param_decl: &mut ParamDecl) { walk_param_decl(self, param_decl) }
    fn visit_fun_def(&mut self, fun_def: &mut FunDef) { walk_fun_def(self, fun_def) }

    // internal
    // TODO
    fn visit_frm_expr(&mut self, frm_expr: &mut FrameExpr) {}
    fn visit_frm_entry(&mut self, frm_entry: &mut FrameEntry) {}
    fn visit_ident_typed(&mut self, ident_typed: &mut IdentTyped) {}
    fn visit_prv_mapping(&mut self, prv_mapping: &mut PrvMapping) {}
    fn visit_loan(&mut self, loan: &mut Loan) {}
}

// Taken from the Rust compiler
macro_rules! walk_list {
    ($visitor: expr, $method: ident, $list: expr) => {
        for elem in $list {
            $visitor.$method(elem)
        }
    };
}

pub fn walk_nat<V: Visitor>(visitor: &mut V, n: &mut Nat) {
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

pub fn walk_ident_kinded<V: Visitor>(visitor: &mut V, id_kind: &mut IdentKinded) {
    let IdentKinded { ident, kind } = id_kind;
    visitor.visit_ident(ident);
    visitor.visit_kind(kind)
}

pub fn walk_prv_rel<V: Visitor>(visitor: &mut V, prv_rel: &mut PrvRel) {
    let PrvRel { longer, shorter } = prv_rel;
    visitor.visit_ident(longer);
    visitor.visit_ident(shorter)
}

pub fn walk_mem<V: Visitor>(visitor: &mut V, mem: &mut Memory) {
    if let Memory::Ident(ident) = mem {
        visitor.visit_ident(ident)
    }
}

pub fn walk_prv<V: Visitor>(visitor: &mut V, prv: &mut Provenance) {
    match prv {
        Provenance::Ident(ident) => visitor.visit_ident(ident),
        Provenance::Value(_) => {}
    }
}

pub fn walk_vty<V: Visitor>(visitor: &mut V, vty: &mut ViewTy) {
    match vty {
        //ViewTy::Ident(ident) => visitor.visit_ident(ident),
        ViewTy::Tuple(elem_tys) => walk_list!(visitor, visit_ty, elem_tys),
        ViewTy::Array(elem_ty, n) => {
            visitor.visit_ty(elem_ty);
            visitor.visit_nat(n)
        }
        ViewTy::Dead(vty) => visitor.visit_vty(vty),
    }
}

pub fn walk_th_hierchy<V: Visitor>(visitor: &mut V, th_hierchy: &mut ThreadHierchyTy) {
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

pub fn walk_dty<V: Visitor>(visitor: &mut V, dty: &mut DataTy) {
    match dty {
        DataTy::Ident(ident) => visitor.visit_ident(ident),
        DataTy::Scalar(sty) => visitor.visit_scalar_ty(sty),
        DataTy::Atomic(aty) => visitor.visit_scalar_ty(aty),
        DataTy::Tuple(elem_dtys) => walk_list!(visitor, visit_dty, elem_dtys),
        DataTy::Array(dty, n) => {
            visitor.visit_dty(dty);
            visitor.visit_nat(n)
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
        DataTy::Dead(dty) => visitor.visit_dty(dty),
    }
}

pub fn walk_ty<V: Visitor>(visitor: &mut V, ty: &mut Ty) {
    match &mut ty.ty {
        TyKind::Data(dty) => visitor.visit_dty(dty),
        TyKind::View(vty) => visitor.visit_vty(vty),
        TyKind::ThreadHierchy(th_hy) => visitor.visit_th_hierchy(th_hy),
        TyKind::Fn(gen_params, params, exec, ret_ty) => {
            walk_list!(visitor, visit_ident_kinded, gen_params);
            walk_list!(visitor, visit_ty, params);
            visitor.visit_exec(exec);
            visitor.visit_ty(ret_ty)
        }
        TyKind::Ident(ident) => visitor.visit_ident(ident),
    }
}

pub fn walk_pl_expr<V: Visitor>(visitor: &mut V, pl_expr: &mut PlaceExpr) {
    match &mut pl_expr.kind {
        PlaceExprKind::Ident(ident) => visitor.visit_ident(ident),
        PlaceExprKind::Deref(pl_expr) => visitor.visit_pl_expr(pl_expr),
        PlaceExprKind::Proj(pl_expr, _) => {
            visitor.visit_pl_expr(pl_expr);
        }
    }
}

pub fn walk_arg_kinded<V: Visitor>(visitor: &mut V, arg_kinded: &mut ArgKinded) {
    match arg_kinded {
        ArgKinded::Ident(ident) => visitor.visit_ident(ident),
        ArgKinded::Nat(n) => visitor.visit_nat(n),
        ArgKinded::Memory(mem) => visitor.visit_mem(mem),
        ArgKinded::Ty(ty) => visitor.visit_ty(ty),
        ArgKinded::Provenance(prv) => visitor.visit_prv(prv),
    }
}

pub fn walk_expr<V: Visitor>(visitor: &mut V, expr: &mut Expr) {
    // For now, only visit ExprKind
    match &mut expr.expr {
        ExprKind::Lit(l) => visitor.visit_lit(l),
        ExprKind::PlaceExpr(pl_expr) => visitor.visit_pl_expr(pl_expr),
        ExprKind::Index(pl_expr, n) => {
            visitor.visit_pl_expr(pl_expr);
            visitor.visit_nat(n)
        }
        ExprKind::Ref(prv, own, pl_expr) => {
            visitor.visit_prv(prv);
            visitor.visit_own(own);
            visitor.visit_pl_expr(pl_expr);
        }
        ExprKind::LetProv(_, expr) => visitor.visit_expr(expr),
        ExprKind::LetUninit(ident, ty, e) => {
            visitor.visit_ident(ident);
            visitor.visit_ty(ty);
            visitor.visit_expr(e);
        }
        ExprKind::Let(mutabl, ident, ty, e1, e2) => {
            visitor.visit_mutability(mutabl);
            visitor.visit_ident(ident);
            match ty.as_mut() {
                Some(ty) => visitor.visit_ty(ty),
                None => {}
            };
            visitor.visit_expr(e1);
            visitor.visit_expr(e2)
        }
        ExprKind::BorrowIndex(prv, own, pl_expr, n) => {
            visitor.visit_prv(prv);
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
        ExprKind::Seq(e1, e2) => {
            visitor.visit_expr(e1);
            visitor.visit_expr(e2)
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
        ExprKind::ParFor(parall_collec, input, funs) => {
            visitor.visit_expr(parall_collec);
            visitor.visit_expr(input);
            visitor.visit_expr(funs)
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
        ExprKind::Idx(e, i) => {
            visitor.visit_expr(e);
            visitor.visit_nat(i);
        }
        ExprKind::Deref(expr) => visitor.visit_expr(expr),
    }
}

pub fn walk_param_decl<V: Visitor>(visitor: &mut V, param_decl: &mut ParamDecl) {
    let ParamDecl { ident, ty, mutbl } = param_decl;
    visitor.visit_ident(ident);
    visitor.visit_ty(ty);
    visitor.visit_mutability(mutbl)
}

pub fn walk_fun_def<V: Visitor>(visitor: &mut V, fun_def: &mut FunDef) {
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
