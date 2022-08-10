use crate::ast::*;

#[rustfmt::skip]
pub trait VisitSimilar: Sized {
    fn visit_binary_op_nats(&mut self, op1: &BinOpNat, op2: &BinOpNat) {}
    fn visit_nats(&mut self, n1: &Nat, n2: &Nat) { walk_nats(self, n1, n2) }
    fn visit_idents_kinded(&mut self, id_kind1: &IdentKinded, id_kind2: &IdentKinded) {
        walk_idents_kinded(self, id_kind1, id_kind2)
    }
    fn visit_prv_rels(&mut self, prv_rel1: &PrvRel, prv_rel2: &PrvRel) {
        walk_prv_rels(self, prv_rel1, prv_rel2)
    }
    fn visit_execs(&mut self, _exec1: &Exec, _exec2: &Exec) {}
    fn visit_mems(&mut self, mem1: &Memory, mem2: &Memory) { walk_mems(self, mem1, mem2) }
    fn visit_prvs(&mut self, prv1: &Provenance, prv2: &Provenance) { walk_prvs(self, prv1, prv2) }
    fn visit_scalar_tys(&mut self, _sty1: &ScalarTy, _sty2: &ScalarTy) {}
    fn visit_th_hierchys(&mut self, th_hierchy1: &ThreadHierchyTy, th_hierchy2: &ThreadHierchyTy) {
        walk_th_hierchys(self, th_hierchy)
    }
    fn visit_dtys(&mut self, dty1: &DataTy, dty2: &DataTy) { walk_dtys(self, dty1, dty2) }
    fn visit_tys(&mut self, ty1: &Ty, ty2: &Ty) { walk_tys(self, ty1, ty2) }
    fn visit_pl_exprs(&mut self, pl_expr1: &PlaceExpr, pl_expr2: &PlaceExpr) {
        walk_pl_exprs(self, pl_expr1, pl_expr2)
    }
    fn visit_arg_kindeds(&mut self, arg_kinded1: &ArgKinded, arg_kinded2: &ArgKinded) {
        walk_arg_kindeds(self, arg_kinded)
    }
    fn visit_kinds(&mut self, _kind1: &Kind, _kind2: &Kind) {}
    fn visit_binary_ops(&mut self, _op1: &BinOp, _op2: &BinOp) {}
    fn visit_unary_ops(&mut self, _op1: &UnOp, _op2: &BinOp) {}
    fn visit_owns(&mut self, _own1: &Ownership, _own2: &Ownership) {}
    fn visit_mutabilities(&mut self, _mutbl1: &Mutability, _mutbl2: &Mutability) {}
    fn visit_lits(&mut self, _lit1: &Lit, _lit2: &Lit) {}
    fn visit_idents(&mut self, _ident1: &Ident, _ident2: &Ident) {}
    fn visit_patterns(&mut self, pattern1: &Pattern, pattern2: &Pattern) {
        walk_patterns(self, pattern1, pattern2)
    }
    fn visit_exprs(&mut self, expr1: &Expr, expr2: &Expr) { walk_exprs(self, expr1, expr2) }
    fn visit_param_decls(&mut self, param_decl1: &ParamDecl, param_decl2: &ParamDecl) {
        walk_param_decls(self, param_decl1, param_decl2)
    }
    fn visit_fun_defs(&mut self, fun_def1: &FunDef, fun_def2: &FunDef) {
        walk_fun_defs(self, fun_def1, fun_def2)
    }
}

macro_rules! walk_lists {
    ($visitor: expr, $method: ident, $list1: expr, $list2: expr) => {
        if $list1.len() != $list2.len() {
            return Err(());
        }
        for (elem1, elem2) in $list1.iter().zip($list2) {
            $visitor.$method(elem1, elem2)
        }
    };
}

pub fn walk_nats<V: VisitSimilar>(visitor: &mut V, n1: &Nat, n2: &Nat) {
    match (n1, n2) {
        (Nat::Ident(ident1), Nat::Ident(ident2)) => visitor.visit_idents(ident1, ident2),
        (Nat::BinOp(op1, l1, r1), Nat::BinOp(op2, l2, r2)) => {
            visitor.visit_binary_op_nats(op1, op2);
            visitor.visit_nats(l1, l2);
            visitor.visit_nats(r1, r2)
        }
        (Nat::Lit(_), Nat::Lit(_)) => {}
        (Nat::App(func1, args1), Nat::App(func2, args2)) => {
            visitor.visit_idents(func1, func2);
            walk_lists!(visitor, visit_nats, args1, args2)
        }
    }
}

pub fn walk_idents_kinded<V: VisitSimilar>(
    visitor: &mut V,
    id_kind1: &IdentKinded,
    id_kind2: &IdentKinded,
) {
    let IdentKinded {
        ident: ident1,
        kind: kind1,
    } = id_kind1;
    let IdentKinded {
        ident: ident2,
        kind: kind2,
    } = id_kind2;
    visitor.visit_idents(ident1, ident2);
    visitor.visit_kinds(kind1, kind2)
}

pub fn walk_prv_rels<V: VisitSimilar>(visitor: &mut V, prv_rel1: &PrvRel, prv_rel2: &PrvRel) {
    let PrvRel {
        longer: longer1,
        shorter: shorter1,
    } = prv_rel1;
    let PrvRel {
        longer: longer2,
        shorter: shorter2,
    } = prv_rel2;
    visitor.visit_idents(longer1, longer2);
    visitor.visit_idents(shorter1, shorter2)
}

pub fn walk_mems<V: VisitSimilar>(visitor: &mut V, mem1: &Memory, mem2: &Memory) {
    if let (Memory::Ident(ident1), Memory::Ident(ident2)) = (mem1, mem2) {
        visitor.visit_idents(ident1, ident2)
    }
}

pub fn walk_prvs<V: VisitSimilar>(visitor: &mut V, prv1: &Provenance, prv2: &Provenance) {
    match (prv1, prv2) {
        (Provenance::Ident(ident1), Provenance::Ident(ident2)) => {
            visitor.visit_idents(ident1, ident2)
        }
        (Provenance::Value(_), Provenance::Value(_)) => {}
    }
}

pub fn walk_th_hierchy<V: VisitSimilar>(
    visitor: &mut V,
    th_hierchy1: &ThreadHierchyTy,
    th_hierchy2: &ThreadHierchyTy,
) {
    match (th_hierchy1, th_hierchy2) {
        (
            ThreadHierchyTy::BlockGrp(ln1, ln2, ln3, lm1, lm2, lm3),
            ThreadHierchyTy::BlockGrp(rn1, rn2, rn3, rm1, rm2, rm3),
        ) => {
            visitor.visit_nats(ln1, rn1);
            visitor.visit_nats(ln2, rn2);
            visitor.visit_nats(ln3, rn3);
            visitor.visit_nats(lm1, rm1);
            visitor.visit_nats(lm2, rm2);
            visitor.visit_nats(lm3, rm3);
        }
        (ThreadHierchyTy::ThreadGrp(ln1, ln2, ln3), ThreadHierchyTy::ThreadGrp(rn1, rn2, rn3)) => {
            visitor.visit_nats(ln1, rn1);
            visitor.visit_nats(ln2, rn2);
            visitor.visit_nats(ln3, rn3);
        }
        (ThreadHierchyTy::WarpGrp(n1), ThreadHierchyTy::WarpGrp(n2)) => visitor.visit_nats(n1, n2),
        (ThreadHierchyTy::Warp, ThreadHierchyTy::Warp) => {}
        (ThreadHierchyTy::Thread, ThreadHierchyTy::Thread) => {}
    }
}

pub fn walk_dtys<V: VisitSimilar>(visitor: &mut V, dty1: &DataTy, dty2: &DataTy) {
    match (&dty1.dty, &dty2.dty) {
        (DataTyKind::Ident(ident1), DataTyKind::Ident(ident2)) => {
            visitor.visit_idents(ident1, ident2)
        }
        (DataTyKind::Scalar(sty1), DataTyKind::Scalar(sty2)) => {
            visitor.visit_scalar_tys(sty1, sty2)
        }
        (DataTyKind::Atomic(aty1), DataTyKind::Atomic(aty2)) => {
            visitor.visit_scalar_tys(aty1, aty2)
        }
        (DataTyKind::ThreadHierchy(th_hy1), DataTyKind::ThreadHierchy(th_hy2)) => {
            visitor.visit_th_hierchys(th_hy1, th_hy2)
        }
        (DataTyKind::Tuple(elem_dtys1), DataTyKind::Tuple(elem_dtys2)) => {
            walk_lists!(visitor, visit_dtys, elem_dtys1, elem_dtys2)
        }
        (DataTyKind::Array(dty1, n1), DataTyKind::Array(dty2, n2)) => {
            visitor.visit_dtys(dty1, dty2);
            visitor.visit_nats(n1, n2)
        }
        (DataTyKind::ArrayShape(dty1, n1), DataTyKind::ArrayShape(dty2, n2)) => {
            visitor.visit_dtys(dty1, dty2);
            visitor.visit_nats(n1, n2);
        }
        (DataTyKind::At(dty1, mem1), DataTyKind::At(dty2, mem2)) => {
            visitor.visit_dtys(dty1, dty2);
            visitor.visit_mems(mem1, mem2)
        }
        (DataTyKind::Ref(prv1, own1, mem1, dty1), DataTyKind::Ref(prv2, own2, mem2, dty2)) => {
            visitor.visit_prvs(prv1, prv2);
            visitor.visit_owns(own1, own2);
            visitor.visit_mems(mem1, mem2);
            visitor.visit_dtys(dty1, dty2)
        }
        (DataTyKind::RawPtr(dty1), DataTyKind::RawPtr(dty2)) => visitor.visit_dtys(dty1, dty2),
        (DataTyKind::Range, DataTyKind::Range) => (),
        (DataTyKind::Dead(dty1), DataTyKind::Dead(dty2)) => visitor.visit_dtys(dty1, dty2),
    }
}

pub fn walk_tys<V: VisitSimilar>(visitor: &mut V, ty1: &Ty, ty2: &Ty) {
    match (&ty1.ty, &ty2.ty) {
        (TyKind::Data(dty1), TyKind::Data(dty2)) => visitor.visit_dtys(dty1, dty2),
        (TyKind::TupleView(elem_tys1), TyKind::TupleView(elem_tys2)) => {
            walk_lists!(visitor, visit_tys, elem_tys1, elem_tys2)
        }
        (
            TyKind::Fn(gen_params1, params1, exec1, ret_ty1),
            TyKind::Fn(gen_params2, params2, exec2, ret_ty2),
        ) => {
            walk_lists!(visitor, visit_idents_kinded, gen_params1, gen_params2);
            walk_lists!(visitor, visit_tys, params1, params2);
            visitor.visit_execs(exec1, exec2);
            visitor.visit_tys(ret_ty1, ret_ty2)
        }
        (TyKind::Ident(ident1), TyKind::Ident(ident2)) => visitor.visit_idents(ident1, ident2),
        (TyKind::Dead(ty1), TyKind::Dead(ty2)) => visitor.visit_tys(ty1, ty2),
    }
}

pub fn walk_pl_exprs<V: VisitSimilar>(visitor: &mut V, pl_expr1: &PlaceExpr, pl_expr2: &PlaceExpr) {
    match (&pl_expr1.pl_expr, &pl_expr2.pl_expr) {
        (PlaceExprKind::Ident(ident1), PlaceExprKind::Ident(ident2)) => {
            visitor.visit_idents(ident1, ident2)
        }
        (PlaceExprKind::Deref(pl_expr1), PlaceExprKind::Deref(pl_expr2)) => {
            visitor.visit_pl_exprs(pl_expr1, pl_expr2)
        }
        (PlaceExprKind::Proj(pl_expr1, _), PlaceExprKind::Proj(pl_expr2, _)) => {
            visitor.visit_pl_exprs(pl_expr1, pl_expr2);
        }
    }
}

pub fn walk_args_kinded<V: VisitSimilar>(
    visitor: &mut V,
    arg_kinded1: &ArgKinded,
    arg_kinded2: &ArgKinded,
) {
    match (arg_kinded1, arg_kinded2) {
        (ArgKinded::Ident(ident1), ArgKinded::Ident(ident2)) => {
            visitor.visit_idents(ident1, ident2)
        }
        (ArgKinded::Nat(n1), ArgKinded::Nat(n2)) => visitor.visit_nats(n1, n2),
        (ArgKinded::Memory(mem1), ArgKinded::Memory(mem2)) => visitor.visit_mems(mem1, mem2),
        (ArgKinded::Ty(ty1), ArgKinded::Ty(ty2)) => visitor.visit_tys(ty1, ty2),
        (ArgKinded::DataTy(dty1), ArgKinded::DataTy(dty2)) => visitor.visit_dtys(dty1, dty2),
        (ArgKinded::Provenance(prv1), ArgKinded::Provenance(prv2)) => {
            visitor.visit_prvs(prv1, prv2)
        }
        _ => report_ueq_args_kinded(arg_kinded1, arg_kinded2),
    }
}

fn report_ueq_args_kinded(arg_kinded1: &ArgKinded, arg_kinded2: &ArgKinded) {
    panic!(
        "{:?} and {:?} have different structures.",
        arg_kinded1, arg_kinded2
    )
}

pub fn walk_patterns<V: VisitSimilar>(visitor: &mut V, pattern1: &Pattern, pattern2: &Pattern) {
    match (pattern1, pattern2) {
        (Pattern::Ident(mutab1, ident1), Pattern::Ident(mutab2, ident2)) => {
            visitor.visit_mutabilities(mutab1, mutab2);
            visitor.visit_idents(ident1, ident2);
        }
        (Pattern::Tuple(patterns1), Pattern::Tuple(patterns2)) => {
            walk_lists!(visitor, visit_patterns, patterns1, patterns2)
        }
        (Pattern::TupleView(patterns1), Pattern::TupleView(patterns2)) => {
            walk_lists!(visitor, visit_patterns, patterns1, patterns2)
        }
        _ => report_ueq_patterns(),
    }
}

fn report_ueq_patterns(pattern1: &Pattern, pattern2: &Pattern) {
    panic!(
        "{:?} and {:?} have different structures.",
        pattern1, pattern2
    )
}

pub fn walk_exprs<V: VisitSimilar>(visitor: &mut V, expr1: &Expr, expr2: &Expr) {
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

pub fn walk_param_decls<V: VisitSimilar>(
    visitor: &mut V,
    param_decl1: &ParamDecl,
    param_decl2: &ParamDecl,
) {
    let ParamDecl { ident, ty, mutbl } = param_decl;
    visitor.visit_ident(ident);
    if let Some(tty) = ty {
        visitor.visit_ty(tty);
    }
    visitor.visit_mutability(mutbl)
}

pub fn walk_fun_defs<V: VisitSimilar>(visitor: &mut V, fun_def1: &FunDef, fun_def2: &FunDef) {
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
