use crate::ast::{
    ArgKinded, DataTy, DataTyKind, Ident, IdentKinded, Memory, Nat, Provenance, ThreadHierchyTy,
    Ty, TyKind,
};
use std::collections::HashMap;

// monot_ty is function type,
//  and since polytype is top-level function type, all (type-level) identifiers must have been
//  introduced by the polymorphic function, therefore finding an identifier on the lhs means that
//  it was introduced by the polymorphic function
pub fn infer_kinded_args_from_mono_ty(
    remain_gen_args: Vec<IdentKinded>,
    subst_param_tys: Vec<Ty>,
    subst_ret_ty: &Ty,
    mono_ty: &Ty,
) -> Vec<ArgKinded> {
    if let TyKind::Fn(_, _, mono_param_tys, _, mono_ret_ty) = &mono_ty.ty {
        if mono_param_tys.len() != subst_param_tys.len() {
            panic!("Unexpected difference in amount of paramters.")
        }
        let mut res_map = HashMap::new();
        for (subst_ty, mono_ty) in subst_param_tys.iter().zip(mono_param_tys) {
            infer_kargs_tys(&mut res_map, subst_ty, mono_ty)
        }
        infer_kargs_tys(&mut res_map, subst_ret_ty, mono_ret_ty);
        let mut res_vec = Vec::new();
        for gen_arg in remain_gen_args {
            let res_karg = res_map.get(&gen_arg.ident).unwrap();
            if gen_arg.kind != res_karg.kind() {
                panic!("Unexpected: Kinds of identifier and argument do not match.")
            }
            res_vec.push(res_karg.clone());
        }
        res_vec
    } else {
        panic!("Expected function type.")
    }
}

macro_rules! infer_from_lists {
    ($method: ident, $map: expr, $list1: expr, $list2: expr) => {
        for (elem1, elem2) in $list1.iter().zip($list2) {
            $method($map, elem1, elem2)
        }
    };
}

macro_rules! insert_checked {
    ($map: expr, $constr: path, $id_ref: expr, $mono_ref: expr) => {{
        let arg_kinded = $constr($mono_ref.clone());
        if let Some(old) = $map.insert($id_ref.clone(), arg_kinded.clone()) {
            if old != arg_kinded {
                println!("old: {:?}", old);
                println!("new: {:?}", arg_kinded);
                panic!("Found different terms for same identifier in mono type.")
            }
        }
    }};
}

macro_rules! panic_no_inst {
    () => {
        panic!("Unexpected: mono type is not an instantiation of poly type")
    };
}
macro_rules! panic_if_neq {
    ($lhs: expr, $rhs: expr) => {
        if $lhs != $rhs {
            panic_no_inst!();
        }
    };
}

fn infer_kargs_tys(map: &mut HashMap<Ident, ArgKinded>, poly_ty: &Ty, mono_ty: &Ty) {
    match (&poly_ty.ty, &mono_ty.ty) {
        (TyKind::Ident(id), _) => insert_checked!(map, ArgKinded::Ty, id, mono_ty),
        (TyKind::Data(dty1), TyKind::Data(dty2)) => infer_kargs_dtys(map, dty1, dty2),
        (
            TyKind::Fn(gen_params1, cons1, params1, exec1, ret_ty1),
            TyKind::Fn(gen_params2, cons2, params2, exec2, ret_ty2),
        ) => {
            if !gen_params1.is_empty() || !gen_params2.is_empty() {
                panic!("Unexpected top-level function type.")
            }
            assert!(cons1.len() == 0 && cons2.len() == 0);
            infer_from_lists!(infer_kargs_tys, map, params1, params2);
            panic_if_neq!(exec1, exec2);
            infer_kargs_tys(map, ret_ty1, ret_ty2)
        }
        (TyKind::Dead(ty1), TyKind::Dead(ty2)) => infer_kargs_tys(map, ty1, ty2),
        _ => panic_no_inst!(),
    }
}

fn infer_kargs_dtys(map: &mut HashMap<Ident, ArgKinded>, poly_dty: &DataTy, mono_dty: &DataTy) {
    match (&poly_dty.dty, &mono_dty.dty) {
        (DataTyKind::Ident(id), _) => insert_checked!(map, ArgKinded::DataTy, id, mono_dty),
        (DataTyKind::Scalar(sty1), DataTyKind::Scalar(sty2)) => {
            panic_if_neq!(sty1, sty2);
        }
        (DataTyKind::Atomic(sty1), DataTyKind::Atomic(sty2)) => {
            panic_if_neq!(sty1, sty2);
        }
        (DataTyKind::ThreadHierchy(th_hy1), DataTyKind::ThreadHierchy(th_hy2)) => {
            infer_kargs_th_hierchies(map, th_hy1, th_hy2)
        }
        (DataTyKind::Tuple(elem_dtys1), DataTyKind::Tuple(elem_dtys2)) => {
            infer_from_lists!(infer_kargs_dtys, map, elem_dtys1, elem_dtys2)
        }
        (DataTyKind::Array(dty1, n1), DataTyKind::Array(dty2, n2)) => {
            infer_kargs_dtys(map, dty1, dty2);
            infer_kargs_nats(map, n1, n2);
        }
        (DataTyKind::ArrayShape(dty1, n1), DataTyKind::ArrayShape(dty2, n2)) => {
            infer_kargs_dtys(map, dty1, dty2);
            infer_kargs_nats(map, n1, n2);
        }
        (DataTyKind::At(dty1, mem1), DataTyKind::At(dty2, mem2)) => {
            infer_kargs_dtys(map, dty1, dty2);
            infer_kargs_mems(map, mem1, mem2);
        }
        (DataTyKind::Ref(prv1, own1, mem1, dty1), DataTyKind::Ref(prv2, own2, mem2, dty2)) => {
            infer_kargs_prvs(map, prv1, prv2);
            panic_if_neq!(own1, own2);
            infer_kargs_mems(map, mem1, mem2);
            infer_kargs_dtys(map, dty1, dty2);
        }
        (DataTyKind::RawPtr(dty1), DataTyKind::RawPtr(dty2)) => infer_kargs_dtys(map, dty1, dty2),
        (DataTyKind::Range, DataTyKind::Range) => (),
        (DataTyKind::Dead(dty1), DataTyKind::Dead(dty2)) => infer_kargs_dtys(map, dty1, dty2),
        _ => panic_no_inst!(),
    }
}

fn infer_kargs_th_hierchies(
    map: &mut HashMap<Ident, ArgKinded>,
    poly_hierchy: &ThreadHierchyTy,
    mono_hierchy: &ThreadHierchyTy,
) {
    match (poly_hierchy, mono_hierchy) {
        (
            ThreadHierchyTy::BlockGrp(ln1, ln2, ln3, lm1, lm2, lm3),
            ThreadHierchyTy::BlockGrp(rn1, rn2, rn3, rm1, rm2, rm3),
        ) => {
            infer_kargs_nats(map, ln1, rn1);
            infer_kargs_nats(map, ln2, rn2);
            infer_kargs_nats(map, ln3, rn3);
            infer_kargs_nats(map, lm1, rm1);
            infer_kargs_nats(map, lm2, rm2);
            infer_kargs_nats(map, lm3, rm3);
        }
        (ThreadHierchyTy::ThreadGrp(ln1, ln2, ln3), ThreadHierchyTy::ThreadGrp(rn1, rn2, rn3)) => {
            infer_kargs_nats(map, ln1, rn1);
            infer_kargs_nats(map, ln2, rn2);
            infer_kargs_nats(map, ln3, rn3);
        }
        (ThreadHierchyTy::WarpGrp(n1), ThreadHierchyTy::WarpGrp(n2)) => {
            infer_kargs_nats(map, n1, n2)
        }
        (ThreadHierchyTy::Warp, ThreadHierchyTy::Warp) => {}
        (ThreadHierchyTy::Thread, ThreadHierchyTy::Thread) => {}
        _ => panic!("Unexpected: mono type is not an instantiation of poly type"),
    }
}

fn infer_kargs_nats(map: &mut HashMap<Ident, ArgKinded>, poly_nat: &Nat, mono_nat: &Nat) {
    match (poly_nat, mono_nat) {
        (Nat::Ident(id), _) => {
            if let Some(ArgKinded::Nat(old)) =
                map.insert(id.clone(), ArgKinded::Nat(mono_nat.clone()))
            {
                if &old != mono_nat {
                    println!(
                        "WARNING: Not able to check equality of Nats `{}` and `{}`",
                        old, mono_nat
                    );
                    println!("Possibly attempting to bind two unqueal nats to same identifier.")
                }
            }
        }
        (Nat::BinOp(op1, l1, r1), Nat::BinOp(op2, l2, r2)) => {
            panic_if_neq!(op1, op2);
            infer_kargs_nats(map, l1, l2);
            infer_kargs_nats(map, r1, r2);
        }
        (Nat::Lit(l1), Nat::Lit(l2)) => panic_if_neq!(l1, l2),
        (Nat::App(func1, args1), Nat::App(func2, args2)) => {
            panic_if_neq!(func1, func2);
            infer_from_lists!(infer_kargs_nats, map, args1, args2);
        }
        _ => panic_no_inst!(),
    }
}

fn infer_kargs_mems(map: &mut HashMap<Ident, ArgKinded>, poly_mem: &Memory, mono_mem: &Memory) {
    match (poly_mem, mono_mem) {
        (Memory::Ident(id), _) => insert_checked!(map, ArgKinded::Memory, id, mono_mem),
        _ => panic_if_neq!(poly_mem, mono_mem),
    }
}

fn infer_kargs_prvs(
    map: &mut HashMap<Ident, ArgKinded>,
    poly_prv: &Provenance,
    mono_prv: &Provenance,
) {
    match (poly_prv, mono_prv) {
        (Provenance::Ident(id), _) => insert_checked!(map, ArgKinded::Provenance, id, mono_prv),
        _ => panic_if_neq!(poly_prv, mono_prv),
    }
}
