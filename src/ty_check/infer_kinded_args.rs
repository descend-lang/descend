use crate::ast::{
    ArgKinded, DataTy, DataTyKind, Ident, IdentKinded, Memory, Nat, Provenance, Ty, TyKind,
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
    if let TyKind::FnTy(mono_fn_ty) = &mono_ty.ty {
        if mono_fn_ty.param_tys.len() != subst_param_tys.len() {
            panic!("Unexpected difference in amount of paramters.")
        }
        let mut res_map = HashMap::new();
        for (subst_ty, mono_ty) in subst_param_tys.iter().zip(&mono_fn_ty.param_tys) {
            infer_kargs_tys(&mut res_map, subst_ty, mono_ty)
        }
        infer_kargs_tys(&mut res_map, subst_ret_ty, &mono_fn_ty.ret_ty);
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
        (TyKind::FnTy(fn_ty1), TyKind::FnTy(fn_ty2)) => {
            if !fn_ty1.generics.is_empty() || !fn_ty2.generics.is_empty() {
                panic!("Unexpected top-level function type.")
            }
            infer_from_lists!(infer_kargs_tys, map, &fn_ty1.param_tys, &fn_ty2.param_tys);
            panic_if_neq!(fn_ty1.exec_ty, fn_ty2.exec_ty);
            infer_kargs_tys(map, &fn_ty1.ret_ty, &fn_ty2.ret_ty)
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
        (DataTyKind::Ref(reff1), DataTyKind::Ref(reff2)) => {
            infer_kargs_prvs(map, &reff1.rgn, &reff2.rgn);
            panic_if_neq!(reff1.own, reff2.own);
            infer_kargs_mems(map, &reff1.mem, &reff2.mem);
            infer_kargs_dtys(map, &reff1.dty, &reff2.dty);
        }
        (DataTyKind::RawPtr(dty1), DataTyKind::RawPtr(dty2)) => infer_kargs_dtys(map, dty1, dty2),
        (DataTyKind::Range, DataTyKind::Range) => (),
        (DataTyKind::Dead(dty1), DataTyKind::Dead(dty2)) => infer_kargs_dtys(map, dty1, dty2),
        _ => panic_no_inst!(),
    }
}

// TODO remove? or is this required somewhere?
// fn infer_dim(map: &mut HashMap<Ident, ArgKinded>, poly_dim: &Dim, mono_dim: &Dim) {
//     match (poly_dim, mono_dim) {
//         (Dim::XYZ(diml), Dim::XYZ(dimr)) => {
//             infer_kargs_nats(map, &diml.0, &dimr.0);
//             infer_kargs_nats(map, &diml.1, &dimr.1);
//             infer_kargs_nats(map, &diml.2, &dimr.2);
//         }
//         (Dim::XY(diml), Dim::XY(dimr))
//         | (Dim::XZ(diml), Dim::XZ(dimr))
//         | (Dim::YZ(diml), Dim::YZ(dimr)) => {
//             infer_kargs_nats(map, &diml.0, &dimr.0);
//             infer_kargs_nats(map, &diml.1, &dimr.1);
//         }
//         (Dim::X(diml), Dim::X(dimr))
//         | (Dim::Y(diml), Dim::Y(dimr))
//         | (Dim::Z(diml), Dim::Z(dimr)) => infer_kargs_nats(map, &diml.0, &dimr.0),
//         _ => panic!("Unexpected: mono type is not an instantiation of poly type"),
//     }
// }

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
            infer_from_lists!(infer_kargs_nats, map, args1, args2.iter());
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
