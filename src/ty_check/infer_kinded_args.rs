use super::{TyError, TyResult};
use crate::ast::{
    ArgKinded, BaseExec, DataTy, DataTyKind, Dim, ExecExpr, ExecTy, ExecTyKind, FnTy, Ident,
    Memory, Nat, ParamSig, Provenance, Ty, TyKind,
};
use std::collections::HashMap;

// mono_ty is function type,
//  and since polytype is top-level function type, all (type-level) identifiers must have been
//  introduced by the polymorphic function, therefore finding an identifier on the poly type
//  means that it was introduced by the polymorphic function (even though the identifier may be an
//  instantiation of a bound identifier
pub fn infer_kinded_args(poly_fn_ty: &FnTy, mono_fn_ty: &FnTy) -> TyResult<Vec<ArgKinded>> {
    if poly_fn_ty.param_sigs.len() != mono_fn_ty.param_sigs.len() {
        panic!("Unexpected difference in amount of paramters.")
    }
    let mut res_map = HashMap::new();
    for (subst_ty, mono_ty) in poly_fn_ty.param_sigs.iter().zip(&mono_fn_ty.param_sigs) {
        infer_kargs_param_sig(&mut res_map, subst_ty, mono_ty)
    }
    infer_kargs_exec_expr(&mut res_map, &poly_fn_ty.exec, &mono_fn_ty.exec);
    infer_kargs_tys(&mut res_map, &poly_fn_ty.ret_ty, &mono_fn_ty.ret_ty);
    let mut res_vec = Vec::new();
    for gen_arg in &poly_fn_ty.generics {
        // FIXME unwrap leads to panic when the value for ident could not be inferred
        //  as does happen when the identifier is not used in the argument type or part of
        //  an expression in the case of nats
        if let Some(res_karg) = res_map.get(&gen_arg.ident) {
            if gen_arg.kind != res_karg.kind() {
                panic!("Unexpected: Kinds of identifier and argument do not match.")
            }
            res_vec.push(res_karg.clone());
        } else {
            return Err(TyError::CannotInferGenericArg(gen_arg.ident.clone()));
        }
    }
    Ok(res_vec)
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
        (TyKind::Data(dty1), TyKind::Data(dty2)) => infer_kargs_dtys(map, dty1, dty2),
        (TyKind::FnTy(fn_ty1), TyKind::FnTy(fn_ty2)) => {
            if !fn_ty1.generics.is_empty() || !fn_ty2.generics.is_empty() {
                panic!("Unexpected top-level function type")
            }
            infer_from_lists!(
                infer_kargs_param_sig,
                map,
                &fn_ty1.param_sigs,
                &fn_ty2.param_sigs
            );
            if let (Some(gel), Some(ger)) = (&fn_ty1.generic_exec, &fn_ty2.generic_exec) {
                infer_kargs_exec_level(map, &gel.ty, &ger.ty);
            }
            infer_kargs_exec_expr(map, &fn_ty1.exec, &fn_ty2.exec);
            infer_kargs_tys(map, &fn_ty1.ret_ty, &fn_ty2.ret_ty)
        }
        _ => panic_no_inst!(),
    }
}

fn infer_kargs_param_sig(
    map: &mut HashMap<Ident, ArgKinded>,
    poly_param_sig: &ParamSig,
    mono_param_sig: &ParamSig,
) {
    infer_kargs_exec_expr(map, &poly_param_sig.exec_expr, &mono_param_sig.exec_expr);
    infer_kargs_tys(map, &poly_param_sig.ty, &mono_param_sig.ty);
}

fn infer_kargs_exec_expr(
    map: &mut HashMap<Ident, ArgKinded>,
    poly_exec_expr: &ExecExpr,
    mono_exec_expr: &ExecExpr,
) {
    match (&poly_exec_expr.exec.base, &mono_exec_expr.exec.base) {
        (BaseExec::Ident(i1), BaseExec::Ident(i2)) if i1 == i2 => (),
        (BaseExec::GpuGrid(gdim1, bdim1), BaseExec::GpuGrid(gdim2, bdim2)) => {
            infer_kargs_dims(map, gdim1, gdim2);
            infer_kargs_dims(map, bdim1, bdim2);
        }
        (BaseExec::CpuThread, BaseExec::CpuThread) => {}
        _ => panic_no_inst!(),
    }
}

fn infer_kargs_exec_level(
    map: &mut HashMap<Ident, ArgKinded>,
    poly_exec_level: &ExecTy,
    mono_exec_level: &ExecTy,
) {
    match (&poly_exec_level.ty, &mono_exec_level.ty) {
        (ExecTyKind::GpuGrid(gdim1, bdim1), ExecTyKind::GpuGrid(gdim2, bdim2))
        | (ExecTyKind::GpuBlockGrp(gdim1, bdim1), ExecTyKind::GpuBlockGrp(gdim2, bdim2)) => {
            infer_kargs_dims(map, gdim1, gdim2);
            infer_kargs_dims(map, bdim1, bdim2);
        }
        (ExecTyKind::GpuBlock(dim1), ExecTyKind::GpuBlock(dim2))
        | (ExecTyKind::GpuThreadGrp(dim1), ExecTyKind::GpuThreadGrp(dim2)) => {
            infer_kargs_dims(map, dim1, dim2);
        }
        (ExecTyKind::CpuThread, ExecTyKind::CpuThread)
        | (ExecTyKind::GpuThread, ExecTyKind::GpuThread)
        | (ExecTyKind::Any, ExecTyKind::Any) => {}
        _ => panic_no_inst!(),
    }
}

fn infer_kargs_dims(map: &mut HashMap<Ident, ArgKinded>, poly_dim: &Dim, mono_dim: &Dim) {
    match (poly_dim, mono_dim) {
        (Dim::XYZ(d3d1), Dim::XYZ(d3d2)) => {
            infer_kargs_nats(map, &d3d1.0, &d3d2.0);
            infer_kargs_nats(map, &d3d1.1, &d3d2.1);
            infer_kargs_nats(map, &d3d1.2, &d3d2.2);
        }
        (Dim::XY(d2d1), Dim::XY(d2d2))
        | (Dim::XZ(d2d1), Dim::XZ(d2d2))
        | (Dim::YZ(d2d1), Dim::YZ(d2d2)) => {
            infer_kargs_nats(map, &d2d1.0, &d2d2.0);
            infer_kargs_nats(map, &d2d1.1, &d2d2.1);
        }
        (Dim::X(d1d1), Dim::X(d1d2))
        | (Dim::Y(d1d1), Dim::Y(d1d2))
        | (Dim::Z(d1d1), Dim::Z(d1d2)) => {
            infer_kargs_nats(map, &d1d1.0, &d1d2.0);
        }
        _ => panic_no_inst!(),
    }
}

fn infer_kargs_field(
    map: &mut HashMap<Ident, ArgKinded>,
    poly_field: &(Ident, DataTy),
    mono_field: &(Ident, DataTy),
) {
    infer_kargs_dtys(map, &poly_field.1, &mono_field.1)
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
        (DataTyKind::Struct(struct_decl1), DataTyKind::Struct(struct_decl2)) => {
            infer_from_lists!(
                infer_kargs_field,
                map,
                &struct_decl1.fields,
                &struct_decl2.fields
            )
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
        (DataTyKind::Dead(dty1), DataTyKind::Dead(dty2)) => infer_kargs_dtys(map, dty1, dty2),
        _ => panic_no_inst!(),
    }
}

fn infer_kargs_nats(map: &mut HashMap<Ident, ArgKinded>, poly_nat: &Nat, mono_nat: &Nat) {
    match (poly_nat, mono_nat) {
        (Nat::Ident(id), _) => {
            if let Some(ArgKinded::Nat(old)) =
                map.insert(id.clone(), ArgKinded::Nat(mono_nat.clone()))
            {
                if &old != mono_nat {
                    panic!(
                        "not able to check equality of Nats `{}` and `{}`",
                        old, mono_nat
                    );
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
