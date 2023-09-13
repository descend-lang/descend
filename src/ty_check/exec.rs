use super::{
    BaseExec, BinOpNat, Dim, Dim1d, Dim2d, DimCompo, ExecExpr, ExecPathElem, ExecTy, ExecTyKind,
    IdentExec, KindCtx, Nat, TyCtx, TyError, TyResult,
};
use crate::ast::LeftOrRight;

pub(super) fn ty_check(
    kind_ctx: &KindCtx,
    ty_ctx: &TyCtx,
    ident_exec: Option<&IdentExec>,
    exec_expr: &mut ExecExpr,
) -> TyResult<()> {
    let mut exec_ty = match &exec_expr.exec.base {
        BaseExec::Ident(ident) => {
            if let Some(ie) = ident_exec {
                if ident == &ie.ident {
                    ie.ty.ty.clone()
                } else {
                    let inline_exec = ty_ctx.get_exec_expr(ident)?;
                    inline_exec.ty.as_ref().unwrap().ty.clone()
                }
            } else {
                return Err(TyError::IllegalExec);
            }
        }
        BaseExec::CpuThread => ExecTyKind::CpuThread,
        BaseExec::GpuGrid(gdim, bdim) => ExecTyKind::GpuGrid(gdim.clone(), bdim.clone()),
    };

    for e in &exec_expr.exec.path {
        match e {
            ExecPathElem::ForAll(d) => {
                exec_ty = ty_check_exec_forall(*d, &exec_ty)?;
            }
            ExecPathElem::TakeRange(exec_split) => {
                exec_ty = ty_check_exec_take_range(
                    exec_split.split_dim,
                    &exec_split.pos,
                    exec_split.left_or_right,
                    &exec_ty,
                )?;
            }
            ExecPathElem::ToThreads(d) => {
                exec_ty = ty_check_exec_to_threads(*d, &exec_ty)?;
            }
            ExecPathElem::ToWarps => exec_ty = ty_check_exec_to_warps(&exec_ty)?,
        }
    }
    exec_expr.ty = Some(Box::new(ExecTy::new(exec_ty)));
    Ok(())
}

fn ty_check_exec_to_threads(d: DimCompo, exec_ty: &ExecTyKind) -> TyResult<ExecTyKind> {
    if let ExecTyKind::GpuGrid(gdim, bdim) = exec_ty {
        let (rest_gdim, rem_gdim) = remove_dim(gdim, d)?;
        let (rest_bdim, rem_bdim) = remove_dim(bdim, d)?;
        let global_dim = match (rem_gdim, rem_bdim) {
            (Dim::X(g), Dim::X(b)) => Dim::X(Box::new(Dim1d(Nat::BinOp(
                BinOpNat::Mul,
                Box::new(g.0),
                Box::new(b.0),
            )))),
            (Dim::Y(g), Dim::Y(b)) => Dim::Y(Box::new(Dim1d(Nat::BinOp(
                BinOpNat::Mul,
                Box::new(g.0),
                Box::new(b.0),
            )))),
            (Dim::Z(g), Dim::Z(b)) => Dim::Z(Box::new(Dim1d(Nat::BinOp(
                BinOpNat::Mul,
                Box::new(g.0),
                Box::new(b.0),
            )))),
            _ => {
                return Err(TyError::String(format!(
                    "Provided dimension {} does not exist",
                    d
                )))
            }
        };
        match (rest_gdim, rest_bdim) {
            (Some(rest_gdim), Some(rest_bdim)) => Ok(ExecTyKind::GpuToThreads(
                global_dim,
                Box::new(ExecTy::new(ExecTyKind::GpuBlockGrp(rest_gdim, rest_bdim))),
            )),
            _ => unimplemented!(),
        }
    } else {
        Err(TyError::UnexpectedType)
    }
}

fn ty_check_exec_to_warps(exec_ty: &ExecTyKind) -> TyResult<ExecTyKind> {
    match exec_ty {
        ExecTyKind::GpuBlock(dim) => match dim.clone() {
            Dim::X(d) => {
                // FIXME the comparison of Nats is not evaluated
                if Nat::BinOp(BinOpNat::Mod, Box::new(d.0.clone()), Box::new(Nat::Lit(32)))
                    != Nat::Lit(0)
                {
                    Err(TyError::String(format!(
                        "Size of GpuBlock needs to be evenly divisible by 32 to create warps, instead got: {:?}",
                        exec_ty
                    )))
                } else {
                    Ok(ExecTyKind::GpuWarpGrp(Nat::BinOp(
                        BinOpNat::Div,
                        Box::new(d.0),
                        Box::new(Nat::Lit(32)),
                    )))
                }
            }
            _ => Err(TyError::String(format!(
                "GpuBlock needs to be one-dimensional to create warps, instead got: {:?}",
                exec_ty
            ))),
        },
        _ => Err(TyError::String(format!(
            "Trying to create warps from {:?}",
            exec_ty
        ))),
    }
}

fn ty_check_exec_forall(d: DimCompo, exec_ty: &ExecTyKind) -> TyResult<ExecTyKind> {
    let res_ty = match exec_ty {
        ExecTyKind::GpuGrid(gdim, bdim) => {
            let inner_dim = remove_dim(gdim, d)?.0;
            match inner_dim {
                Some(dim) => ExecTyKind::GpuGrid(dim, bdim.clone()),
                None => ExecTyKind::GpuBlock(bdim.clone()),
            }
        }
        ExecTyKind::GpuBlockGrp(gdim, bdim) => {
            let inner_dim = remove_dim(gdim, d)?.0;
            match inner_dim {
                Some(dim) => ExecTyKind::GpuBlockGrp(dim, bdim.clone()),
                None => ExecTyKind::GpuBlock(bdim.clone()),
            }
        }
        ExecTyKind::GpuBlock(bdim) => {
            let inner_dim = remove_dim(bdim, d)?.0;
            match inner_dim {
                Some(dim) => ExecTyKind::GpuBlock(dim),
                None => ExecTyKind::GpuThread,
            }
        }
        ExecTyKind::GpuThreadGrp(tdim) => {
            let inner_dim = remove_dim(tdim, d)?.0;
            match inner_dim {
                Some(dim) => ExecTyKind::GpuThreadGrp(dim),
                None => ExecTyKind::GpuThread,
            }
        }
        ExecTyKind::GpuWarpGrp(_) => ExecTyKind::GpuWarp,
        ExecTyKind::GpuWarp => ExecTyKind::GpuThread,
        ExecTyKind::GpuToThreads(dim, inner_exec) => {
            if dim_compo_matches_dim(d, dim) {
                inner_exec.ty.clone()
            } else {
                let forall_inner = ty_check_exec_forall(d, &inner_exec.ty)?;
                ExecTyKind::GpuToThreads(dim.clone(), Box::new(ExecTy::new(forall_inner)))
            }
        }
        ex @ ExecTyKind::CpuThread | ex @ ExecTyKind::GpuThread | ex @ ExecTyKind::Any => {
            return Err(TyError::String(format!("Cannot schedule over {:?}", ex)))
        }
    };
    Ok(res_ty)
}

pub fn remove_dim(dim: &Dim, dim_compo: DimCompo) -> TyResult<(Option<Dim>, Dim)> {
    match (dim, dim_compo) {
        (Dim::XYZ(dim3d), DimCompo::X) => Ok((
            Some(Dim::YZ(Box::new(Dim2d(
                dim3d.as_ref().1.clone(),
                dim3d.2.clone(),
            )))),
            Dim::X(Box::new(Dim1d(dim3d.0.clone()))),
        )),
        (Dim::XYZ(dim3d), DimCompo::Y) => Ok((
            Some(Dim::XZ(Box::new(Dim2d(
                dim3d.as_ref().0.clone(),
                dim3d.2.clone(),
            )))),
            Dim::Y(Box::new(Dim1d(dim3d.1.clone()))),
        )),
        (Dim::XYZ(dim3d), DimCompo::Z) => Ok((
            Some(Dim::XY(Box::new(Dim2d(
                dim3d.as_ref().0.clone(),
                dim3d.as_ref().1.clone(),
            )))),
            Dim::Z(Box::new(Dim1d(dim3d.2.clone()))),
        )),
        (Dim::XY(dim2d), DimCompo::X) => Ok((
            Some(Dim::Y(Box::new(Dim1d(dim2d.as_ref().1.clone())))),
            Dim::X(Box::new(Dim1d(dim2d.0.clone()))),
        )),
        (Dim::XY(dim2d), DimCompo::Y) => Ok((
            Some(Dim::X(Box::new(Dim1d(dim2d.as_ref().0.clone())))),
            Dim::Y(Box::new(Dim1d(dim2d.1.clone()))),
        )),
        (Dim::XZ(dim2d), DimCompo::X) => Ok((
            Some(Dim::Z(Box::new(Dim1d(dim2d.as_ref().1.clone())))),
            Dim::X(Box::new(Dim1d(dim2d.0.clone()))),
        )),
        (Dim::XZ(dim2d), DimCompo::Z) => Ok((
            Some(Dim::X(Box::new(Dim1d(dim2d.as_ref().0.clone())))),
            Dim::Z(Box::new(Dim1d(dim2d.1.clone()))),
        )),
        (Dim::YZ(dim2d), DimCompo::Y) => Ok((
            Some(Dim::Z(Box::new(Dim1d(dim2d.as_ref().1.clone())))),
            Dim::Y(Box::new(Dim1d(dim2d.0.clone()))),
        )),
        (Dim::YZ(dim2d), DimCompo::Z) => Ok((
            Some(Dim::Y(Box::new(Dim1d(dim2d.as_ref().0.clone())))),
            Dim::Z(Box::new(Dim1d(dim2d.1.clone()))),
        )),
        (Dim::X(_), DimCompo::X) | (Dim::Y(_), DimCompo::Y) | (Dim::Z(_), DimCompo::Z) => {
            Ok((None, dim.clone()))
        }
        _ => Err(TyError::IllegalDimension),
    }
}

fn ty_check_exec_take_range(
    d: DimCompo,
    n: &Nat,
    proj: LeftOrRight,
    exec_ty: &ExecTyKind,
) -> TyResult<ExecTyKind> {
    // TODO check well-formedness of Nats
    let (lexec_ty, rexec_ty) = match exec_ty {
        ExecTyKind::GpuGrid(gdim, bdim) | ExecTyKind::GpuBlockGrp(gdim, bdim) => {
            let (ldim, rdim) = split_dim(d, n.clone(), gdim.clone())?;
            (
                ExecTyKind::GpuBlockGrp(ldim, bdim.clone()),
                ExecTyKind::GpuBlockGrp(rdim, bdim.clone()),
            )
        }
        ExecTyKind::GpuBlock(dim) | ExecTyKind::GpuThreadGrp(dim) => {
            let (ldim, rdim) = split_dim(d, n.clone(), dim.clone())?;
            (
                ExecTyKind::GpuThreadGrp(ldim),
                ExecTyKind::GpuThreadGrp(rdim),
            )
        }
        ExecTyKind::GpuToThreads(dim, inner) => {
            if dim_compo_matches_dim(d, dim) {
                let (ldim, rdim) = split_dim(d, n.clone(), dim.clone())?;
                (
                    ExecTyKind::GpuToThreads(ldim, inner.clone()),
                    ExecTyKind::GpuToThreads(rdim, inner.clone()),
                )
            } else if let ExecTyKind::GpuBlockGrp(gdim, bdim) = &inner.ty {
                let (ldim, rdim) = split_dim(d, n.clone(), gdim.clone())?;
                (
                    ExecTyKind::GpuToThreads(
                        dim.clone(),
                        Box::new(ExecTy::new(ExecTyKind::GpuBlockGrp(ldim, bdim.clone()))),
                    ),
                    ExecTyKind::GpuToThreads(
                        dim.clone(),
                        Box::new(ExecTy::new(ExecTyKind::GpuBlockGrp(rdim, bdim.clone()))),
                    ),
                )
            } else {
                panic!("GpuToThreads is not well-formed.")
            }
        }
        ex => {
            return Err(TyError::String(format!(
                "Trying to split non-splittable execution resource: {:?}",
                ex
            )))
        }
    };
    Ok(if proj == LeftOrRight::Left {
        lexec_ty
    } else {
        rexec_ty
    })
}

fn dim_compo_matches_dim(d: DimCompo, dim: &Dim) -> bool {
    (matches!(dim, Dim::X(_)) && d == DimCompo::X)
        | (matches!(dim, Dim::Y(_)) && d == DimCompo::Y)
        | (matches!(dim, Dim::Z(_)) && d == DimCompo::Z)
}

fn split_dim(split_dim: DimCompo, pos: Nat, dim: Dim) -> TyResult<(Dim, Dim)> {
    Ok(match dim {
        Dim::XYZ(d) => match split_dim {
            DimCompo::X => (
                Dim::new_3d(pos.clone(), d.1.clone(), d.2.clone()),
                Dim::new_3d(
                    Nat::BinOp(BinOpNat::Sub, Box::new(d.0), Box::new(pos)),
                    d.1,
                    d.2,
                ),
            ),
            DimCompo::Y => (
                Dim::new_3d(d.0.clone(), pos.clone(), d.2.clone()),
                Dim::new_3d(
                    d.0,
                    Nat::BinOp(BinOpNat::Sub, Box::new(d.1), Box::new(pos)),
                    d.2,
                ),
            ),
            DimCompo::Z => (
                Dim::new_3d(d.0.clone(), d.1.clone(), pos.clone()),
                Dim::new_3d(
                    d.0,
                    d.1,
                    Nat::BinOp(BinOpNat::Sub, Box::new(d.2), Box::new(pos)),
                ),
            ),
        },
        Dim::XY(d) => match split_dim {
            DimCompo::X => (
                Dim::new_2d(Dim::XY, pos.clone(), d.1.clone()),
                Dim::new_2d(
                    Dim::XY,
                    Nat::BinOp(BinOpNat::Sub, Box::new(d.0), Box::new(pos)),
                    d.1,
                ),
            ),
            DimCompo::Y => (
                Dim::new_2d(Dim::XY, d.0.clone(), pos.clone()),
                Dim::new_2d(
                    Dim::XY,
                    d.0,
                    Nat::BinOp(BinOpNat::Sub, Box::new(d.1), Box::new(pos)),
                ),
            ),
            DimCompo::Z => return Err(TyError::IllegalDimension),
        },
        Dim::XZ(d) => match split_dim {
            DimCompo::X => (
                Dim::new_2d(Dim::XZ, pos.clone(), d.1.clone()),
                Dim::new_2d(
                    Dim::XZ,
                    Nat::BinOp(BinOpNat::Sub, Box::new(d.0), Box::new(pos)),
                    d.1,
                ),
            ),
            DimCompo::Y => return Err(TyError::IllegalDimension),
            DimCompo::Z => (
                Dim::new_2d(Dim::XZ, d.0.clone(), pos.clone()),
                Dim::new_2d(
                    Dim::XZ,
                    d.0,
                    Nat::BinOp(BinOpNat::Sub, Box::new(d.1), Box::new(pos)),
                ),
            ),
        },
        Dim::YZ(d) => match split_dim {
            DimCompo::X => return Err(TyError::IllegalDimension),
            DimCompo::Y => (
                Dim::new_2d(Dim::YZ, pos.clone(), d.1.clone()),
                Dim::new_2d(
                    Dim::YZ,
                    Nat::BinOp(BinOpNat::Sub, Box::new(d.0), Box::new(pos)),
                    d.1,
                ),
            ),
            DimCompo::Z => (
                Dim::new_2d(Dim::YZ, d.0.clone(), pos.clone()),
                Dim::new_2d(
                    Dim::YZ,
                    d.0,
                    Nat::BinOp(BinOpNat::Sub, Box::new(d.1), Box::new(pos)),
                ),
            ),
        },
        Dim::X(d) => {
            if let DimCompo::X = split_dim {
                (
                    Dim::new_1d(Dim::X, pos.clone()),
                    Dim::new_1d(
                        Dim::X,
                        Nat::BinOp(BinOpNat::Sub, Box::new(d.0), Box::new(pos)),
                    ),
                )
            } else {
                return Err(TyError::IllegalDimension);
            }
        }
        Dim::Y(d) => {
            if let DimCompo::Y = split_dim {
                (
                    Dim::new_1d(Dim::Y, pos.clone()),
                    Dim::new_1d(
                        Dim::Y,
                        Nat::BinOp(BinOpNat::Sub, Box::new(d.0), Box::new(pos)),
                    ),
                )
            } else {
                return Err(TyError::IllegalDimension);
            }
        }
        Dim::Z(d) => {
            if let DimCompo::Z = split_dim {
                (
                    Dim::new_1d(Dim::Z, pos.clone()),
                    Dim::new_1d(
                        Dim::Z,
                        Nat::BinOp(BinOpNat::Sub, Box::new(d.0), Box::new(pos)),
                    ),
                )
            } else {
                return Err(TyError::IllegalDimension);
            }
        }
    })
}

fn update_encountered_dims(forall_dims_encountered: &mut Vec<DimCompo>, e: &ExecPathElem) {
    if let ExecPathElem::ForAll(d) = e {
        if forall_dims_encountered.contains(d) {
            forall_dims_encountered.clear();
            forall_dims_encountered.push(*d);
        }
    }
}

fn swappable_exec_path_elems(
    dims_encountered: &[DimCompo],
    lhs: &ExecPathElem,
    rhs: &ExecPathElem,
) -> bool {
    match (lhs, rhs) {
        (ExecPathElem::ForAll(dl), ExecPathElem::ForAll(dr)) => dl > dr,
        (ExecPathElem::ForAll(_), ExecPathElem::TakeRange(r)) => {
            !dims_encountered.contains(&r.split_dim)
        }
        _ => false,
    }
}

fn normalize(mut exec_path: Vec<ExecPathElem>) -> Vec<ExecPathElem> {
    let mut forall_dims_encountered = Vec::with_capacity(3);
    for i in 0..exec_path.len() - 1 {
        for j in 0..exec_path.len() - i - 1 {
            update_encountered_dims(&mut forall_dims_encountered, &exec_path[j]);
            update_encountered_dims(&mut forall_dims_encountered, &exec_path[j + 1]);
            if swappable_exec_path_elems(&forall_dims_encountered, &exec_path[j], &exec_path[j + 1])
            {
                exec_path.swap(j, j + 1)
            }
        }
    }
    exec_path
}
