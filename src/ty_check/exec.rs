use super::{
    BaseExec, BinOpNat, Dim, Dim1d, Dim2d, DimCompo, ExecExpr, ExecPathElem, ExecTy, ExecTyKind,
    IdentExec, KindCtx, Nat, TyCtx, TyError, TyResult,
};

pub(super) fn ty_check(
    kind_ctx: &KindCtx,
    ty_ctx: &TyCtx,
    ident_exec: &IdentExec,
    exec_expr: &mut ExecExpr,
) -> TyResult<()> {
    let mut exec_ty = match &exec_expr.exec.base {
        BaseExec::Ident(ident) => {
            if ident == &ident_exec.ident {
                ident_exec.ty.ty.clone()
            } else {
                let inline_exec = ty_ctx.get_exec_expr(ident)?;
                inline_exec.ty.as_ref().unwrap().ty.clone()
            }
        }
        BaseExec::CpuThread => ExecTyKind::CpuThread,
        BaseExec::GpuGrid(gdim, bdim) => ExecTyKind::GpuGrid(gdim.clone(), bdim.clone()),
    };

    for e in &exec_expr.exec.path {
        match &e {
            ExecPathElem::Distrib(d) => {
                exec_ty = ty_check_exec_distrib(*d, &exec_ty)?;
            }
            ExecPathElem::SplitProj(exec_split) => {
                exec_ty = ty_check_exec_split_proj(
                    exec_split.split_dim,
                    &exec_split.pos,
                    exec_split.proj,
                    &exec_ty,
                )?;
            }
            ExecPathElem::ToThreads(d) => {
                exec_ty = ty_check_exec_to_threads(*d, &exec_ty)?;
            }
        }
    }
    exec_expr.ty = Some(Box::new(ExecTy::new(exec_ty)));
    Ok(())
}

fn ty_check_exec_to_threads(dim: DimCompo, exec_ty: &ExecTyKind) -> TyResult<ExecTyKind> {
    let result_ty = if let ExecTyKind::GpuGrid(gdim, bdim) = exec_ty {
        // match (gdim, bdim) {
        // }
        ()
    };
    todo!()
}

fn ty_check_exec_distrib(d: DimCompo, exec_ty: &ExecTyKind) -> TyResult<ExecTyKind> {
    let res_ty = match exec_ty {
        ExecTyKind::GpuGrid(gdim, bdim) => {
            let inner_dim = remove_dim(gdim, d)?;
            match inner_dim {
                Some(dim) => ExecTyKind::GpuGrid(dim, bdim.clone()),
                None => ExecTyKind::GpuBlock(bdim.clone()),
            }
        }
        ExecTyKind::GpuBlockGrp(gdim, bdim) => {
            let inner_dim = remove_dim(gdim, d)?;
            match inner_dim {
                Some(dim) => ExecTyKind::GpuBlockGrp(dim, bdim.clone()),
                None => ExecTyKind::GpuBlock(bdim.clone()),
            }
        }
        ExecTyKind::GpuBlock(bdim) => {
            let inner_dim = remove_dim(bdim, d)?;
            match inner_dim {
                Some(dim) => ExecTyKind::GpuBlock(dim),
                None => ExecTyKind::GpuThread,
            }
        }
        ExecTyKind::GpuThreadGrp(tdim) => {
            let inner_dim = remove_dim(tdim, d)?;
            match inner_dim {
                Some(dim) => ExecTyKind::GpuThreadGrp(dim),
                None => ExecTyKind::GpuThread,
            }
        }
        ExecTyKind::GpuGlobalThreads(gdim) => {
            let inner_dim = remove_dim(gdim, d)?;
            match inner_dim {
                Some(dim) => ExecTyKind::GpuGlobalThreads(dim),
                None => ExecTyKind::GpuThread,
            }
        }
        ex @ ExecTyKind::CpuThread | ex @ ExecTyKind::GpuThread | ex @ ExecTyKind::View => {
            return Err(TyError::String(format!("Cannot schedule over {}", ex)))
        }
    };
    Ok(res_ty)
}

pub fn remove_dim(dim: &Dim, dim_compo: DimCompo) -> TyResult<Option<Dim>> {
    match (dim, dim_compo) {
        (Dim::XYZ(dim3d), DimCompo::X) => Ok(Some(Dim::YZ(Box::new(Dim2d(
            dim3d.as_ref().1.clone(),
            dim3d.2.clone(),
        ))))),
        (Dim::XYZ(dim3d), DimCompo::Y) => Ok(Some(Dim::XZ(Box::new(Dim2d(
            dim3d.as_ref().0.clone(),
            dim3d.2.clone(),
        ))))),
        (Dim::XYZ(dim3d), DimCompo::Z) => Ok(Some(Dim::XY(Box::new(Dim2d(
            dim3d.as_ref().0.clone(),
            dim3d.as_ref().1.clone(),
        ))))),
        (Dim::XY(dim2d), DimCompo::X) => {
            Ok(Some(Dim::Y(Box::new(Dim1d(dim2d.as_ref().1.clone())))))
        }
        (Dim::XY(dim2d), DimCompo::Y) => {
            Ok(Some(Dim::X(Box::new(Dim1d(dim2d.as_ref().0.clone())))))
        }
        (Dim::XZ(dim2d), DimCompo::X) => {
            Ok(Some(Dim::Z(Box::new(Dim1d(dim2d.as_ref().1.clone())))))
        }
        (Dim::XZ(dim2d), DimCompo::Z) => {
            Ok(Some(Dim::X(Box::new(Dim1d(dim2d.as_ref().0.clone())))))
        }
        (Dim::YZ(dim2d), DimCompo::Y) => {
            Ok(Some(Dim::Z(Box::new(Dim1d(dim2d.as_ref().1.clone())))))
        }
        (Dim::YZ(dim2d), DimCompo::Z) => {
            Ok(Some(Dim::Y(Box::new(Dim1d(dim2d.as_ref().0.clone())))))
        }
        (Dim::X(_), DimCompo::X) | (Dim::Y(_), DimCompo::Y) | (Dim::Z(_), DimCompo::Z) => Ok(None),
        _ => Err(TyError::IllegalDimension),
    }
}

fn ty_check_exec_split_proj(
    d: DimCompo,
    n: &Nat,
    proj: u8,
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
        ExecTyKind::GpuGlobalThreads(dim) => {
            let (ldim, rdim) = split_dim(d, n.clone(), dim.clone())?;
            (
                ExecTyKind::GpuGlobalThreads(ldim),
                ExecTyKind::GpuGlobalThreads(rdim),
            )
        }
        ex => {
            return Err(TyError::String(format!(
                "Trying to split non-splittable execution resource: {}",
                ex
            )))
        }
    };
    Ok(if proj == 0 { lexec_ty } else { rexec_ty })
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
