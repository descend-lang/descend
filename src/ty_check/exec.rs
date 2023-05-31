use super::{
    BaseExec, Dim, Dim1d, Dim2d, DimCompo, ExecExpr, ExecPathElem, ExecTy, ExecTyKind, IdentExec,
    KindCtx, TyCtx, TyError, TyResult,
};
use crate::ast::{Constraint, Ident, Predicate};

// TODO well-formedness of ExecTy!!!!
pub(super) fn ty_check(
    kind_ctx: &KindCtx,
    ty_ctx: &TyCtx,
    ident_exec: &IdentExec,
    exec_expr: &mut ExecExpr,
) -> TyResult<Constraint> {
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

    let mut constraint = Constraint::Pred(Predicate::True);
    for e in &exec_expr.exec.path {
        match &e {
            ExecPathElem::Distrib(d) => {
                exec_ty = ty_check_exec_distrib(*d, &exec_ty)?;
            }
            ExecPathElem::SplitProj(exec_split) => {
                let (ety, constr) = ty_check_exec_split_proj(
                    exec_split.split_dim,
                    &exec_split.pos,
                    exec_split.proj,
                    &exec_ty,
                )?;
                exec_ty = ety;
                constraint = Constraint::and(constraint, constr);
            }
            ExecPathElem::ToThreads(d) => {
                exec_ty = ty_check_exec_to_threads(*d, &exec_ty)?;
            }
        }
    }
    exec_expr.ty = Some(Box::new(ExecTy::new(exec_ty)));
    Ok(constraint)
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
            return Err(TyError::String(format!("Cannot schedule over {:?}", ex)))
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
    pos: &Ident,
    proj: u8,
    exec_ty: &ExecTyKind,
) -> TyResult<(ExecTyKind, Constraint)> {
    // TODO check well-formedness of Nats
    let (lexec_ty, rexec_ty, constr) = match exec_ty {
        ExecTyKind::GpuGrid(gdim, bdim) | ExecTyKind::GpuBlockGrp(gdim, bdim) => {
            let ((ldim, rdim), constr) = split_dim(d, pos, gdim.clone())?;
            (
                ExecTyKind::GpuBlockGrp(ldim, bdim.clone()),
                ExecTyKind::GpuBlockGrp(rdim, bdim.clone()),
                constr,
            )
        }
        ExecTyKind::GpuBlock(dim) | ExecTyKind::GpuThreadGrp(dim) => {
            let ((ldim, rdim), constr) = split_dim(d, pos, dim.clone())?;
            (
                ExecTyKind::GpuThreadGrp(ldim),
                ExecTyKind::GpuThreadGrp(rdim),
                constr,
            )
        }
        ExecTyKind::GpuGlobalThreads(dim) => {
            let ((ldim, rdim), constr) = split_dim(d, pos, dim.clone())?;
            (
                ExecTyKind::GpuGlobalThreads(ldim),
                ExecTyKind::GpuGlobalThreads(rdim),
                constr,
            )
        }
        ex => {
            return Err(TyError::String(format!(
                "Trying to split non-splittable execution resource: {:?}",
                ex
            )))
        }
    };
    Ok(if proj == 0 {
        (lexec_ty, constr)
    } else {
        (rexec_ty, constr)
    })
}

fn split_dim(split_dim: DimCompo, pos: &Ident, dim: Dim) -> TyResult<((Dim, Dim), Constraint)> {
    let (new_dims, diff) = match dim {
        Dim::XYZ(d) => match split_dim {
            DimCompo::X => {
                let diff = d.0.subtract(Predicate::Ident(pos.clone()));
                (
                    (
                        Dim::new_3d(Predicate::Ident(pos.clone()), d.1.clone(), d.2.clone()),
                        Dim::new_3d(diff.clone(), d.1, d.2),
                    ),
                    diff,
                )
            }
            DimCompo::Y => {
                let diff = d.1.subtract(Predicate::Ident(pos.clone()));
                (
                    (
                        Dim::new_3d(d.0.clone(), Predicate::Ident(pos.clone()), d.2.clone()),
                        Dim::new_3d(d.0, diff.clone(), d.2),
                    ),
                    diff,
                )
            }
            DimCompo::Z => {
                let diff = d.2.subtract(Predicate::Ident(pos.clone()));
                (
                    (
                        Dim::new_3d(d.0.clone(), d.1.clone(), Predicate::Ident(pos.clone())),
                        Dim::new_3d(d.0, d.1, diff.clone()),
                    ),
                    diff,
                )
            }
        },
        Dim::XY(d) => match split_dim {
            DimCompo::X => {
                let diff = d.0.subtract(Predicate::Ident(pos.clone()));
                (
                    (
                        Dim::new_2d(Dim::XY, Predicate::Ident(pos.clone()), d.1.clone()),
                        Dim::new_2d(Dim::XY, diff.clone(), d.1),
                    ),
                    diff,
                )
            }
            DimCompo::Y => {
                let diff = d.1.subtract(Predicate::Ident(pos.clone()));
                (
                    (
                        Dim::new_2d(Dim::XY, d.0.clone(), Predicate::Ident(pos.clone())),
                        Dim::new_2d(Dim::XY, d.0, diff.clone()),
                    ),
                    diff,
                )
            }
            DimCompo::Z => return Err(TyError::IllegalDimension),
        },
        Dim::XZ(d) => match split_dim {
            DimCompo::X => {
                let diff = d.0.subtract(Predicate::Ident(pos.clone()));
                (
                    (
                        Dim::new_2d(Dim::XZ, Predicate::Ident(pos.clone()), d.1.clone()),
                        Dim::new_2d(Dim::XZ, diff.clone(), d.1),
                    ),
                    diff,
                )
            }
            DimCompo::Y => return Err(TyError::IllegalDimension),
            DimCompo::Z => {
                let diff = d.1.subtract(Predicate::Ident(pos.clone()));
                (
                    (
                        Dim::new_2d(Dim::XZ, d.0.clone(), Predicate::Ident(pos.clone())),
                        Dim::new_2d(Dim::XZ, d.0, diff.clone()),
                    ),
                    diff,
                )
            }
        },
        Dim::YZ(d) => match split_dim {
            DimCompo::X => return Err(TyError::IllegalDimension),
            DimCompo::Y => {
                let diff = d.0.subtract(Predicate::Ident(pos.clone()));
                (
                    (
                        Dim::new_2d(Dim::YZ, Predicate::Ident(pos.clone()), d.1.clone()),
                        Dim::new_2d(Dim::YZ, diff.clone(), d.1),
                    ),
                    diff,
                )
            }
            DimCompo::Z => {
                let diff = d.1.subtract(Predicate::Ident(pos.clone()));
                (
                    (
                        Dim::new_2d(Dim::YZ, d.0.clone(), Predicate::Ident(pos.clone())),
                        Dim::new_2d(Dim::YZ, d.0, diff.clone()),
                    ),
                    diff,
                )
            }
        },
        Dim::X(d) => {
            if let DimCompo::X = split_dim {
                let diff = d.0.subtract(Predicate::Ident(pos.clone()));
                (
                    (
                        Dim::new_1d(Dim::X, Predicate::Ident(pos.clone())),
                        Dim::new_1d(Dim::X, diff.clone()),
                    ),
                    diff,
                )
            } else {
                return Err(TyError::IllegalDimension);
            }
        }
        Dim::Y(d) => {
            if let DimCompo::Y = split_dim {
                let diff = d.0.subtract(Predicate::Ident(pos.clone()));
                (
                    (
                        Dim::new_1d(Dim::Y, Predicate::Ident(pos.clone())),
                        Dim::new_1d(Dim::Y, diff.clone()),
                    ),
                    diff,
                )
            } else {
                return Err(TyError::IllegalDimension);
            }
        }
        Dim::Z(d) => {
            if let DimCompo::Z = split_dim {
                let diff = d.0.subtract(Predicate::Ident(pos.clone()));
                (
                    (
                        Dim::new_1d(Dim::Z, Predicate::Ident(pos.clone())),
                        Dim::new_1d(Dim::Z, diff.clone()),
                    ),
                    diff,
                )
            } else {
                return Err(TyError::IllegalDimension);
            }
        }
    };
    let constraint = Constraint::Pred(Predicate::leq(Predicate::Num(0), diff));

    Ok((new_dims, constraint))
}
