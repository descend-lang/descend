use super::{
    BaseExec, BinOpNat, Dim, Dim1d, Dim2d, DimCompo, ExecExpr, ExecPathElem, ExecTy, ExecTyKind,
    IdentExec, Nat, TyCtx, TyError, TyResult,
};
use crate::arena_ast::{ExecExprKind, LeftOrRight, NatCtx};
use bumpalo::{collections::Vec as BumpVec, Bump};

pub(super) fn ty_check<'a>(
    nat_ctx: &'a NatCtx<'a>,
    ty_ctx: &'a TyCtx<'a>,
    ident_exec: Option<&'a IdentExec<'a>>,
    exec_expr: &mut ExecExpr<'a>,
    arena: &'a Bump,
) -> TyResult<'a, ()> {
    // 1) compute the base kind
    let exec_kind = match &exec_expr.exec.base {
        BaseExec::Ident(ident) => {
            if let Some(ie) = ident_exec {
                if ident == &ie.ident {
                    ie.ty.ty.clone()
                } else {
                    let inline = ty_ctx.get_exec_expr_for_exec_ident(ident)?;
                    inline.ty.as_ref().unwrap().ty.clone()
                }
            } else {
                return Err(TyError::IllegalExec);
            }
        }
        BaseExec::CpuThread => ExecTyKind::CpuThread,
        BaseExec::GpuGrid(gdim, bdim) => ExecTyKind::GpuGrid((**gdim).clone(), (**bdim).clone()),
    };

    // 2) Bump‐allocate that base kind so we have &'a ExecTyKind
    let mut kind_ref: &'a ExecTyKind = &arena.alloc(ExecTy::new(exec_kind.clone())).ty;

    // 3) For each step, work entirely with arena‐owned refs
    for step in &exec_expr.exec.path {
        // call the helper on an arena‐live reference
        let next_kind: ExecTyKind = match step {
            ExecPathElem::ForAll(d) => ty_check_exec_forall(*d, kind_ref, arena)?,
            ExecPathElem::TakeRange(sp) => {
                ty_check_exec_take_range(sp.split_dim, &sp.pos, sp.left_or_right, kind_ref, arena)?
            }
            ExecPathElem::ToThreads(d) => ty_check_exec_to_threads(*d, kind_ref, arena)?,
            ExecPathElem::ToWarps => ty_check_exec_to_warps(nat_ctx, kind_ref, arena)?,
        };
        // Now bump‐allocate the returned kind, update our ref
        let boxed = arena.alloc(ExecTy::new(next_kind));
        kind_ref = &boxed.ty;
    }

    // 4) Finally write out the fully‐elaborated type
    exec_expr.ty = Some(arena.alloc(ExecTy::new(kind_ref.clone())));

    Ok(())
}

fn ty_check_exec_to_threads<'a>(
    d: DimCompo,
    exec_ty: &'a ExecTyKind<'a>,
    arena: &'a Bump,
) -> TyResult<'a, ExecTyKind<'a>> {
    if let ExecTyKind::GpuGrid(gdim, bdim) = exec_ty {
        let (rest_gdim, rem_gdim) = remove_dim(gdim, d, arena)?;
        let (rest_bdim, rem_bdim) = remove_dim(bdim, d, arena)?;

        let global_dim: Dim<'a> = match (rem_gdim, rem_bdim) {
            (Dim::X(g), Dim::X(b)) => {
                let combined = Nat::new_binop_ref(arena, BinOpNat::Mul, g.0.clone(), b.0.clone());
                // use a zero-capture closure so that its inferred lifetime is `'a`
                Dim::new_1d(arena, |d1: &'a Dim1d<'a>| Dim::X(d1), combined)
            }
            (Dim::Y(g), Dim::Y(b)) => {
                let combined = Nat::new_binop_ref(arena, BinOpNat::Mul, g.0.clone(), b.0.clone());
                Dim::new_1d(arena, |d1: &'a Dim1d<'a>| Dim::Y(d1), combined)
            }
            (Dim::Z(g), Dim::Z(b)) => {
                let combined = Nat::new_binop_ref(arena, BinOpNat::Mul, g.0.clone(), b.0.clone());
                Dim::new_1d(arena, |d1: &'a Dim1d<'a>| Dim::Z(d1), combined)
            }
            _ => {
                return Err(TyError::String(format!(
                    "Cannot thread-map dimension {:?} on {:?}/{:?}",
                    d, gdim, bdim
                )))
            }
        };

        if let (Some(rg), Some(rb)) = (rest_gdim, rest_bdim) {
            let inner = ExecTyKind::GpuBlockGrp(rg, rb);
            let inner_ty: &'a ExecTy<'a> = arena.alloc(ExecTy::new(inner));
            Ok(ExecTyKind::GpuToThreads(global_dim, inner_ty))
        } else {
            Err(TyError::UnexpectedType)
        }
    } else {
        Err(TyError::UnexpectedType)
    }
}

/**
fn ty_check_exec_to_warps<'a>(
    nat_ctx: &NatCtx,
    exec_ty: &'a ExecTyKind<'a>,
) -> TyResult<'a, ExecTyKind<'a>> {
    match exec_ty {
        ExecTyKind::GpuBlock(dim) => match dim.clone() {
            Dim::X(d) => {
                if d.0.eval(nat_ctx)? % 32 != 0 {
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
*/

fn ty_check_exec_to_warps<'a>(
    nat_ctx: &'a NatCtx<'a>,
    exec_ty: &'a ExecTyKind<'a>,
    arena: &'a Bump,
) -> TyResult<'a, ExecTyKind<'a>> {
    // Only valid if we're looking at a single‐dimension block
    if let ExecTyKind::GpuBlock(block_dim) = exec_ty {
        match block_dim {
            Dim::X(d1) | Dim::Y(d1) | Dim::Z(d1) => {
                // d1: &Dim1d<'a>, so d1.0: Nat<'a>
                let len = d1.0.eval(nat_ctx)?;
                if len % 32 != 0 {
                    return Err(TyError::String(format!(
                        "Block size must be divisible by 32 to form warps, got {} in {:?}",
                        len, exec_ty
                    )));
                }
                // compute len / 32 in the arena
                let warp_nat: Nat<'a> =
                    Nat::new_binop_ref(arena, BinOpNat::Div, d1.0.clone(), Nat::Lit(32));
                Ok(ExecTyKind::GpuWarpGrp(warp_nat))
            }
            _ => Err(TyError::String(format!(
                "GpuBlock must be 1-D to form warps, got {:?}",
                exec_ty
            ))),
        }
    } else {
        Err(TyError::String(format!(
            "Cannot form warps from non-GpuBlock type {:?}",
            exec_ty
        )))
    }
}

fn ty_check_exec_forall<'a>(
    d: DimCompo,
    exec_ty: &'a ExecTyKind<'a>,
    arena: &'a Bump,
) -> TyResult<'a, ExecTyKind<'a>> {
    let res_ty = match exec_ty {
        ExecTyKind::GpuGrid(gdim, bdim) => {
            let inner_dim = remove_dim(gdim, d, arena)?.0;
            match inner_dim {
                Some(dim) => ExecTyKind::GpuGrid(dim, bdim.clone()),
                None => ExecTyKind::GpuBlock(bdim.clone()),
            }
        }
        ExecTyKind::GpuBlockGrp(gdim, bdim) => {
            let inner_dim = remove_dim(gdim, d, arena)?.0;
            match inner_dim {
                Some(dim) => ExecTyKind::GpuBlockGrp(dim, bdim.clone()),
                None => ExecTyKind::GpuBlock(bdim.clone()),
            }
        }
        ExecTyKind::GpuBlock(bdim) => {
            let inner_dim = remove_dim(bdim, d, arena)?.0;
            match inner_dim {
                Some(dim) => ExecTyKind::GpuBlock(dim),
                None => ExecTyKind::GpuThread,
            }
        }
        ExecTyKind::GpuThreadGrp(tdim) => {
            let inner_dim = remove_dim(tdim, d, arena)?.0;
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
                let forall_inner = ty_check_exec_forall(d, &inner_exec.ty, arena)?;
                let new_ty: ExecTy<'a> = ExecTy::new(forall_inner);
                let new_ref: &'a ExecTy<'a> = arena.alloc(new_ty);
                ExecTyKind::GpuToThreads(dim.clone(), new_ref)
            }
        }
        ex @ ExecTyKind::CpuThread | ex @ ExecTyKind::GpuThread | ex @ ExecTyKind::Any => {
            return Err(TyError::String(format!("Cannot schedule over {:?}", ex)))
        }
    };
    Ok(res_ty)
}

/**
pub fn remove_dim<'a>(
    dim: &'a Dim<'a>,
    dim_compo: DimCompo,
) -> TyResult<'a, (Option<Dim<'a>>, Dim<'a>)> {
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
*/

pub fn remove_dim<'a>(
    dim: &'a Dim<'a>,
    dim_compo: DimCompo,
    arena: &'a Bump,
) -> TyResult<'a, (Option<Dim<'a>>, Dim<'a>)> {
    use DimCompo::*;
    let result = match (dim, dim_compo) {
        // 3D → leftover 2D + removed 1D
        (Dim::XYZ(d3), X) => {
            let rest = Dim::new_2d(
                arena,
                |d2: &'a Dim2d<'a>| Dim::YZ(d2),
                d3.1.clone(),
                d3.2.clone(),
            );
            let rem = Dim::new_1d(arena, |d1: &'a Dim1d<'a>| Dim::X(d1), d3.0.clone());
            (Some(rest), rem)
        }
        (Dim::XYZ(d3), Y) => {
            let rest = Dim::new_2d(
                arena,
                |d2: &'a Dim2d<'a>| Dim::XZ(d2),
                d3.0.clone(),
                d3.2.clone(),
            );
            let rem = Dim::new_1d(arena, |d1: &'a Dim1d<'a>| Dim::Y(d1), d3.1.clone());
            (Some(rest), rem)
        }
        (Dim::XYZ(d3), Z) => {
            let rest = Dim::new_2d(
                arena,
                |d2: &'a Dim2d<'a>| Dim::XY(d2),
                d3.0.clone(),
                d3.1.clone(),
            );
            let rem = Dim::new_1d(arena, |d1: &'a Dim1d<'a>| Dim::Z(d1), d3.2.clone());
            (Some(rest), rem)
        }

        // 2D → leftover 1D + removed 1D
        (Dim::XY(d2), X) => {
            let rest = Dim::new_1d(arena, |d1: &'a Dim1d<'a>| Dim::Y(d1), d2.1.clone());
            let rem = Dim::new_1d(arena, |d1: &'a Dim1d<'a>| Dim::X(d1), d2.0.clone());
            (Some(rest), rem)
        }
        (Dim::XY(d2), Y) => {
            let rest = Dim::new_1d(arena, |d1: &'a Dim1d<'a>| Dim::X(d1), d2.0.clone());
            let rem = Dim::new_1d(arena, |d1: &'a Dim1d<'a>| Dim::Y(d1), d2.1.clone());
            (Some(rest), rem)
        }

        (Dim::XZ(d2), X) => {
            let rest = Dim::new_1d(arena, |d1: &'a Dim1d<'a>| Dim::Z(d1), d2.1.clone());
            let rem = Dim::new_1d(arena, |d1: &'a Dim1d<'a>| Dim::X(d1), d2.0.clone());
            (Some(rest), rem)
        }
        (Dim::XZ(d2), Z) => {
            let rest = Dim::new_1d(arena, |d1: &'a Dim1d<'a>| Dim::X(d1), d2.0.clone());
            let rem = Dim::new_1d(arena, |d1: &'a Dim1d<'a>| Dim::Z(d1), d2.1.clone());
            (Some(rest), rem)
        }

        (Dim::YZ(d2), Y) => {
            let rest = Dim::new_1d(arena, |d1: &'a Dim1d<'a>| Dim::Z(d1), d2.1.clone());
            let rem = Dim::new_1d(arena, |d1: &'a Dim1d<'a>| Dim::Y(d1), d2.0.clone());
            (Some(rest), rem)
        }
        (Dim::YZ(d2), Z) => {
            let rest = Dim::new_1d(arena, |d1: &'a Dim1d<'a>| Dim::Y(d1), d2.0.clone());
            let rem = Dim::new_1d(arena, |d1: &'a Dim1d<'a>| Dim::Z(d1), d2.1.clone());
            (Some(rest), rem)
        }

        // 1D → nothing + same 1D
        (Dim::X(d1), X) => (
            None,
            Dim::new_1d(arena, |d: &'a Dim1d<'a>| Dim::X(d), d1.0.clone()),
        ),
        (Dim::Y(d1), Y) => (
            None,
            Dim::new_1d(arena, |d: &'a Dim1d<'a>| Dim::Y(d), d1.0.clone()),
        ),
        (Dim::Z(d1), Z) => (
            None,
            Dim::new_1d(arena, |d: &'a Dim1d<'a>| Dim::Z(d), d1.0.clone()),
        ),

        // anything else is illegal
        _ => return Err(TyError::IllegalDimension),
    };

    Ok(result)
}

fn ty_check_exec_take_range<'a>(
    d: DimCompo,
    n: &'a Nat<'a>,
    proj: LeftOrRight,
    exec_ty: &'a ExecTyKind<'a>,
    arena: &'a Bump,
) -> TyResult<'a, ExecTyKind<'a>> {
    // split into two ExecTyKind variants, left & right
    let (left_ty, right_ty) = match exec_ty {
        // Grid or BlockGrp: we split the grid‐dim, keep block‐dim the same
        ExecTyKind::GpuGrid(gdim, bdim) | ExecTyKind::GpuBlockGrp(gdim, bdim) => {
            let (ldim, rdim) = split_dim(d, n, gdim.clone(), arena)?;
            let left = ExecTyKind::GpuBlockGrp(ldim, bdim.clone());
            let right = ExecTyKind::GpuBlockGrp(rdim, bdim.clone());
            (left, right)
        }

        // Block or ThreadGrp: split the single dim
        ExecTyKind::GpuBlock(dim) | ExecTyKind::GpuThreadGrp(dim) => {
            let (ldim, rdim) = split_dim(d, n, dim.clone(), arena)?;
            let left = ExecTyKind::GpuThreadGrp(ldim);
            let right = ExecTyKind::GpuThreadGrp(rdim);
            (left, right)
        }

        // ToThreads: either it splits on the ToThreads dim, or we descend into the inner ExecTy
        ExecTyKind::GpuToThreads(dim, inner_ref) => {
            if dim_compo_matches_dim(d, dim) {
                // slice the ToThreads dimension itself
                let (ldim, rdim) = split_dim(d, n, dim.clone(), arena)?;
                (
                    ExecTyKind::GpuToThreads(ldim, inner_ref.clone()),
                    ExecTyKind::GpuToThreads(rdim, inner_ref.clone()),
                )
            } else if let ExecTyKind::GpuBlockGrp(gdim2, bdim2) = &inner_ref.ty {
                // otherwise split inside the inner block‐group
                let (ldim, rdim) = split_dim(d, n, gdim2.clone(), arena)?;

                // bump‐allocate the two new inner ExecTy values
                let left_inner = ExecTyKind::GpuBlockGrp(ldim, bdim2.clone());
                let right_inner = ExecTyKind::GpuBlockGrp(rdim, bdim2.clone());
                let left_ref: &'a ExecTy<'a> = arena.alloc(ExecTy::new(left_inner));
                let right_ref: &'a ExecTy<'a> = arena.alloc(ExecTy::new(right_inner));

                (
                    ExecTyKind::GpuToThreads(dim.clone(), left_ref),
                    ExecTyKind::GpuToThreads(dim.clone(), right_ref),
                )
            } else {
                panic!("GpuToThreads is not well-formed.")
            }
        }

        other => {
            return Err(TyError::String(format!(
                "Trying to split non-splittable execution resource: {:?}",
                other
            )))
        }
    };

    // pick the left or right projection
    Ok(if proj == LeftOrRight::Left {
        left_ty
    } else {
        right_ty
    })
}

fn dim_compo_matches_dim<'a>(d: DimCompo, dim: &'a Dim<'a>) -> bool {
    (matches!(dim, Dim::X(_)) && d == DimCompo::X)
        | (matches!(dim, Dim::Y(_)) && d == DimCompo::Y)
        | (matches!(dim, Dim::Z(_)) && d == DimCompo::Z)
}

/**
fn split_dim<'a>(
    split_dim: DimCompo,
    pos: Nat<'a>,
    dim: Dim<'a>,
) -> TyResult<'a, (Dim<'a>, Dim<'a>)> {
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
*/

pub fn split_dim<'a>(
    split_dim: DimCompo,
    pos: &'a Nat<'a>,
    dim: Dim<'a>,
    arena: &'a Bump,
) -> TyResult<'a, (Dim<'a>, Dim<'a>)> {
    use DimCompo::*;

    let result = match dim {
        // 3D case: peel off one axis, leave a 3D on both sides
        Dim::XYZ(d3) => match split_dim {
            X => {
                let left = Dim::new_3d(arena, d3.0.clone(), d3.1.clone(), d3.2.clone());
                let right_nat = Nat::new_binop_ref(arena, BinOpNat::Sub, d3.0.clone(), pos.clone());
                let right = Dim::new_3d(arena, right_nat, d3.1.clone(), d3.2.clone());
                (left, right)
            }
            Y => {
                let left = Dim::new_3d(arena, d3.0.clone(), d3.1.clone(), d3.2.clone());
                let right_nat = Nat::new_binop_ref(arena, BinOpNat::Sub, d3.1.clone(), pos.clone());
                let right = Dim::new_3d(arena, d3.0.clone(), right_nat, d3.2.clone());
                (left, right)
            }
            Z => {
                let left = Dim::new_3d(arena, d3.0.clone(), d3.1.clone(), d3.2.clone());
                let right_nat = Nat::new_binop_ref(arena, BinOpNat::Sub, d3.2.clone(), pos.clone());
                let right = Dim::new_3d(arena, d3.0.clone(), d3.1.clone(), right_nat);
                (left, right)
            }
        },

        // 2D cases: peel off one axis, leave a 2D on both sides
        Dim::XY(d2) => match split_dim {
            X => {
                let left = Dim::new_2d(
                    arena,
                    |d: &'a Dim2d<'a>| Dim::XY(d),
                    pos.clone(),
                    d2.1.clone(),
                );
                let right_nat = Nat::new_binop_ref(arena, BinOpNat::Sub, d2.0.clone(), pos.clone());
                let right = Dim::new_2d(
                    arena,
                    |d: &'a Dim2d<'a>| Dim::XY(d),
                    right_nat,
                    d2.1.clone(),
                );
                (left, right)
            }
            Y => {
                let left = Dim::new_2d(
                    arena,
                    |d: &'a Dim2d<'a>| Dim::XY(d),
                    d2.0.clone(),
                    pos.clone(),
                );
                let right_nat = Nat::new_binop_ref(arena, BinOpNat::Sub, d2.1.clone(), pos.clone());
                let right = Dim::new_2d(
                    arena,
                    |d: &'a Dim2d<'a>| Dim::XY(d),
                    d2.0.clone(),
                    right_nat,
                );
                (left, right)
            }
            Z => return Err(TyError::IllegalDimension),
        },

        Dim::XZ(d2) => match split_dim {
            X => {
                let left = Dim::new_2d(
                    arena,
                    |d: &'a Dim2d<'a>| Dim::XZ(d),
                    pos.clone(),
                    d2.1.clone(),
                );
                let right_nat = Nat::new_binop_ref(arena, BinOpNat::Sub, d2.0.clone(), pos.clone());
                let right = Dim::new_2d(
                    arena,
                    |d: &'a Dim2d<'a>| Dim::XZ(d),
                    right_nat,
                    d2.1.clone(),
                );
                (left, right)
            }
            Z => {
                let left = Dim::new_2d(
                    arena,
                    |d: &'a Dim2d<'a>| Dim::XZ(d),
                    d2.0.clone(),
                    pos.clone(),
                );
                let right_nat = Nat::new_binop_ref(arena, BinOpNat::Sub, d2.1.clone(), pos.clone());
                let right = Dim::new_2d(
                    arena,
                    |d: &'a Dim2d<'a>| Dim::XZ(d),
                    d2.0.clone(),
                    right_nat,
                );
                (left, right)
            }
            Y => return Err(TyError::IllegalDimension),
        },

        Dim::YZ(d2) => match split_dim {
            Y => {
                let left = Dim::new_2d(
                    arena,
                    |d: &'a Dim2d<'a>| Dim::YZ(d),
                    pos.clone(),
                    d2.1.clone(),
                );
                let right_nat = Nat::new_binop_ref(arena, BinOpNat::Sub, d2.0.clone(), pos.clone());
                let right = Dim::new_2d(
                    arena,
                    |d: &'a Dim2d<'a>| Dim::YZ(d),
                    right_nat,
                    d2.1.clone(),
                );
                (left, right)
            }
            Z => {
                let left = Dim::new_2d(
                    arena,
                    |d: &'a Dim2d<'a>| Dim::YZ(d),
                    d2.0.clone(),
                    pos.clone(),
                );
                let right_nat = Nat::new_binop_ref(arena, BinOpNat::Sub, d2.1.clone(), pos.clone());
                let right = Dim::new_2d(
                    arena,
                    |d: &'a Dim2d<'a>| Dim::YZ(d),
                    d2.0.clone(),
                    right_nat,
                );
                (left, right)
            }
            X => return Err(TyError::IllegalDimension),
        },

        // 1D cases: peel off the only axis
        Dim::X(d1) if split_dim == X => {
            let left = Dim::new_1d(arena, |d: &'a Dim1d<'a>| Dim::X(d), pos.clone());
            let right_nat = Nat::new_binop_ref(arena, BinOpNat::Sub, d1.0.clone(), pos.clone());
            let right = Dim::new_1d(arena, |d: &'a Dim1d<'a>| Dim::X(d), right_nat);
            (left, right)
        }
        Dim::Y(d1) if split_dim == Y => {
            let left = Dim::new_1d(arena, |d: &'a Dim1d<'a>| Dim::Y(d), pos.clone());
            let right_nat = Nat::new_binop_ref(arena, BinOpNat::Sub, d1.0.clone(), pos.clone());
            let right = Dim::new_1d(arena, |d: &'a Dim1d<'a>| Dim::Y(d), right_nat);
            (left, right)
        }
        Dim::Z(d1) if split_dim == Z => {
            let left = Dim::new_1d(arena, |d: &'a Dim1d<'a>| Dim::Z(d), pos.clone());
            let right_nat = Nat::new_binop_ref(arena, BinOpNat::Sub, d1.0.clone(), pos.clone());
            let right = Dim::new_1d(arena, |d: &'a Dim1d<'a>| Dim::Z(d), right_nat);
            (left, right)
        }

        _ => return Err(TyError::IllegalDimension),
    };

    Ok(result)
}

/**
pub(super) fn normalize<'a>(mut exec: ExecExpr<'a>) -> ExecExpr<'a> {
    assert!(exec.ty.is_some());
    let mut exec_path = exec.exec.path;
    if !exec_path.is_empty() {
        let boundaries = level_boundaries(&exec_path);
        sort_within_boundaries(&mut exec_path, &boundaries);
    }
    exec.exec.path = exec_path;
    exec
}
*/

pub(super) fn normalize<'a>(old: ExecExpr<'a>, arena: &'a bumpalo::Bump) -> ExecExpr<'a> {
    assert!(old.ty.is_some());

    // 1) Copy the old path into a fresh bump-Vec
    let mut new_path: BumpVec<'a, ExecPathElem<'a>> = BumpVec::new_in(arena);
    new_path.extend(old.exec.path.iter().cloned());

    // 2) Sort if needed
    if !new_path.is_empty() {
        // We can still use the slice-based sorter:
        let slice = new_path.as_mut_slice();
        let boundaries = level_boundaries(slice);
        sort_within_boundaries(slice, &boundaries);
    }

    // 3) Build a new ExecExprKind<'a> in the arena
    let new_exec_kind = ExecExprKind {
        base: old.exec.base.clone(),
        path: new_path,
    };
    let new_exec_ref: &'a ExecExprKind<'a> = arena.alloc(new_exec_kind);

    // 4) Return a fresh ExecExpr pointing at it, but re‐use the old ty/span
    ExecExpr {
        exec: new_exec_ref,
        ty: old.ty,
        span: old.span,
    }
}

// Allocating a handful of usizes on the heap here is negligible
// FIXME: not correct if first take_range on dimension of lower level followed by forall on different dimension in upper level
//  for fix: see formalism
fn level_boundaries<'a>(exec_path: &'a [ExecPathElem<'a>]) -> Vec<usize> {
    let mut forall_dims_encountered = Vec::with_capacity(3);
    let mut boundaries = Vec::with_capacity(3);
    for (i, elem) in exec_path.iter().enumerate() {
        match elem {
            ExecPathElem::ForAll(d) => {
                if forall_dims_encountered.contains(d) {
                    forall_dims_encountered.clear();
                    boundaries.push(i);
                }
                forall_dims_encountered.push(*d);
            }
            ExecPathElem::TakeRange(take_range) => {
                if forall_dims_encountered.contains(&take_range.split_dim) {
                    forall_dims_encountered.clear();
                    boundaries.push(i);
                }
            }
            ExecPathElem::ToWarps => {
                forall_dims_encountered.clear();
                boundaries.push(i);
            }
            ExecPathElem::ToThreads(_) => unimplemented!(),
        }
    }
    // upper boundary of last level
    boundaries.push(exec_path.len());
    boundaries
}

/**
fn sort_within_boundaries<'a>(exec_path: &'a mut Vec<ExecPathElem<'a>>, boundaries: &[usize]) {
    let mut lower_bound = 0;
    for b in boundaries {
        for i in lower_bound..*b {
            for j in lower_bound..(*b - i - 1) {
                if swappable_exec_path_elems(&exec_path[j], &exec_path[j + 1]) {
                    exec_path.swap(j, j + 1)
                }
            }
        }
        lower_bound = *b;
    }
}
*/

fn sort_within_boundaries<'a>(exec_path: &mut [ExecPathElem<'a>], boundaries: &[usize]) {
    let mut lower = 0;
    for &b in boundaries {
        for i in lower..b {
            for j in lower..(b - 1) {
                if swappable_exec_path_elems(&exec_path[j], &exec_path[j + 1]) {
                    exec_path.swap(j, j + 1);
                }
            }
        }
        lower = b;
    }
}

fn swappable_exec_path_elems<'a>(lhs: &'a ExecPathElem<'a>, rhs: &'a ExecPathElem<'a>) -> bool {
    match (lhs, rhs) {
        (ExecPathElem::ForAll(dl), ExecPathElem::ForAll(dr)) => dl > dr,
        (ExecPathElem::ForAll(_), ExecPathElem::TakeRange(_)) => true,
        _ => false,
    }
}
