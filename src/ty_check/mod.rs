mod borrow_check;
mod constraint_check;
mod ctxs;
mod error;
mod infer_kinded_args;
pub mod pre_decl;
mod subty;
pub(crate) mod unify;

use crate::ast::internal::{FrameEntry, IdentTyped, Loan, Place, PrvMapping};
use crate::ast::utils::FreeKindedIdents;
use crate::ast::visit::Visit;
use crate::ast::DataTyKind::Scalar;
use crate::ast::ThreadHierchyTy;
use crate::ast::*;
use crate::error::ErrorReported;
use crate::ty_check::infer_kinded_args::infer_kinded_args_from_mono_ty;
use crate::ty_check::unify::Constrainable;
use core::panic;
use ctxs::{GlobalCtx, KindCtx, TyCtx};
use error::*;
use std::collections::HashSet;
use std::ops::Deref;

use self::constraint_check::ConstraintScheme;

type TyResult<T> = Result<T, TyError>;

macro_rules! iter_TyResult_to_TyResult {
    ($err_iter: expr) => {{
        let err_vec: Vec<TyError> = $err_iter
            .into_iter()
            .filter_map(|res| -> Option<TyError> {
                match res {
                    Ok(_) => None,
                    Err(err) => Some(err),
                }
            })
            .collect();
        if err_vec.is_empty() {
            Ok(())
        } else {
            Err(TyError::MultiError(err_vec))
        }
    }};
}

// ∀ε ∈ Σ. Σ ⊢ ε
// --------------
//      ⊢ Σ
pub fn ty_check(compil_unit: &mut CompilUnit) -> Result<(), ErrorReported> {
    TyChecker::new().ty_check(compil_unit).map_err(|err| {
        err.emit(compil_unit.source);
        ErrorReported
    })
}

struct TyChecker {
    gl_ctx: GlobalCtx,
}

impl TyChecker {
    pub fn new() -> Self {
        let gl_ctx = GlobalCtx::new().append_fun_decls(&pre_decl::fun_decls());

        TyChecker { gl_ctx }
    }

    fn ty_check(&mut self, compil_unit: &mut CompilUnit) -> TyResult<()> {
        let errs: Vec<TyError> = self
            .gl_ctx
            .append_from_item_def(&compil_unit.item_defs)
            .into_iter()
            .map(|ctx_error| TyError::from(ctx_error))
            .collect();

        if errs.is_empty() {
            iter_TyResult_to_TyResult!(compil_unit
                .item_defs
                .iter_mut()
                .map(|item| self.ty_check_item_def(item),))
        } else {
            Err(TyError::MultiError(errs))
        }
    }

    fn ty_check_item_def(&mut self, item_def: &mut Item) -> TyResult<()> {
        match item_def {
            Item::FunDef(fun_def) => self.ty_check_fun_def(KindCtx::new(), fun_def),
            Item::StructDef(struct_def) => self.ty_check_struct_def(struct_def),
            Item::TraitDef(trait_def) => self.ty_check_trait_def(trait_def),
            Item::ImplDef(impl_def) => self.ty_check_impl_def(impl_def),
        }
    }

    fn ty_check_struct_def(&mut self, struct_def: &mut StructDef) -> TyResult<()> {
        let kind_ctx = KindCtx::new().append_idents(struct_def.generic_params.clone());
        let ty_ctx = TyCtx::new();

        iter_TyResult_to_TyResult!(struct_def.decls.iter().map(|struct_field| {
            self.ty_well_formed(
                &kind_ctx,
                &ty_ctx,
                Exec::View,
                &Ty::new(TyKind::Data(struct_field.ty.clone())),
            ) //TODO exec = View???
        }))
    }

    fn ty_check_trait_def(&mut self, trait_def: &mut TraitDef) -> TyResult<()> {
        let kind_ctx_empty = KindCtx::new();
        let kind_ctx_trait = KindCtx::new()
            .append_idents(vec![IdentKinded::new(&Ident::new("Self"), Kind::DataTy)])
            .append_idents(trait_def.generic_params.clone());
        let ty_ctx = TyCtx::new();

        self.gl_ctx.theta.append_constraints(&trait_def.constraints);

        let result =
            iter_TyResult_to_TyResult!(trait_def.decls.iter_mut().map(|ass_item| match ass_item {
                AssociatedItem::FunDef(fun_def) => {
                    self.ty_check_fun_def(kind_ctx_trait.clone(), fun_def)
                }
                AssociatedItem::FunDecl(fun_decl) => {
                    let fun_ty = self.gl_ctx.fun_ty_by_name(FunctionName {
                        name: fun_decl.name.clone(),
                        fun_kind: FunctionKind::TraitFun(trait_def.name.clone()),
                    });
                    self.tyscheme_well_formed(&kind_ctx_empty, &ty_ctx, fun_decl.exec, fun_ty)
                }
                AssociatedItem::ConstItem(_, _, _) => unimplemented!("TODO"),
            }));

        self.gl_ctx.theta.append_constraints(&trait_def.constraints);

        result?;

        let kind_ctx =
            kind_ctx_trait
                .append_idents(vec![IdentKinded::new(&Ident::new("Self"), Kind::Ty).clone()]);
        iter_TyResult_to_TyResult!(trait_def.constraints.iter().map(|con| {
            self.well_formed_constraint_scheme(&kind_ctx, &ty_ctx, &ConstraintScheme::new(con))
        }))
    }

    fn ty_check_impl_def(&mut self, impl_def: &mut ImplDef) -> TyResult<()> {
        let kind_ctx = KindCtx::new();
        let ty_ctx = TyCtx::new();

        if impl_def.trait_impl.is_some() {
            let trait_impl = impl_def.trait_impl.clone().unwrap();
            let trait_def = self.gl_ctx.trait_ty_by_name(&trait_impl.name)?.clone();

            Self::check_args_have_correct_kinds(&trait_def.generic_params, &trait_impl.generics)?;

            let mut monotypes = Vec::with_capacity(trait_def.generic_params.len() + 1);
            monotypes.push(impl_def.dty.clone());
            monotypes.extend(
                trait_impl
                    .generics
                    .iter()
                    .filter_map(|gen_arg| match gen_arg {
                        ArgKinded::DataTy(dty) => Some(dty.clone()),
                        _ => unimplemented!("TODO"),
                    })
                    .collect::<Vec<DataTy>>(),
            );

            let mut generics = Vec::with_capacity(monotypes.len());
            generics.push(IdentKinded::new(&Ident::new("Self"), Kind::DataTy));
            generics.extend(trait_def.generic_params.clone());

            //Check every generic is a free type var in "monotypes"
            let free_idents = monotypes.iter().fold(HashSet::new(), |mut free, monoty| {
                free.extend(monoty.free_idents());
                free
            });
            if !impl_def
                .generic_params
                .iter()
                .fold(true, |res, gen| res & free_idents.contains(gen))
            {
                return Err(TyError::WrongNumberOfGenericParams {
                    expected: free_idents.len(),
                    found: generics.len(),
                });
            }

            self.well_formed_constraint_scheme(
                &kind_ctx,
                &ty_ctx,
                &ConstraintScheme {
                    generics: impl_def.generic_params.clone(),
                    implican: impl_def.constraints.clone(),
                    implied: Constraint {
                        param: impl_def.dty.clone(),
                        trait_bound: trait_impl.clone(),
                    },
                },
            )?;

            //All supertrait constraints: "if Self impl this trait => Self also impl trait X"
            let supertraits_constraints = trait_def
                .supertraits_constraints()
                .into_iter()
                .map(|supertrait_cons| ConstraintScheme {
                    generics: generics.clone(),
                    implican: vec![Constraint {
                        param: DataTy::new(DataTyKind::Ident(Ident::new("Self"))),
                        trait_bound: TraitMonoType {
                            name: trait_def.name.clone(),
                            generics: trait_def
                                .generic_params
                                .iter()
                                .map(|gen| gen.arg_kinded())
                                .collect(),
                        },
                    }],
                    implied: supertrait_cons,
                })
                .collect::<Vec<ConstraintScheme>>();

            //We must not assume the supertrait constraints, because we didnt check if
            //our impl really fullfill this supertrait constraints
            //Otherwise, if we would check this constraints, we would deduce from the
            //supertraits constraints and because we impl this trait that all this
            //constraints are fullfilled
            self.gl_ctx
                .theta
                .remove_constraint_schemes(&supertraits_constraints);
            //While typechecking the constraints specified in the where-clause of the impl can be assumed
            self.gl_ctx.theta.append_constraints(&impl_def.constraints);

            let kind_ctx = kind_ctx.append_idents(impl_def.generic_params.clone());

            let mut errors = Vec::new();

            //Check for every supertrait constraint if it is fullfilled
            trait_def
                .supertraits_constraints()
                .into_iter()
                .for_each(|supertrait_con| {
                    if !self.gl_ctx.theta.check_constraint(
                        &generics.iter().zip(monotypes.iter()).fold(
                            supertrait_con.clone(),
                            |cons, (t, tau)| {
                                cons.subst_ident_kinded(t, &ArgKinded::DataTy(tau.clone()))
                            },
                        ),
                    ) {
                        errors.push(TyError::UnfullfilledConstraint(supertrait_con))
                    }
                });
            //Check for every constraint specified in the where-clause of the trait is fullfilled
            trait_def.constraints.iter().for_each(|con| {
                if !self.gl_ctx.theta.check_constraint(
                    &generics
                        .iter()
                        .zip(monotypes.iter())
                        .fold(con.clone(), |cons, (t, tau)| {
                            cons.subst_ident_kinded(t, &ArgKinded::DataTy(tau.clone()))
                        }),
                ) {
                    errors.push(TyError::UnfullfilledConstraint(con.clone()))
                }
            });

            //Check if all fun_decls from the trait are implmented here
            let impl_def_ty = impl_def.ty();
            let mut ass_items_to_check: Vec<&mut AssociatedItem> =
                impl_def.decls.iter_mut().collect();
            trait_def.decls.iter().for_each(|ass_item| {
                let fun_name = match ass_item {
                    AssociatedItem::FunDef(fun_def) => fun_def.name.clone(),
                    AssociatedItem::FunDecl(fun_decl) => fun_decl.name.clone(),
                    AssociatedItem::ConstItem(_, _, _) => unimplemented!("TODO"),
                };
                match ass_item {
                    AssociatedItem::FunDef(_) | AssociatedItem::FunDecl(_) => {
                        if let Some(index) =
                            ass_items_to_check.iter().position(
                                |impl_ass_item| match impl_ass_item {
                                    AssociatedItem::FunDef(fun) => fun.name == fun_name,
                                    _ => false,
                                },
                            )
                        {
                            let fun_impl = match ass_items_to_check.swap_remove(index) {
                                AssociatedItem::FunDef(fun_def) => fun_def,
                                _ => panic!("This can not happen"),
                            };
                            let fun_decl_ty = self
                                .gl_ctx
                                .fun_ty_by_name(FunctionName::from_trait(&fun_name, &trait_def));

                            let expected_impl_fun_ty = TypeScheme {
                                generic_params: fun_decl_ty.generic_params.clone(),
                                constraints: fun_decl_ty.constraints[1..].to_vec(),
                                mono_ty: fun_decl_ty.mono_ty.clone(),
                            }
                            .instantiate(
                                monotypes
                                    .clone()
                                    .into_iter()
                                    .map(|mono_ty| ArgKinded::DataTy(mono_ty))
                                    .collect::<Vec<ArgKinded>>()
                                    .as_slice(),
                            );
                            let fun_impl_ty = fun_impl.ty();

                            if expected_impl_fun_ty.generic_params.len()
                                == fun_impl_ty.generic_params.len()
                                && expected_impl_fun_ty
                                    .generic_params
                                    .iter()
                                    .zip(fun_impl_ty.generic_params.iter())
                                    .fold(true, |res, (gen1, gen2)| res && gen1.kind == gen2.kind)
                            {
                                if expected_impl_fun_ty
                                    .mono_ty
                                    .eq_structure(&fun_impl_ty.mono_ty)
                                {
                                    if let Err(err) =
                                        self.ty_check_fun_def(kind_ctx.clone(), fun_impl)
                                    {
                                        errors.push(err);
                                    }
                                } else {
                                    errors.push(TyError::UnexpectedType {
                                        expected: expected_impl_fun_ty.mono_ty,
                                        found: fun_impl_ty.mono_ty,
                                    })
                                }
                            } else {
                                errors.push(TyError::UnexpectedType {
                                    expected: expected_impl_fun_ty.mono_ty,
                                    found: fun_impl_ty.mono_ty,
                                })
                            }
                        } else {
                            match ass_item {
                                AssociatedItem::FunDef(_) => (),
                                AssociatedItem::FunDecl(_) => {
                                    errors.push(TyError::from(CtxError::FunNotImplemented {
                                        function_name: fun_name.clone(),
                                        trait_name: trait_def.name.clone(),
                                        impl_dty: impl_def_ty.clone(),
                                    }))
                                }
                                _ => unimplemented!(),
                            }
                        }
                    }
                    AssociatedItem::ConstItem(_, _, _) => unimplemented!("TODO"),
                }
            });

            ass_items_to_check
                .iter()
                .for_each(|item| errors.push(TyError::UnexpectedAssItemInImpl((**item).clone())));

            //Reset constraint environment
            self.gl_ctx.theta.remove_constraints(&impl_def.constraints);
            self.gl_ctx
                .theta
                .append_constraint_schemes(&supertraits_constraints);

            if errors.is_empty() {
                Ok(())
            } else {
                Err(TyError::MultiError(errors))
            }
        } else {
            let kind_ctx = kind_ctx.append_idents(impl_def.generic_params.clone());
            self.gl_ctx.theta.append_constraints(&impl_def.constraints);

            let result =
                iter_TyResult_to_TyResult!(impl_def.decls.iter_mut().map(|decl| match decl {
                    AssociatedItem::FunDecl(fun_decl) => Err(TyError::UnexpectedAssItemInImpl(
                        AssociatedItem::FunDecl(fun_decl.clone())
                    )),
                    AssociatedItem::FunDef(fun_def) =>
                        self.ty_check_fun_def(kind_ctx.clone(), fun_def),
                    AssociatedItem::ConstItem(_, _, _) => unimplemented!("TODO"),
                }));

            self.gl_ctx.theta.remove_constraints(&impl_def.constraints);

            result
        }
    }

    // Σ ⊢ fn f <List[φ], List[ρ], List[α]> (x1: τ1, ..., xn: τn) → τr where List[ρ1:ρ2] { e }
    fn ty_check_fun_def(&mut self, kind_ctx: KindCtx, gf: &mut FunDef) -> TyResult<()> {
        let kind_ctx = kind_ctx.append_idents(gf.generic_params.clone());
        kind_ctx.well_kinded_prv_rels(&gf.prv_rels)?;
        let kind_ctx = kind_ctx.append_prv_rels(gf.prv_rels.clone());

        self.gl_ctx.theta.append_constraints(&gf.constraints);

        let res: TyResult<()> = {
            // TODO check that every prv_rel only uses provenance variables bound in generic_params

            // Build frame typing for this function
            let glf_frame = internal::append_idents_typed(
                &vec![],
                gf.param_decls
                    .iter()
                    .map(|ParamDecl { ident, ty, mutbl }| IdentTyped {
                        ident: ident.clone(),
                        ty: ty.as_ref().unwrap().clone(),
                        mutbl: *mutbl,
                    })
                    .collect(),
            );
            let ty_ctx = TyCtx::from(glf_frame);

            self.tyscheme_well_formed(&kind_ctx, &ty_ctx, gf.exec, &gf.ty())?;

            self.ty_check_expr(&kind_ctx, ty_ctx, gf.exec, &mut gf.body_expr)?;

            // t <= t_f
            // unify::constrain(
            //     gf.body_expr.ty.as_ref().unwrap(),
            //     &Ty::new(TyKind::Data(gf.ret_dty.clone())),
            // )?;

            //coalesce::coalesce_ty(&mut self.term_constr.constr_map, &mut body_ctx, )
            let empty_ty_ctx = subty::check(
                &kind_ctx,
                TyCtx::new(),
                gf.body_expr.ty.as_ref().unwrap().dty(),
                &gf.ret_dty,
            )?;
            //TODO why is this the case?
            assert!(
                empty_ty_ctx.is_empty(),
                "Expected typing context to be empty. But TyCtx:\n {:?}",
                empty_ty_ctx
            );
            Ok(())
        };

        self.gl_ctx.theta.remove_constraints(&gf.constraints);

        res
    }

    // TODO find out if Gamma is always correct by construction (similarly to Delta), also all 3 combined
    // e has type τ under Σ, Δ, and Γ, producing output context Γ'
    // sideconditions: Global Function Context Σ, Kinding context Δ and typing context are well-formed and
    //   type τ is well-formed under well-formed GlFunCtxt, kinding ctx, output context Γ'.
    // Σ; Δ; Γ ⊢ e :^exec τ ⇒ Γ′, side conditions:  ⊢ Σ;Δ;Γ and Σ;Δ;Γ′ ⊢ τ
    // This never returns a dead type, because typing an expression with a dead type is not possible.
    fn ty_check_expr(
        &mut self,
        kind_ctx: &KindCtx,
        ty_ctx: TyCtx,
        exec: Exec,
        expr: &mut Expr,
    ) -> TyResult<TyCtx> {
        // TODO input contexts are well-formed
        //   well_formed_ctxs(gl_ctx, kind_ctx, &ty_ctx);
        let (res_ty_ctx, ty) = match &mut expr.expr {
            ExprKind::PlaceExpr(pl_expr) => {
                if pl_expr.is_place() {
                    self.ty_check_pl_expr_without_deref(kind_ctx, ty_ctx, exec, pl_expr)?
                } else {
                    self.ty_check_pl_expr_with_deref(kind_ctx, ty_ctx, exec, pl_expr)?
                }
            }
            ExprKind::Block(prvs, body) => {
                self.ty_check_block(kind_ctx, ty_ctx, exec, prvs, body)?
            }
            ExprKind::Let(pattern, ty, e) => {
                self.ty_check_let(kind_ctx, ty_ctx, exec, pattern, ty, e)?
            }
            ExprKind::LetUninit(ident, ty) => Self::ty_check_let_uninit(ty_ctx, exec, ident, ty)?,
            ExprKind::Seq(es) => self.ty_check_seq(kind_ctx, ty_ctx, exec, es)?,
            ExprKind::Lit(l) => Self::ty_check_literal(ty_ctx, l),
            ExprKind::Array(elems) => self.ty_check_array(kind_ctx, ty_ctx, exec, elems)?,
            ExprKind::Tuple(elems) => self.ty_check_tuple(kind_ctx, ty_ctx, exec, elems)?,
            ExprKind::Proj(e, i) => self.ty_check_proj(kind_ctx, ty_ctx, exec, e, i)?,
            ExprKind::App(path, function_kind, ef, k_args, args) => self.ty_check_app(
                kind_ctx,
                ty_ctx,
                exec,
                path,
                function_kind,
                ef,
                k_args,
                args,
            )?,
            // TODO remove
            ExprKind::DepApp(ef, k_args) => {
                unimplemented!()
            }
            ExprKind::StructInst(name, generic_args, inst_exprs) => {
                self.ty_check_new_struct(kind_ctx, ty_ctx, exec, name, generic_args, inst_exprs)?
            }
            ExprKind::Ref(prv, own, pl_expr) => {
                self.ty_check_borrow(kind_ctx, ty_ctx, exec, prv, *own, pl_expr)?
            }
            ExprKind::Index(pl_expr, index) => {
                self.ty_check_index_copy(kind_ctx, ty_ctx, exec, pl_expr, index)?
            }
            ExprKind::Assign(pl_expr, e) => {
                if pl_expr.is_place() {
                    self.ty_check_assign_place(kind_ctx, ty_ctx, exec, &pl_expr, e)?
                } else {
                    self.ty_check_assign_deref(kind_ctx, ty_ctx, exec, pl_expr, e)?
                }
            }
            ExprKind::IdxAssign(pl_expr, idx, e) => {
                self.ty_check_idx_assign(kind_ctx, ty_ctx, exec, pl_expr, idx, e)?
            }
            ExprKind::ParBranch(parall_collec, branch_idents, branch_bodies) => self
                .ty_check_par_branch(
                    kind_ctx,
                    ty_ctx,
                    exec,
                    parall_collec,
                    branch_idents,
                    branch_bodies,
                )?,
            ExprKind::ParForWith(
                decls,
                parall_ident,
                parall_collec,
                input_idents,
                input_exprs,
                body,
            ) => self.ty_check_par_for(
                kind_ctx,
                ty_ctx,
                exec,
                decls,
                parall_ident,
                parall_collec,
                input_idents,
                input_exprs,
                body,
            )?,
            ExprKind::ForNat(var, range, body) => {
                self.ty_check_for_nat(kind_ctx, ty_ctx, exec, var, range, body)?
            }
            ExprKind::For(ident, collec, body) => {
                self.ty_check_for(kind_ctx, ty_ctx, exec, ident, collec, body)?
            }
            ExprKind::IfElse(cond, case_true, case_false) => {
                self.ty_check_if_else(kind_ctx, ty_ctx, exec, cond, case_true, case_false)?
            }
            ExprKind::If(cond, case_true) => {
                self.ty_check_if(kind_ctx, ty_ctx, exec, cond, case_true)?
            }
            ExprKind::While(cond, body) => {
                self.ty_check_while(kind_ctx, ty_ctx, exec, cond, body)?
            }
            ExprKind::Lambda(params, exec, ret_ty, body) => {
                self.ty_check_lambda(kind_ctx, ty_ctx, *exec, params, ret_ty, body)?
            }
            ExprKind::BinOp(bin_op, lhs, rhs) => {
                self.ty_check_binary_op(kind_ctx, ty_ctx, exec, bin_op, lhs, rhs)?
            }
            ExprKind::UnOp(un_op, e) => self.ty_check_unary_op(kind_ctx, ty_ctx, exec, un_op, e)?,
            ExprKind::Split(r1, r2, own, s, view_ref) => {
                self.ty_check_split(kind_ctx, ty_ctx, exec, r1, r2, *own, s, view_ref)?
            }
            ExprKind::Range(l, u) => self.ty_check_range(kind_ctx, ty_ctx, exec, l, u)?,
            ExprKind::BorrowIndex(_, _, _, _) => unimplemented!(),
            ExprKind::Idx(_, _) => {
                unimplemented!("This is helper syntax to index into non-place expressions.")
            }
            ExprKind::Deref(_) => panic!(
                "Dereferencing a non place expression is not a valid Descend \
        program and only exists for codegen."
            ),
        };

        // TODO reintroduce!!!!
        //if let Err(err) = self.ty_well_formed(kind_ctx, &res_ty_ctx, exec, &ty) {
        //    panic!("{:?}", err);
        //}
        expr.ty = Some(ty);
        Ok(res_ty_ctx)
    }

    fn ty_check_new_struct(
        &mut self,
        kind_ctx: &KindCtx,
        ty_ctx: TyCtx,
        exec: Exec,
        struct_name: &String,
        generic_args: &mut Vec<ArgKinded>,
        inst_exprs: &mut Vec<(Ident, Expr)>,
    ) -> TyResult<(TyCtx, Ty)> {
        let struct_def_orginal = self.gl_ctx.struct_by_name(struct_name)?;
        let struct_def = struct_def_orginal.clone(); // Prevent borrowing errors

        //Check generic args
        if struct_def.generic_params.len() < generic_args.len() {
            return Err(TyError::WrongNumberOfGenericParams {
                expected: struct_def.generic_params.len(),
                found: generic_args.len(),
            });
        }
        Self::check_args_have_correct_kinds(
            &struct_def.generic_params[0..generic_args.len()].to_vec(),
            &generic_args,
        )?;
        let struct_ty = struct_def.ty().instantiate(generic_args);
        iter_TyResult_to_TyResult!(generic_args.iter().map(|gen_arg| match gen_arg {
            ArgKinded::DataTy(dty) =>
                self.ty_well_formed(kind_ctx, &ty_ctx, exec, &Ty::new(TyKind::Data(dty.clone()))),
            _ => unimplemented!("TODO"),
        }))?;

        //Sort all inst_exprs to have the same order like in struct_def
        //And check if all struct_fields are initialized
        let mut errs = Vec::new();
        let inst_exprs_sorted = struct_def
            .decls
            .iter()
            .filter_map(|field| {
                if let Some(inst_expr_position) = inst_exprs
                    .iter()
                    .position(|(name, _)| name.name == field.name)
                {
                    Some(inst_exprs.swap_remove(inst_expr_position))
                } else {
                    errs.push(TyError::MissingStructField {
                        missing_field: field.name.clone(),
                        struct_name: struct_def.name.clone(),
                    });
                    None
                }
            })
            .collect();
        inst_exprs.iter().for_each(|(name, expr)| {
            errs.push(TyError::UnexpectedStructField {
                unexpected_field: name.name.clone(),
                struct_name: struct_def.name.clone(),
            })
        });
        *inst_exprs = inst_exprs_sorted;
        if !errs.is_empty() {
            return Err(TyError::MultiError(errs));
        }

        //Tycheck every expression
        let ty_ctx = inst_exprs
            .iter_mut()
            .try_fold(ty_ctx, |ty_ctx, (_, expr)| {
                self.ty_check_expr(kind_ctx, ty_ctx, exec, expr)
            })?;

        //Infer remaining generic args
        let struct_inst_tys = match &struct_ty.mono_ty.dty().dty {
            DataTyKind::Struct(struct_dty) => struct_dty
                .attributes
                .iter()
                .map(|field| Ty::new(TyKind::Data(field.ty.clone()))),
            _ => panic!("Expected a struct data type, but found something else"),
        }
        .collect::<Vec<_>>();
        let inferred_generic_args = infer_kinded_args_from_mono_ty(
            &struct_ty.generic_params,
            struct_inst_tys
                .iter()
                .zip(inst_exprs.iter().map(|(_, expr)| expr.ty.as_ref().unwrap())),
        );
        let generic_args_len = generic_args.len();
        generic_args.extend(inferred_generic_args);
        let struct_ty = struct_ty.instantiate(&generic_args[generic_args_len..]);

        //Check if all constraints are fullfilled
        if let Some(unfulfilled_con) = struct_ty
            .constraints
            .iter()
            .find(|con| !self.gl_ctx.theta.check_constraint(con))
        {
            Err(TyError::UnfullfilledConstraint(unfulfilled_con.clone()))?;
        }

        //Check if every expression has the expected type
        inst_exprs
            .iter()
            .zip(match &struct_ty.mono_ty.dty().dty {
                DataTyKind::Struct(struct_dty) => struct_dty.attributes.iter(),
                _ => panic!("Expected a struct data type, but found something else"),
            })
            .try_for_each(|((_, expr), field)| {
                let found_ty = expr.ty.as_ref().unwrap();
                let expected_ty = Ty::new(TyKind::Data(field.ty.clone()));
                if expected_ty.eq_structure(found_ty) {
                    Ok(())
                } else {
                    Err(TyError::UnexpectedType {
                        expected: expected_ty.clone(),
                        found: found_ty.clone(),
                    })
                }
            })?;

        if let Some(unfulfilled_con) = struct_ty
            .constraints
            .iter()
            .find(|con| !self.gl_ctx.theta.check_constraint(con))
        {
            Err(TyError::UnfullfilledConstraint(unfulfilled_con.clone()))
        } else {
            Ok((ty_ctx, struct_ty.mono_ty))
        }
    }

    fn ty_check_range(
        &mut self,
        kind_ctx: &KindCtx,
        ty_ctx: TyCtx,
        exec: Exec,
        l: &mut Expr,
        u: &mut Expr,
    ) -> TyResult<(TyCtx, Ty)> {
        if exec != Exec::CpuThread && exec != Exec::GpuThread {
            return Err(TyError::IllegalExec);
        }

        let ty_ctx_l = self.ty_check_expr(kind_ctx, ty_ctx, exec, l)?;
        let ty_ctx_u = self.ty_check_expr(kind_ctx, ty_ctx_l, exec, u)?;

        if !matches!(
            &l.ty.as_ref().unwrap().ty,
            TyKind::Data(DataTy {
                dty: DataTyKind::Scalar(ScalarTy::I32),
                ..
            })
        ) {
            panic!("expected i32 for l in range")
        }
        if !matches!(
            &u.ty.as_ref().unwrap().ty,
            TyKind::Data(DataTy {
                dty: DataTyKind::Scalar(ScalarTy::I32),
                ..
            })
        ) {
            panic!("expected i32 for u in range")
        }

        Ok((
            ty_ctx_u,
            Ty::new(TyKind::Data(DataTy::new(DataTyKind::Range))),
        ))
    }

    fn ty_check_split(
        &self,
        kind_ctx: &KindCtx,
        ty_ctx: TyCtx,
        exec: Exec,
        r1: &Option<String>,
        r2: &Option<String>,
        own: Ownership,
        s: &Nat,
        view: &mut PlaceExpr,
    ) -> TyResult<(TyCtx, Ty)> {
        fn tag_loans(loans: &HashSet<Loan>, tag: SplitTag) -> HashSet<Loan> {
            loans
                .iter()
                .cloned()
                .map(|mut l| {
                    l.place_expr.split_tag_path.push(tag);
                    l
                })
                .collect()
        }
        fn split_loans(loans: HashSet<Loan>) -> (HashSet<Loan>, HashSet<Loan>) {
            let fst = tag_loans(&loans, SplitTag::Fst);
            let snd = tag_loans(&loans, SplitTag::Snd);
            (fst, snd)
        }

        let (ty_ctx_prv1, prv1) = TyChecker::infer_prv(ty_ctx, r1);
        let (ty_ctx_prv1_prv2, prv2) = TyChecker::infer_prv(ty_ctx_prv1, r2);
        if !(ty_ctx_prv1_prv2.loans_in_prv(&prv1)?.is_empty()) {
            return Err(TyError::PrvValueAlreadyInUse(prv1));
        }
        if !(ty_ctx_prv1_prv2.loans_in_prv(&prv2)?.is_empty()) {
            return Err(TyError::PrvValueAlreadyInUse(prv2));
        }
        let mems =
            self.place_expr_ty_mems_under_exec_own(kind_ctx, &ty_ctx_prv1_prv2, exec, own, view)?;

        let split_ty = if let TyKind::Data(DataTy {
            dty: DataTyKind::ArrayShape(elem_dty, n),
            ..
        }) = &view.ty.as_ref().unwrap().ty
        {
            if s > n {
                return Err(TyError::String(
                    "Trying to access array out-of-bounds.".to_string(),
                ));
            }

            let mem = if let Some(mem) = mems.last() {
                mem
            } else {
                panic!("An array view must always reside in memory.")
            };

            Ty::new(TyKind::Data(DataTy::new(DataTyKind::Tuple(vec![
                DataTy::new(DataTyKind::Ref(
                    Provenance::Value(prv1.clone()),
                    own,
                    mem.clone(),
                    Box::new(DataTy::new(DataTyKind::ArrayShape(
                        elem_dty.clone(),
                        s.clone(),
                    ))),
                )),
                DataTy::new(DataTyKind::Ref(
                    Provenance::Value(prv2.clone()),
                    own,
                    mem.clone(),
                    Box::new(DataTy::new(DataTyKind::ArrayShape(
                        elem_dty.clone(),
                        Nat::BinOp(BinOpNat::Sub, Box::new(n.clone()), Box::new(s.clone())),
                    ))),
                )),
            ]))))
        } else {
            return Err(TyError::UnexpectedTypeKind {
                expected_name: String::from("TyKind::Data"),
                found: view.ty.as_ref().unwrap().clone(),
            });
        };

        let loans = borrow_check::ownership_safe(
            self,
            kind_ctx,
            &ty_ctx_prv1_prv2,
            exec,
            &[],
            own,
            &view.clone(),
        )
        .map_err(|err| TyError::ConflictingBorrow(Box::new(view.clone()), Ownership::Uniq, err))?;
        let (fst_loans, snd_loans) = split_loans(loans);
        let prv1_to_loans = PrvMapping {
            prv: prv1,
            loans: fst_loans,
        };
        let prv2_to_loans = PrvMapping {
            prv: prv2,
            loans: snd_loans,
        };
        let split_ty_ctx = ty_ctx_prv1_prv2
            .append_prv_mapping(prv1_to_loans)
            .append_prv_mapping(prv2_to_loans);

        Ok((split_ty_ctx, split_ty))
    }

    fn infer_prv(ty_ctx: TyCtx, prv_name: &Option<String>) -> (TyCtx, String) {
        let (ty_ctx_r1, r1) = if let Some(prv) = prv_name.as_ref() {
            (ty_ctx, prv.clone())
        } else {
            let name = utils::fresh_name("r");
            (ty_ctx.append_prv_mapping(PrvMapping::new(&name)), name)
        };
        (ty_ctx_r1, r1)
    }

    fn ty_check_for_nat(
        &mut self,
        kind_ctx: &KindCtx,
        ty_ctx: TyCtx,
        exec: Exec,
        var: &Ident,
        range: &Nat,
        body: &mut Expr,
    ) -> TyResult<(TyCtx, Ty)> {
        let scoped_kind_ctx: KindCtx = kind_ctx.clone().append_idents(vec![IdentKinded {
            ident: var.clone(),
            kind: Kind::Nat,
        }]);
        let ty_ctx_1 = self.ty_check_expr(
            &scoped_kind_ctx,
            ty_ctx.clone().append_frame(vec![]),
            exec,
            body,
        )?;
        let ty_ctx_1_no_body = ty_ctx_1.drop_last_frame();
        if ty_ctx != ty_ctx_1_no_body {
            // let diff: Vec<_> = ty_ctx_1_no_body
            //     .prv_mappings()
            //     .filter(|new| ty_ctx.prv_mappings().any(|old| &old == new))
            //     .collect();
            // eprintln!("{:?}", diff);
            return Err(TyError::String(
                "Using a data type in loop that can only be used once.".to_string(),
            ));
        }
        Ok((
            ty_ctx,
            Ty::new(TyKind::Data(DataTy::new(DataTyKind::Scalar(
                ScalarTy::Unit,
            )))),
        ))
    }

    fn ty_check_for(
        &mut self,
        kind_ctx: &KindCtx,
        ty_ctx: TyCtx,
        exec: Exec,
        ident: &Ident,
        collec: &mut Expr,
        body: &mut Expr,
    ) -> TyResult<(TyCtx, Ty)> {
        let collec_ty_ctx = self.ty_check_expr(kind_ctx, ty_ctx, exec, collec)?;
        let ident_dty = match &collec.ty.as_ref().unwrap().ty {
            // TODO
            TyKind::Data(DataTy {
                dty: DataTyKind::Array(elem_dty, n),
                ..
            }) => unimplemented!(),
            TyKind::Data(DataTy {
                dty: DataTyKind::Ref(prv, own, mem, arr_dty),
                ..
            }) => match &arr_dty.as_ref().dty {
                DataTyKind::Array(elem_dty, _) => {
                    DataTyKind::Ref(prv.clone(), *own, mem.clone(), elem_dty.clone())
                }
                DataTyKind::ArrayShape(elem_dty, _) => {
                    DataTyKind::Ref(prv.clone(), *own, mem.clone(), elem_dty.clone())
                }
                _ => {
                    return Err(TyError::String(format!(
                        "Expected reference to array data type, but found {:?}",
                        *arr_dty
                    )))
                }
            },
            TyKind::Data(DataTy {
                dty: DataTyKind::Range,
                ..
            }) => DataTyKind::Scalar(ScalarTy::I32),
            _ => {
                return Err(TyError::String(format!(
                    "Expected array data type or reference to array data type, but found {:?}",
                    collec.ty.as_ref().unwrap()
                )));
            }
        };
        let collec_ty_ctx_with_ident =
            collec_ty_ctx
                .clone()
                .append_frame(vec![FrameEntry::Var(IdentTyped::new(
                    ident.clone(),
                    Ty::new(TyKind::Data(DataTy::new(ident_dty))),
                    Mutability::Const,
                ))]);
        let iter_ty_ctx = self.ty_check_expr(kind_ctx, collec_ty_ctx_with_ident, exec, body)?;
        let ty_ctx_no_body = iter_ty_ctx.drop_last_frame();
        if collec_ty_ctx != ty_ctx_no_body {
            return Err(TyError::String(
                "Using a data type in loop that can only be used once.".to_string(),
            ));
        }
        Ok((
            collec_ty_ctx,
            Ty::new(TyKind::Data(DataTy::new(DataTyKind::Scalar(
                ScalarTy::Unit,
            )))),
        ))
    }

    fn ty_check_while(
        &mut self,
        kind_ctx: &KindCtx,
        ty_ctx: TyCtx,
        exec: Exec,
        cond: &mut Expr,
        body: &mut Expr,
    ) -> TyResult<(TyCtx, Ty)> {
        let cond_ty_ctx = self.ty_check_expr(kind_ctx, ty_ctx, exec, cond)?;
        let body_ty_ctx =
            self.ty_check_expr(kind_ctx, cond_ty_ctx.append_frame(vec![]), exec, body)?;

        let body_outer_ty_ctx = body_ty_ctx.drop_last_frame();
        let cond_temp_ty_ctx =
            self.ty_check_expr(kind_ctx, body_outer_ty_ctx.clone(), exec, cond)?;
        if body_outer_ty_ctx != cond_temp_ty_ctx {
            return Err(TyError::String(
                "Context should have stayed the same".to_string(),
            ));
        }
        let body_temp_ty_ctx = self.ty_check_expr(
            kind_ctx,
            body_outer_ty_ctx.clone().append_frame(vec![]),
            exec,
            body,
        )?;
        if body_outer_ty_ctx != body_temp_ty_ctx.drop_last_frame() {
            return Err(TyError::String(
                "Context should have stayed the same".to_string(),
            ));
        }

        let cond_ty = cond.ty.as_ref().unwrap();
        let body_ty = body.ty.as_ref().unwrap();

        if !matches!(
            &cond_ty.ty,
            TyKind::Data(DataTy {
                dty: DataTyKind::Scalar(ScalarTy::Bool),
                ..
            })
        ) {
            return Err(TyError::String(format!(
                "Expected condition in while loop, instead got {:?}",
                cond_ty
            )));
        }
        if !matches!(
            &body_ty.ty,
            TyKind::Data(DataTy {
                dty: DataTyKind::Scalar(ScalarTy::Unit),
                ..
            })
        ) {
            return Err(TyError::String(format!(
                "Body of while loop is not of unit type, instead got {:?}",
                body_ty
            )));
        }
        Ok((
            body_outer_ty_ctx,
            Ty::new(TyKind::Data(DataTy::new(DataTyKind::Scalar(
                ScalarTy::Unit,
            )))),
        ))
    }

    fn ty_check_if_else(
        &mut self,
        kind_ctx: &KindCtx,
        ty_ctx: TyCtx,
        exec: Exec,
        cond: &mut Expr,
        case_true: &mut Expr,
        case_false: &mut Expr,
    ) -> TyResult<(TyCtx, Ty)> {
        // TODO deal with provenances in cases
        let cond_ty_ctx = self.ty_check_expr(kind_ctx, ty_ctx, exec, cond)?;
        let _case_true_ty_ctx =
            self.ty_check_expr(kind_ctx, cond_ty_ctx.clone(), exec, case_true)?;
        let case_false_ty_ctx = self.ty_check_expr(kind_ctx, cond_ty_ctx, exec, case_false)?;

        let cond_ty = cond.ty.as_ref().unwrap();
        let case_true_ty = case_true.ty.as_ref().unwrap();
        let case_false_ty = case_false.ty.as_ref().unwrap();

        if !matches!(
            &cond_ty.ty,
            TyKind::Data(DataTy {
                dty: DataTyKind::Scalar(ScalarTy::Bool),
                ..
            })
        ) {
            return Err(TyError::String(format!(
                "Expected condition in if case, instead got {:?}",
                cond_ty
            )));
        }
        if !matches!(
            &case_true_ty.ty,
            TyKind::Data(DataTy {
                dty: DataTyKind::Scalar(ScalarTy::Unit),
                ..
            })
        ) {
            return Err(TyError::String(format!(
                "Body of the true case is not of unit type, instead got {:?}",
                case_true_ty
            )));
        }
        if !matches!(
            &case_false_ty.ty,
            TyKind::Data(DataTy {
                dty: DataTyKind::Scalar(ScalarTy::Unit),
                ..
            })
        ) {
            return Err(TyError::String(format!(
                "Body of the false case is not of unit type, instead got {:?}",
                case_false_ty
            )));
        }

        Ok((
            case_false_ty_ctx,
            Ty::new(TyKind::Data(DataTy::new(DataTyKind::Scalar(
                ScalarTy::Unit,
            )))),
        ))
    }

    fn ty_check_if(
        &mut self,
        kind_ctx: &KindCtx,
        ty_ctx: TyCtx,
        exec: Exec,
        cond: &mut Expr,
        case_true: &mut Expr,
    ) -> TyResult<(TyCtx, Ty)> {
        // TODO deal with provenances in cases
        let cond_ty_ctx = self.ty_check_expr(kind_ctx, ty_ctx, exec, cond)?;
        let case_true_ty_ctx =
            self.ty_check_expr(kind_ctx, cond_ty_ctx.clone(), exec, case_true)?;

        let cond_ty = cond.ty.as_ref().unwrap();
        let case_true_ty = case_true.ty.as_ref().unwrap();

        if !matches!(
            &cond_ty.ty,
            TyKind::Data(DataTy {
                dty: DataTyKind::Scalar(ScalarTy::Bool),
                ..
            })
        ) {
            return Err(TyError::String(format!(
                "Expected condition in if case, instead got {:?}",
                cond_ty
            )));
        }
        if !matches!(
            &case_true_ty.ty,
            TyKind::Data(DataTy {
                dty: DataTyKind::Scalar(ScalarTy::Unit),
                ..
            })
        ) {
            return Err(TyError::String(format!(
                "Body of the true case is not of unit type, instead got {:?}",
                case_true_ty
            )));
        }

        Ok((
            case_true_ty_ctx,
            Ty::new(TyKind::Data(DataTy::new(DataTyKind::Scalar(
                ScalarTy::Unit,
            )))),
        ))
    }

    fn ty_check_par_branch(
        &mut self,
        kind_ctx: &KindCtx,
        ty_ctx: TyCtx,
        exec: Exec,
        parall_collec: &mut Expr,
        branch_idents: &[Ident],
        branch_bodies: &mut [Expr],
    ) -> TyResult<(TyCtx, Ty)> {
        let parall_collec_ty_ctx = self.ty_check_expr(kind_ctx, ty_ctx, exec, parall_collec)?;
        if let TyKind::Data(DataTy {
            dty: DataTyKind::SplitThreadHierchy(th, n),
            ..
        }) = &parall_collec.ty.as_ref().unwrap().ty
        {
            if branch_idents.len() != branch_bodies.len() {
                panic!(
                    "Amount of branch identifiers and amount of branches do not match:\
                            {} and {}",
                    branch_idents.len(),
                    branch_bodies.len()
                );
            }
            if branch_idents.len() != 2 {
                return Err(TyError::String(format!(
                    "Expected 2 parallel branches but found {}",
                    branch_idents.len()
                )));
            }
            let idents_typed = Self::parbranch_parall_ident_dty_from_split(
                branch_idents,
                th.as_ref().clone(),
                n.clone(),
            )?;
            let mut parbranch_ctx = parall_collec_ty_ctx.clone();
            for (it, bb) in idents_typed.into_iter().zip(branch_bodies) {
                let branch_ctx = parbranch_ctx.append_frame(vec![]).append_ident_typed(it);
                let branch_res_ctx = self.ty_check_expr(kind_ctx, branch_ctx, exec, bb)?;
                if bb.ty.as_ref().unwrap().ty != TyKind::Data(DataTy::new(Scalar(ScalarTy::Unit))) {
                    return Err(TyError::String(
                        "A par_branch branch must not return a value.".to_string(),
                    ));
                }
                parbranch_ctx = branch_res_ctx.drop_last_frame();
            }
            Ok((
                parbranch_ctx,
                Ty::new(TyKind::Data(DataTy::new(Scalar(ScalarTy::Unit)))),
            ))
        } else {
            Err(TyError::String(format!(
                "Unexpected type. Expected Split Parallel Collection but found: {:?}",
                &parall_collec.ty.as_ref().unwrap().ty
            )))
        }
    }

    fn parbranch_parall_ident_dty_from_split(
        idents: &[Ident],
        orig_th: ThreadHierchyTy,
        pos: Nat,
    ) -> TyResult<Vec<IdentTyped>> {
        let (lth, rth) = match orig_th {
            ThreadHierchyTy::BlockGrp(m1, m2, m3, n1, n2, n3) => (
                ThreadHierchyTy::BlockGrp(
                    pos.clone(),
                    m2.clone(),
                    m3.clone(),
                    n1.clone(),
                    n2.clone(),
                    n3.clone(),
                ),
                ThreadHierchyTy::BlockGrp(
                    Nat::BinOp(BinOpNat::Sub, Box::new(m1), Box::new(pos)),
                    m2,
                    m3,
                    n1,
                    n2,
                    n3,
                ),
            ),
            ThreadHierchyTy::ThreadGrp(n1, n2, n3) => (
                ThreadHierchyTy::ThreadGrp(pos.clone(), n2.clone(), n3.clone()),
                ThreadHierchyTy::ThreadGrp(
                    Nat::BinOp(BinOpNat::Sub, Box::new(n1), Box::new(pos)),
                    n2,
                    n3,
                ),
            ),
            _ => panic!("A non-splittable parallel resource should not exist here"),
        };
        let li = IdentTyped::new(
            idents[0].clone(),
            Ty::new(TyKind::Data(DataTy::new(DataTyKind::ThreadHierchy(
                Box::new(lth),
            )))),
            Mutability::Const,
        );
        let ri = IdentTyped::new(
            idents[1].clone(),
            Ty::new(TyKind::Data(DataTy::new(DataTyKind::ThreadHierchy(
                Box::new(rth),
            )))),
            Mutability::Const,
        );
        Ok(vec![li, ri])
    }

    // TODO split up groupings, i.e., deal with TupleViews and require enough functions.
    fn ty_check_par_for(
        &mut self,
        kind_ctx: &KindCtx,
        ty_ctx: TyCtx,
        exec: Exec,
        decls: &mut Option<Vec<Expr>>,
        parall_ident: &Option<Ident>,
        parall_collec: &mut Expr,
        input_idents: &[Ident],
        input_exprs: &mut [Expr],
        body: &mut Expr,
    ) -> TyResult<(TyCtx, Ty)> {
        fn to_exec(parall_collec: &Expr) -> TyResult<Exec> {
            match &parall_collec.ty.as_ref().unwrap().ty {
                TyKind::Data(DataTy {
                    dty: DataTyKind::ThreadHierchy(th_hy),
                    ..
                }) => match th_hy.as_ref() {
                    ThreadHierchyTy::BlockGrp(_, _, _, _, _, _) => Ok(Exec::GpuGrid),
                    ThreadHierchyTy::ThreadGrp(_, _, _) => Ok(Exec::GpuBlock),
                    ThreadHierchyTy::WarpGrp(_) => Ok(Exec::GpuBlock),
                    ThreadHierchyTy::Warp => Ok(Exec::GpuWarp),
                    // TODO error instead?
                    ThreadHierchyTy::Thread => Ok(Exec::GpuThread),
                },
                _ => panic!("Expected a parallel collection: Grid or Block."),
            }
        }

        // Add declarations to context
        let mut decl_ty_ctx = ty_ctx;
        for decls in decls {
            for d in decls {
                if !matches!(d.expr, ExprKind::LetUninit(_, _)) {
                    return Err(TyError::String(
                        "Only unitialized let declarations are allowed here.".to_string(),
                    ));
                }
                decl_ty_ctx = self.ty_check_expr(kind_ctx, decl_ty_ctx, Exec::GpuThread, d)?;
                // If the declaration is for shared memory, assume that it is assigned a value
                // automatically, therefore making the type non-dead.
                if let ExprKind::LetUninit(ident, t) = &d.expr {
                    if matches!(
                        &t.ty,
                        TyKind::Data(DataTy {
                            dty: DataTyKind::At(_, Memory::GpuShared),
                            ..
                        })
                    ) {
                        decl_ty_ctx = decl_ty_ctx.set_place_ty(
                            &Place {
                                ident: ident.clone(),
                                path: vec![],
                            },
                            t.as_ref().clone(),
                        );
                    }
                } else {
                    panic!("decl blocks allow only LetUninit. Something went wrong.");
                }
            }
        }

        let parall_collec_ty_ctx =
            self.ty_check_expr(kind_ctx, decl_ty_ctx, exec, parall_collec)?;
        let allowed_exec = to_exec(parall_collec)?;
        if allowed_exec != exec {
            return Err(TyError::String(format!(
                "Trying to run a parallel for-loop over {:?} inside of {:?}",
                parall_collec, exec
            )));
        }
        let mut input_ty_ctx = parall_collec_ty_ctx;
        for e in input_exprs.iter_mut() {
            input_ty_ctx = self.ty_check_expr(kind_ctx, input_ty_ctx, exec, e)?;
        }

        let input_idents_typed = TyChecker::type_input_idents(input_idents, input_exprs)?;
        let parall_ident_typed =
            TyChecker::parfor_parall_ident_ty_from_parall_collec(parall_ident, parall_collec)?;
        let body_exec = TyChecker::exec_for_parall_collec(&parall_ident_typed)?;
        let mut frm_ty = input_idents_typed
            .into_iter()
            .map(FrameEntry::Var)
            .collect::<Vec<_>>();
        if parall_ident_typed.is_some() {
            frm_ty.push(FrameEntry::Var(parall_ident_typed.unwrap()));
        }
        let ty_ctx_with_idents = input_ty_ctx.clone().append_frame(frm_ty);

        // Dismiss the resulting typing context. A par_for always synchronizes. Therefore everything
        // that is used for the par_for can safely be reused.
        let _body_ty_ctx = self.ty_check_expr(kind_ctx, ty_ctx_with_idents, body_exec, body)?;

        Ok((
            input_ty_ctx,
            Ty::new(TyKind::Data(DataTy::new(DataTyKind::Scalar(
                ScalarTy::Unit,
            )))),
        ))
    }

    fn type_input_idents(
        input_idents: &[Ident],
        input_exprs: &[Expr],
    ) -> TyResult<Vec<IdentTyped>> {
        if input_idents.len() != input_exprs.len() {
            return Err(TyError::String(
                "Amount of input identifiers and input shapes do not match".to_string(),
            ));
        }

        input_exprs
            .iter()
            .map(|e| {
                if let TyKind::Data(DataTy {
                    dty: DataTyKind::Ref(r, o, m, arr_view),
                    ..
                }) = &e.ty.as_ref().unwrap().ty
                {
                    if let DataTy {
                        dty: DataTyKind::ArrayShape(tty, n),
                        ..
                    } = arr_view.as_ref()
                    {
                        Ok(Ty::new(TyKind::Data(DataTy::new(DataTyKind::Ref(
                            r.clone(),
                            *o,
                            m.clone(),
                            tty.clone(),
                        )))))
                    } else {
                        Err(TyError::UnexpectedDataTypeKind {
                            expected_name: String::from("DataTyKind::ArrayShape"),
                            found: (**arr_view).clone(),
                        })
                    }
                } else {
                    Err(TyError::UnexpectedTypeKind {
                        expected_name: String::from("TyKind::Data"),
                        found: e.ty.as_ref().unwrap().clone(),
                    })
                }
            })
            .zip(input_idents)
            .map(|(ty, i)| Ok(IdentTyped::new(i.clone(), ty?, Mutability::Const)))
            .collect::<TyResult<Vec<_>>>()
    }

    fn parfor_parall_ident_ty_from_parall_collec(
        parall_ident: &Option<Ident>,
        parall_collec: &Expr,
    ) -> TyResult<Option<IdentTyped>> {
        if parall_ident.is_none() {
            return Ok(None);
        }
        let thread_hierchy_ty = match &parall_collec.ty.as_ref().unwrap().ty {
            TyKind::Data(DataTy {
                dty: DataTyKind::ThreadHierchy(th_hy),
                ..
            }) => match th_hy.as_ref() {
                ThreadHierchyTy::BlockGrp(_, _, _, m1, m2, m3) => {
                    ThreadHierchyTy::ThreadGrp(m1.clone(), m2.clone(), m3.clone())
                }
                ThreadHierchyTy::WarpGrp(_) => ThreadHierchyTy::Warp,
                ThreadHierchyTy::Warp | ThreadHierchyTy::ThreadGrp(_, _, _) => {
                    ThreadHierchyTy::Thread
                }
                ThreadHierchyTy::Thread => {
                    return Err(TyError::String(
                        "Thread is not a parallel execution resources.".to_string(),
                    ))
                }
            },
            _ => {
                return Err(TyError::String(
                    "Provided expression is not a parallel collection.".to_string(),
                ))
            }
        };
        Ok(Some(IdentTyped::new(
            parall_ident.as_ref().unwrap().clone(),
            Ty::new(TyKind::Data(DataTy::new(DataTyKind::ThreadHierchy(
                Box::new(thread_hierchy_ty),
            )))),
            Mutability::Const,
        )))
    }

    fn exec_for_parall_collec(parall_ident_typed: &Option<IdentTyped>) -> TyResult<Exec> {
        if parall_ident_typed.is_none() {
            return Ok(Exec::GpuThread);
        }
        let body_exec = if let TyKind::Data(DataTy {
            dty: DataTyKind::ThreadHierchy(th_hierchy),
            ..
        }) = &parall_ident_typed.as_ref().unwrap().ty.ty
        {
            match th_hierchy.as_ref() {
                ThreadHierchyTy::WarpGrp(_) | ThreadHierchyTy::ThreadGrp(_, _, _) => Exec::GpuBlock,
                ThreadHierchyTy::Warp => Exec::GpuWarp,
                ThreadHierchyTy::Thread => Exec::GpuThread,
                ThreadHierchyTy::BlockGrp(_, _, _, _, _, _) => {
                    return Err(TyError::String(
                        "Cannot parallelize over multiple Grids.".to_string(),
                    ))
                }
            }
        } else {
            panic!(
                "Expected a thread hierarchy type but found {:?}.",
                &parall_ident_typed.as_ref().unwrap().ty.ty
            )
        };
        Ok(body_exec)
    }

    fn ty_check_lambda(
        &mut self,
        kind_ctx: &KindCtx,
        ty_ctx: TyCtx,
        exec: Exec,
        params: &mut [ParamDecl],
        ret_dty: &DataTy,
        body: &mut Expr,
    ) -> TyResult<(TyCtx, Ty)> {
        // Build frame typing for this function
        let fun_frame = internal::append_idents_typed(
            &vec![],
            params
                .iter()
                .map(|ParamDecl { ident, ty, mutbl }| IdentTyped {
                    ident: ident.clone(),
                    ty: match ty {
                        Some(tty) => tty.clone(),
                        None => Ty::new(utils::fresh_ident("param_ty", TyKind::Ident)),
                    },
                    mutbl: *mutbl,
                })
                .collect(),
        );
        // Copy porvenance mappings into scope and append scope frame.
        // FIXME check that no variables are captured.
        let fun_ty_ctx = ty_ctx.clone().append_frame(fun_frame);

        self.ty_check_expr(kind_ctx, fun_ty_ctx, exec, body)?;

        // t <= t_f
        let empty_ty_ctx = subty::check(
            kind_ctx,
            TyCtx::new(),
            body.ty.as_ref().unwrap().dty(),
            ret_dty,
        )?;

        assert!(
            empty_ty_ctx.is_empty(),
            "Expected typing context to be empty. But TyCtx:\n {:?}",
            empty_ty_ctx
        );

        let fun_ty = Ty::new(TyKind::Fn(
            params
                .iter()
                .map(|decl| decl.ty.as_ref().unwrap().clone())
                .collect(),
            exec,
            Box::new(Ty::new(TyKind::Data(ret_dty.clone()))),
        ));

        Ok((ty_ctx, fun_ty))
    }

    fn ty_check_block(
        &mut self,
        kind_ctx: &KindCtx,
        ty_ctx: TyCtx,
        exec: Exec,
        prvs: &[String],
        body: &mut Expr,
    ) -> TyResult<(TyCtx, Ty)> {
        let mut ty_ctx_with_prvs = ty_ctx.append_frame(vec![]);
        for prv in prvs {
            ty_ctx_with_prvs = ty_ctx_with_prvs.append_prv_mapping(PrvMapping::new(prv))
        }
        // TODO do we have to check that the prvs in res_ty_ctx have loans now?
        let body_ty_ctx = self.ty_check_expr(kind_ctx, ty_ctx_with_prvs, exec, body)?;
        let res_ty_ctx = body_ty_ctx.drop_last_frame();
        Ok((res_ty_ctx, body.ty.as_ref().unwrap().clone()))
    }

    fn check_mutable(ty_ctx: &TyCtx, pl: &Place) -> TyResult<()> {
        let ident_ty = ty_ctx.ident_ty(&pl.ident)?;
        if ident_ty.mutbl != Mutability::Mut {
            return Err(TyError::AssignToConst(pl.to_place_expr()));
        }
        Ok(())
    }

    fn ty_check_assign_place(
        &mut self,
        kind_ctx: &KindCtx,
        ty_ctx: TyCtx,
        exec: Exec,
        pl_expr: &PlaceExpr,
        e: &mut Expr,
    ) -> TyResult<(TyCtx, Ty)> {
        let assigned_val_ty_ctx = self.ty_check_expr(kind_ctx, ty_ctx, exec, e)?;
        let pl = pl_expr.to_place().unwrap();
        let mut place_ty = assigned_val_ty_ctx.place_ty(&pl)?;
        // FIXME this should be checked for ArrayViews as well
        // fn contains_view_dty(ty: &TyKind) -> bool {
        //     unimplemented!()
        // }
        // if contains_view_dty(&place_ty.ty) {
        //     return Err(TyError::String(format!(
        //         "Reassigning views is forbidden. Trying to assign view {:?}",
        //         e
        //     )));
        // }
        Self::check_mutable(&assigned_val_ty_ctx, &pl)?;

        // If the place is not dead, check that it is safe to use, otherwise it is safe to use anyway.
        if !matches!(
            &place_ty.ty,
            TyKind::Data(DataTy {
                dty: DataTyKind::Dead(_),
                ..
            })
        ) {
            let pl_uniq_loans = borrow_check::ownership_safe(
                self,
                kind_ctx,
                &assigned_val_ty_ctx,
                exec,
                &[],
                Ownership::Uniq,
                pl_expr,
            )
            .map_err(|err| {
                TyError::ConflictingBorrow(Box::new(pl_expr.clone()), Ownership::Uniq, err)
            })?;
            // TODO remove this is always true if borrow_check::ownership_safe succeeds
            // assert_eq!(pl_uniq_loans.len(), 1);
            // let place_loan = Loan {
            //     place_expr: pl_expr.clone(),
            //     own: Ownership::Uniq,
            // };
            // if !matches!(pl_uniq_loans.get(&place_loan), Some(_)) {
            //     return Err(TyError::)
            // }
        }

        let after_subty_ctx = unify::sub_unify(
            kind_ctx,
            assigned_val_ty_ctx,
            e.ty.as_mut().unwrap(),
            &mut place_ty,
        )?;
        let adjust_place_ty_ctx = after_subty_ctx.set_place_ty(&pl, e.ty.as_ref().unwrap().clone());
        Ok((
            adjust_place_ty_ctx.without_reborrow_loans(pl_expr),
            Ty::new(TyKind::Data(DataTy::new(DataTyKind::Scalar(
                ScalarTy::Unit,
            )))),
        ))
    }

    fn ty_check_assign_deref(
        &mut self,
        kind_ctx: &KindCtx,
        ty_ctx: TyCtx,
        exec: Exec,
        deref_expr: &mut PlaceExpr,
        e: &mut Expr,
    ) -> TyResult<(TyCtx, Ty)> {
        let assigned_val_ty_ctx = self.ty_check_expr(kind_ctx, ty_ctx, exec, e)?;
        self.place_expr_ty_under_exec_own(
            kind_ctx,
            &assigned_val_ty_ctx,
            exec,
            Ownership::Uniq,
            deref_expr,
        )?;

        borrow_check::ownership_safe(
            self,
            kind_ctx,
            &assigned_val_ty_ctx,
            exec,
            &[],
            Ownership::Uniq,
            &deref_expr,
        )
        .map_err(|err| {
            TyError::ConflictingBorrow(Box::new(deref_expr.clone()), Ownership::Uniq, err)
        })?;

        let deref_ty = &mut deref_expr.ty.as_mut().unwrap();
        let after_subty_ctx = unify::sub_unify(
            kind_ctx,
            assigned_val_ty_ctx,
            e.ty.as_mut().unwrap(),
            deref_ty,
        )?;

        if !deref_ty.is_fully_alive() {
            return Err(TyError::String(
                "Trying to assign through reference, to a type which is not fully alive."
                    .to_string(),
            ));
        }

        if let TyKind::Data(_) = &deref_ty.ty {
            Ok((
                after_subty_ctx.without_reborrow_loans(deref_expr),
                Ty::new(TyKind::Data(DataTy::new(DataTyKind::Scalar(
                    ScalarTy::Unit,
                )))),
            ))
        } else {
            Err(TyError::String(
                "Trying to dereference view type which is not allowed.".to_string(),
            ))
        }
    }

    fn ty_check_idx_assign(
        &mut self,
        kind_ctx: &KindCtx,
        ty_ctx: TyCtx,
        exec: Exec,
        pl_expr: &mut PlaceExpr,
        idx: &Nat,
        e: &mut Expr,
    ) -> TyResult<(TyCtx, Ty)> {
        if exec != Exec::CpuThread && exec != Exec::GpuThread {
            return Err(TyError::String(format!(
                "Trying to assign to memory from {}.",
                exec
            )));
        }

        let assigned_val_ty_ctx = self.ty_check_expr(kind_ctx, ty_ctx, exec, e)?;
        self.place_expr_ty_under_exec_own(
            kind_ctx,
            &assigned_val_ty_ctx,
            exec,
            Ownership::Uniq,
            pl_expr,
        )?;
        let (n, own, mem, dty) = match &pl_expr.ty.as_ref().unwrap().ty {
            TyKind::Data(DataTy {
                dty: DataTyKind::Array(elem_dty, n),
                ..
            }) => unimplemented!(), //(Ty::Data(*elem_ty), n),
            TyKind::Data(DataTy {
                dty: DataTyKind::At(arr_dty, mem),
                ..
            }) => {
                if let DataTy {
                    dty: DataTyKind::Array(elem_dty, n),
                    ..
                } = arr_dty.as_ref()
                {
                    unimplemented!() //(Ty::Data(*elem_ty), n)
                } else {
                    return Err(TyError::String(
                        "Trying to index into non array type.".to_string(),
                    ));
                }
            }
            // FIXME is this allowed? There is no reborrow but this leaks the lifetime and does not
            //  consume the array view.
            TyKind::Data(DataTy {
                dty: DataTyKind::Ref(prv, own, mem, arr_view),
                ..
            }) => match &arr_view.dty {
                DataTyKind::ArrayShape(sdty, n) if matches!(&sdty.dty, DataTyKind::Scalar(_)) => {
                    (n, own, mem, sdty.as_ref())
                }
                DataTyKind::ArrayShape(_, _) => return Err(TyError::AssignToView),
                _ => {
                    return Err(TyError::String(
                        "Expected a reference to array view.".to_string(),
                    ))
                }
            },
            _ => {
                return Err(TyError::String(
                    "Trying to index into non array type.".to_string(),
                ))
            }
        };

        if !dty.is_fully_alive() {
            return Err(TyError::String(
                "Trying to assign through reference, to a type which is not fully alive."
                    .to_string(),
            ));
        }
        Self::accessible_memory(exec, mem)?;

        if own != &Ownership::Uniq {
            return Err(TyError::String(
                "Cannot assign through shared references.".to_string(),
            ));
        }

        if n <= idx {
            return Err(TyError::String(
                "Trying to access array out-of-bounds.".to_string(),
            ));
        }

        borrow_check::ownership_safe(
            self,
            kind_ctx,
            &assigned_val_ty_ctx,
            exec,
            &[],
            Ownership::Uniq,
            pl_expr,
        )
        .map_err(|err| {
            TyError::ConflictingBorrow(Box::new(pl_expr.clone()), Ownership::Shrd, err)
        })?;

        let after_subty_ctx = subty::check(
            kind_ctx,
            assigned_val_ty_ctx,
            e.ty.as_ref().unwrap().dty(),
            &dty,
        )?;

        Ok((
            after_subty_ctx,
            Ty::new(TyKind::Data(DataTy::new(DataTyKind::Scalar(
                ScalarTy::Unit,
            )))),
        ))
    }

    fn ty_check_index_copy(
        &mut self,
        kind_ctx: &KindCtx,
        ty_ctx: TyCtx,
        exec: Exec,
        pl_expr: &mut PlaceExpr,
        idx: &mut Nat,
    ) -> TyResult<(TyCtx, Ty)> {
        // TODO refactor
        borrow_check::ownership_safe(self, kind_ctx, &ty_ctx, exec, &[], Ownership::Shrd, pl_expr)
            .map_err(|err| {
                TyError::ConflictingBorrow(Box::new(pl_expr.clone()), Ownership::Shrd, err)
            })?;
        self.place_expr_ty_under_exec_own(kind_ctx, &ty_ctx, exec, Ownership::Shrd, pl_expr)?;
        let (elem_dty, n) = match pl_expr.ty.as_ref().unwrap().ty.clone() {
            TyKind::Data(DataTy {
                dty: DataTyKind::Array(elem_dty, n),
                ..
            }) => (*elem_dty, n),
            TyKind::Data(DataTy {
                dty: DataTyKind::At(arr_dty, _),
                ..
            }) => {
                if let DataTyKind::Array(elem_ty, n) = &arr_dty.dty {
                    (elem_ty.as_ref().clone(), n.clone())
                } else {
                    return Err(TyError::String(
                        "Trying to index into non array type.".to_string(),
                    ));
                }
            }
            TyKind::Data(DataTy {
                dty: DataTyKind::Ref(prv, own, mem, dty),
                ..
            }) => {
                match &dty.dty {
                    DataTyKind::ArrayShape(sty, n) if matches!(&sty.dty, DataTyKind::Scalar(_)) => {
                        (sty.as_ref().clone(), n.clone())
                    }
                    DataTyKind::ArrayShape(view_ty, n) => {
                        Self::accessible_memory(exec, &mem)?;
                        // TODO is ownership checking necessary here?
                        (
                            DataTy::new(DataTyKind::Ref(prv, own, mem, view_ty.clone())),
                            n.clone(),
                        )
                    }
                    DataTyKind::Array(elem_ty, n) => (elem_ty.as_ref().clone(), n.clone()),
                    _ => {
                        return Err(TyError::String(
                            "Expected a reference as element type of array view.".to_string(),
                        ))
                    }
                }
            }
            _ => {
                return Err(TyError::String(
                    "Trying to index into non array type.".to_string(),
                ))
            }
        };

        if &n < idx {
            return Err(TyError::String(
                "Trying to access array out-of-bounds.".to_string(),
            ));
        }

        if elem_dty.copyable() {
            Ok((ty_ctx, Ty::new(TyKind::Data(elem_dty))))
        } else {
            Err(TyError::String(format!(
                "Cannot move out of array type: {:?}",
                elem_dty
            )))
        }
    }

    // FIXME currently assumes that binary operators exist only for f32 and i32 and that both
    //  arguments have to be of the same type
    fn ty_check_binary_op(
        &mut self,
        kind_ctx: &KindCtx,
        ty_ctx: TyCtx,
        exec: Exec,
        bin_op: &BinOp,
        lhs: &mut Expr,
        rhs: &mut Expr,
    ) -> TyResult<(TyCtx, Ty)> {
        // FIXME certain operations should only be allowed for certain data types
        //      true > false is currently valid
        let lhs_ty_ctx = self.ty_check_expr(kind_ctx, ty_ctx, exec, lhs)?;
        let rhs_ty_ctx = self.ty_check_expr(kind_ctx, lhs_ty_ctx, exec, rhs)?;

        let lhs_ty = lhs.ty.as_ref().unwrap();
        let rhs_ty = rhs.ty.as_ref().unwrap();
        let ret = match bin_op {
            BinOp::Add
            | BinOp::Sub
            | BinOp::Mul
            | BinOp::Div
            | BinOp::Mod
            | BinOp::And
            | BinOp::Or => lhs_ty.clone(),
            BinOp::Eq | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge | BinOp::Neq => Ty::new(
                TyKind::Data(DataTy::new(DataTyKind::Scalar(ScalarTy::Bool))),
            ),
        };
        // let fresh_id = constrain::fresh_ident("p_bin_op", DataTyKind::Ident);
        // let operand_ty = Ty::new(TyKind::Data(DataTy::new(fresh_id)));
        // self.term_constr
        //     .constrain(&mut rhs_ty_ctx, lhs_ty, &operand_ty)?;
        // self.term_constr
        //     .constrain(&mut rhs_ty_ctx, rhs_ty, &operand_ty)?;
        match (&lhs_ty.ty, &rhs_ty.ty) {
            (TyKind::Data(dty1), TyKind::Data(dty2)) => match (&dty1.dty, &dty2.dty) {
                (
                    DataTyKind::Scalar(ScalarTy::F32),
                    DataTyKind::Scalar(ScalarTy::F32),
                ) |
                ( DataTyKind::Scalar(ScalarTy::F64), DataTyKind::Scalar(ScalarTy::F64)) |
                (   DataTyKind::Scalar(ScalarTy::I32),
                    DataTyKind::Scalar(ScalarTy::I32),
                ) |
                (    DataTyKind::Scalar(ScalarTy::Bool),
                    DataTyKind::Scalar(ScalarTy::Bool),
                ) => Ok((rhs_ty_ctx, ret)),
                _ => Err(TyError::String(format!(
                    "Expected the same number types for operator {}, instead got\n Lhs: {:?}\n Rhs: {:?}",
                    bin_op, lhs, rhs
                )))
            }
            _ => Err(TyError::String(format!(
            "Expected the same number types for operator {}, instead got\n Lhs: {:?}\n Rhs: {:?}",
            bin_op, lhs, rhs
        ))),
        }
        // Ok((rhs_ty_ctx, operand_ty))
    }

    // FIXME currently assumes that binary operators exist only for f32 and i32
    fn ty_check_unary_op(
        &mut self,
        kind_ctx: &KindCtx,
        ty_ctx: TyCtx,
        exec: Exec,
        un_op: &UnOp,
        e: &mut Expr,
    ) -> TyResult<(TyCtx, Ty)> {
        let res_ctx = self.ty_check_expr(kind_ctx, ty_ctx, exec, e)?;
        let e_ty = e.ty.as_ref().unwrap();
        match &e_ty.ty {
            TyKind::Data(DataTy {
                dty: DataTyKind::Scalar(ScalarTy::F32),
                ..
            })
            | TyKind::Data(DataTy {
                dty: DataTyKind::Scalar(ScalarTy::I32),
                ..
            }) => Ok((res_ctx, e_ty.clone())),
            _ => Err(TyError::String(format!(
                "Exected a number type (i.e., f32 or i32), but found {:?}",
                e_ty
            ))),
        }
    }

    fn ty_check_app(
        &mut self,
        kind_ctx: &KindCtx,
        ty_ctx: TyCtx,
        exec: Exec,
        path: &mut Path,
        fun_kind: &mut Option<FunctionKind>,
        ef: &mut Expr,
        k_args: &mut Vec<ArgKinded>,
        args: &mut [Expr],
    ) -> TyResult<(TyCtx, Ty)> {
        //Tycheck args
        let mut res_ty_ctx = ty_ctx;
        for arg in args.iter_mut() {
            res_ty_ctx = self.ty_check_expr(kind_ctx, res_ty_ctx, exec, arg)?;
        }

        //Get function name
        let fun_name = if let ExprKind::PlaceExpr(place_expr) = &ef.expr {
            let place = place_expr.to_place().unwrap();
            place.ident
        } else {
            panic!("function is not a place expr");
        };
        //Replace InferFromFirstArg-path by dty of first arg
        if let Path::InferFromFirstArg = path {
            let dty = args.first().unwrap().ty.as_ref().unwrap().dty().clone();
            *path = Path::DataTy(match dty.dty {
                DataTyKind::Ref(_, _, _, dty) => *dty,
                _ => dty,
            })
        }
        //Infer function_kind from path
        *fun_kind = Some(match path {
            Path::Empty => FunctionKind::GlobalFun,
            Path::DataTy(dty) => {
                self.ty_well_formed(
                    kind_ctx,
                    &res_ty_ctx,
                    exec,
                    &Ty::new(TyKind::Data(dty.clone())),
                )?;

                match &dty.dty {
                    //If this is an ident only trait-functions can be called
                    DataTyKind::Ident(ident) => {
                        self.gl_ctx.trait_fun_name(&fun_name.name, &ident)?.fun_kind
                    }
                    //Else this dty corresponds to a concrete impl
                    _ => self
                        .gl_ctx
                        .impl_fun_name_by_dty(&fun_name.name, dty)?
                        .fun_kind
                        .clone(),
                }
            }
            Path::InferFromFirstArg => panic!("This should be already replaced by Path::DataTy"),
        });

        //Get type_scheme of function from context
        let fun_ty =
        // place should be an identifier referring to a globally declared function
        if let Ok(fun_ty) = self.gl_ctx.fun_ty_by_ident(&fun_name, &fun_kind.as_ref().unwrap()) {
            //TODO how to set a type for ef which is a typescheme?

            //TODO this is now the function monotype, not the function type
            //Is this a problem?
            ef.ty = Some(fun_ty.mono_ty.clone());

            fun_ty.clone()
        } else {
            Err(TyError::String(format!(
                "The provided function expression\n {:?}\n is not a identifier for a declared function",
                ef
            )))?
        };

        // TODO check well-kinded: FrameTyping, Prv, Ty
        let (f_subst, mut f_mono_ty) = Self::dep_app(&fun_ty, k_args)?;
        let (f_subst_param_tys, exec_f, f_subst_ret_ty) =
            if let TyKind::Fn(f_subst_param_tys, exec_f, f_subst_ret_ty) = &f_subst.mono_ty.ty {
                (f_subst_param_tys, exec_f, f_subst_ret_ty)
            } else {
                panic!("Expected function type but found something else.")
            };
        let exec_f = if !exec_f.callable_in(exec) {
            return Err(TyError::String(format!(
                "Trying to apply function for execution resource `{}` \
                under execution resource `{}`",
                exec_f, exec
            )));
        } else {
            exec_f
        };

        let ret_ty = Ty::new(utils::fresh_ident("ret_ty", TyKind::Ident));
        unify::unify(
            &mut f_mono_ty,
            &mut Ty::new(TyKind::Fn(
                args.iter()
                    .map(|arg| arg.ty.as_ref().unwrap().clone())
                    .collect(),
                *exec_f,
                Box::new(ret_ty),
            )),
        )?;

        //Infer remaing kinded args
        let (f_mono_param_tys, _, f_mono_ret_ty) =
            if let TyKind::Fn(f_subst_param_tys, exec_f, f_subst_ret_ty) = &f_mono_ty.ty {
                (f_subst_param_tys, exec_f, f_subst_ret_ty)
            } else {
                panic!("Expected function type but found something else.")
            };
        let inferred_k_args = infer_kinded_args_from_mono_ty(
            &f_subst.generic_params,
            f_subst_param_tys
                .iter()
                .zip(f_mono_param_tys.iter())
                .chain(std::iter::once(&**f_subst_ret_ty).zip(std::iter::once(&**f_mono_ret_ty))),
        );
        k_args.extend(inferred_k_args);

        //Check if all constraints of the function are fullfilled
        if let Some(unfulfilled_con) = fun_ty
            .constraints
            .iter()
            .map(|con| fun_ty.instantiate_single(con, k_args))
            .find(|con| !self.gl_ctx.theta.check_constraint(con))
        {
            Err(TyError::UnfullfilledConstraint(unfulfilled_con.clone()))?;
        }

        // TODO check provenance relations
        return Ok((res_ty_ctx, (**f_mono_ret_ty).clone()));
    }

    fn dep_app(ty_scheme: &TypeScheme, k_args: &[ArgKinded]) -> TyResult<(TypeScheme, Ty)> {
        if ty_scheme.generic_params.len() < k_args.len() {
            return Err(TyError::WrongNumberOfGenericParams {
                expected: ty_scheme.generic_params.len(),
                found: k_args.len(),
            });
        }
        Self::check_args_have_correct_kinds(
            &ty_scheme.generic_params[0..k_args.len()].to_vec(),
            &k_args.to_vec(),
        )?;
        let fun_ty_subs = ty_scheme.instantiate(k_args);
        let (fun_mono_ty, _) = unify::inst_ty_scheme(&fun_ty_subs);

        Ok((fun_ty_subs, fun_mono_ty))
    }

    fn check_args_have_correct_kinds(
        expected: &Vec<IdentKinded>,
        kv: &Vec<ArgKinded>,
    ) -> TyResult<()> {
        if expected.len() == kv.len() {
            iter_TyResult_to_TyResult!(expected
                .iter()
                .zip(kv.iter())
                .map(|(gen, arg)| TyChecker::check_arg_has_correct_kind(&gen.kind, arg)))
        } else {
            Err(TyError::WrongNumberOfGenericParams {
                expected: expected.len(),
                found: kv.len(),
            })
        }
    }

    fn check_arg_has_correct_kind(expected: &Kind, kv: &ArgKinded) -> TyResult<()> {
        if expected == &kv.kind() {
            Ok(())
        } else {
            Err(TyError::WrongKind {
                expected: *expected,
                found: kv.kind(),
            })
        }
    }

    fn ty_check_tuple(
        &mut self,
        kind_ctx: &KindCtx,
        ty_ctx: TyCtx,
        exec: Exec,
        elems: &mut [Expr],
    ) -> TyResult<(TyCtx, Ty)> {
        let mut tmp_ty_ctx = ty_ctx;
        for elem in elems.iter_mut() {
            tmp_ty_ctx = self.ty_check_expr(kind_ctx, tmp_ty_ctx, exec, elem)?;
        }
        let elem_tys: TyResult<Vec<_>> = elems
            .iter()
            .map(|elem| match &elem.ty.as_ref().unwrap().ty {
                TyKind::Data(dty) => Ok(dty.clone()),
                TyKind::Ident(_) => Err(TyError::String(
                    "Tuple elements must be data types, but found general type identifier."
                        .to_string(),
                )),
                TyKind::Fn(_, _, _) => Err(TyError::String(
                    "Tuple elements must be data types, but found function type.".to_string(),
                )),
                TyKind::Dead(_) => {
                    panic!(
                        "It shouldn't be possible to pass a value of a dead type\
                        to a tuple constructor."
                    )
                }
            })
            .collect();
        Ok((
            tmp_ty_ctx,
            Ty::new(TyKind::Data(DataTy::new(DataTyKind::Tuple(elem_tys?)))),
        ))
    }

    fn ty_check_proj(
        &mut self,
        kind_ctx: &KindCtx,
        ty_ctx: TyCtx,
        exec: Exec,
        e: &mut Expr,
        i: &ProjEntry,
    ) -> TyResult<(TyCtx, Ty)> {
        if let ExprKind::PlaceExpr(_) = e.expr {
            panic!("Place expression should have been typechecked by a different rule.")
        }

        let tuple_ty_ctx = self.ty_check_expr(kind_ctx, ty_ctx, exec, e)?;
        let elem_ty = proj_elem_ty(e.ty.as_ref().unwrap(), i)?;

        Ok((tuple_ty_ctx, elem_ty))
    }

    fn ty_check_array(
        &mut self,
        kind_ctx: &KindCtx,
        mut ty_ctx: TyCtx,
        exec: Exec,
        elems: &mut Vec<Expr>,
    ) -> TyResult<(TyCtx, Ty)> {
        assert!(!elems.is_empty());
        for elem in elems.iter_mut() {
            ty_ctx = self.ty_check_expr(kind_ctx, ty_ctx, exec, elem)?;
        }
        let ty = elems.first().unwrap().ty.as_ref();
        if !matches!(&ty.unwrap().ty, TyKind::Data(_)) {
            return Err(TyError::String(
                "Array elements cannot be views.".to_string(),
            ));
        }
        if elems.iter().any(|elem| ty != elem.ty.as_ref()) {
            Err(TyError::String(
                "Not all provided elements have the same type.".to_string(),
            ))
        } else {
            Ok((
                ty_ctx,
                Ty::new(TyKind::Data(DataTy::new(DataTyKind::Array(
                    Box::new(ty.as_ref().unwrap().dty().clone()),
                    Nat::Lit(elems.len()),
                )))),
            ))
        }
    }

    fn ty_check_literal(ty_ctx: TyCtx, l: &mut Lit) -> (TyCtx, Ty) {
        let scalar_data = match l {
            Lit::Unit => ScalarTy::Unit,
            Lit::Bool(_) => ScalarTy::Bool,
            Lit::I32(_) => ScalarTy::I32,
            Lit::U32(_) => ScalarTy::U32,
            Lit::F32(_) => ScalarTy::F32,
            Lit::F64(_) => ScalarTy::F64,
        };
        (
            ty_ctx,
            Ty::new(TyKind::Data(DataTy::new(DataTyKind::Scalar(scalar_data)))),
        )
    }

    fn type_idents(pattern: &Pattern, dty: DataTy) -> Vec<IdentTyped> {
        match (pattern, dty.dty) {
            (Pattern::Tuple(tuple_elems), DataTyKind::Tuple(tuple_dtys)) => tuple_elems
                .iter()
                .zip(tuple_dtys)
                .fold(vec![], |mut acc, (tp, dty)| {
                    acc.append(&mut TyChecker::type_idents(tp, dty));
                    acc
                }),
            (Pattern::Ident(mutbl, ident), d) => {
                vec![IdentTyped::new(
                    ident.clone(),
                    Ty::new(TyKind::Data(DataTy::new(d))),
                    *mutbl,
                )]
            }
            _ => panic!("Pattern and data type do not match."),
        }
    }

    fn infer_pattern_ident_tys(
        ty_ctx: TyCtx,
        pattern: &Pattern,
        pattern_ty: &Ty,
    ) -> TyResult<TyCtx> {
        match (pattern, &pattern_ty.ty) {
            (Pattern::Ident(mutbl, ident), ident_ty) => {
                let ident_with_annotated_ty =
                    IdentTyped::new(ident.clone(), Ty::new(ident_ty.clone()), *mutbl);
                Ok(ty_ctx.append_ident_typed(ident_with_annotated_ty))
            }
            (
                Pattern::Tuple(patterns),
                TyKind::Data(DataTy {
                    dty: DataTyKind::Tuple(elem_tys),
                    ..
                }),
            ) => Ok(patterns
                .iter()
                .zip(elem_tys)
                .try_fold(ty_ctx, |ctx, (p, tty)| {
                    TyChecker::infer_pattern_ident_tys(ctx, p, &Ty::new(TyKind::Data(tty.clone())))
                })?),
            _ => Err(TyError::PatternAndTypeDoNotMatch),
        }
    }

    fn infer_pattern_ty(
        kind_ctx: &KindCtx,
        ty_ctx: TyCtx,
        pattern: &Pattern,
        pattern_ty: &mut Option<Ty>,
        assign_ty: &mut Ty,
    ) -> TyResult<TyCtx> {
        let (ty_ctx_sub, pattern_ty) = if let Some(pty) = pattern_ty {
            (
                unify::sub_unify(kind_ctx, ty_ctx, assign_ty, pty)?,
                pty.clone(),
            )
        } else {
            (ty_ctx, assign_ty.clone())
        };
        TyChecker::infer_pattern_ident_tys(ty_ctx_sub, pattern, &pattern_ty)
    }

    fn ty_check_let(
        &mut self,
        kind_ctx: &KindCtx,
        ty_ctx: TyCtx,
        exec: Exec,
        pattern: &Pattern,
        pattern_ty: &mut Option<Ty>,
        expr: &mut Expr,
    ) -> TyResult<(TyCtx, Ty)> {
        let ty_ctx_e = self.ty_check_expr(kind_ctx, ty_ctx, exec, expr)?;
        let e_ty = expr.ty.as_mut().unwrap();
        let ty_ctx_with_idents =
            TyChecker::infer_pattern_ty(kind_ctx, ty_ctx_e, pattern, pattern_ty, e_ty)?;
        Ok((
            ty_ctx_with_idents,
            Ty::new(TyKind::Data(DataTy::new(DataTyKind::Scalar(
                ScalarTy::Unit,
            )))),
        ))
    }

    // TODO respect exec?
    fn ty_check_let_uninit(
        ty_ctx: TyCtx,
        exec: Exec,
        ident: &Ident,
        ty: &Ty,
    ) -> TyResult<(TyCtx, Ty)> {
        if let TyKind::Data(dty) = &ty.ty {
            let ident_with_ty = IdentTyped::new(
                ident.clone(),
                Ty::new(TyKind::Data(DataTy::new(DataTyKind::Dead(Box::new(
                    dty.clone(),
                ))))),
                Mutability::Mut,
            );
            let ty_ctx_with_ident = ty_ctx.append_ident_typed(ident_with_ty);
            Ok((
                ty_ctx_with_ident,
                Ty::new(TyKind::Data(DataTy::new(DataTyKind::Scalar(
                    ScalarTy::Unit,
                )))),
            ))
        } else {
            Err(TyError::MutabilityNotAllowed(ty.clone()))
        }
    }

    fn ty_check_seq(
        &mut self,
        kind_ctx: &KindCtx,
        ty_ctx: TyCtx,
        exec: Exec,
        es: &mut [Expr],
    ) -> TyResult<(TyCtx, Ty)> {
        let mut ty_ctx = ty_ctx;
        for e in &mut *es {
            ty_ctx = self
                .ty_check_expr(kind_ctx, ty_ctx, exec, e)?
                .garbage_collect_loans();
        }
        Ok((ty_ctx, es.last().unwrap().ty.as_ref().unwrap().clone()))
    }

    fn ty_check_pl_expr_with_deref(
        &mut self,
        kind_ctx: &KindCtx,
        ty_ctx: TyCtx,
        exec: Exec,
        pl_expr: &mut PlaceExpr,
    ) -> TyResult<(TyCtx, Ty)> {
        // TODO refactor
        borrow_check::ownership_safe(self, kind_ctx, &ty_ctx, exec, &[], Ownership::Shrd, pl_expr)
            .map_err(|err| {
                TyError::ConflictingBorrow(Box::new(pl_expr.clone()), Ownership::Shrd, err)
            })?;
        self.place_expr_ty_under_exec_own(kind_ctx, &ty_ctx, exec, Ownership::Shrd, pl_expr)?;
        if !pl_expr.ty.as_ref().unwrap().is_fully_alive() {
            return Err(TyError::String(format!(
                "Part of Place {:?} was moved before.",
                pl_expr
            )));
        }
        unify::unify(
            pl_expr.ty.as_mut().unwrap(),
            &mut Ty::new(TyKind::Data(DataTy::with_constr(
                utils::fresh_ident("pl_deref", DataTyKind::Ident),
                vec![ConstraintOld::Copyable],
            ))),
        )?;
        if pl_expr.ty.as_ref().unwrap().copyable() {
            Ok((ty_ctx, pl_expr.ty.as_ref().unwrap().clone()))
        } else {
            Err(TyError::String("Data type is not copyable.".to_string()))
        }
    }

    fn ty_check_pl_expr_without_deref(
        &self,
        kind_ctx: &KindCtx,
        ty_ctx: TyCtx,
        exec: Exec,
        pl_expr: &PlaceExpr,
    ) -> TyResult<(TyCtx, Ty)> {
        let place = pl_expr.to_place().unwrap();
        // If place is an identifier referring to a globally declared function
        let (res_ty_ctx, pl_ty) = if let Ok(_) = self
            .gl_ctx
            .fun_ty_by_ident(&place.ident, &FunctionKind::GlobalFun)
        {
            //TODO FunctionKind::GlobalFun right???
            panic!("function identifiers should only appear in App-expressions")
        } else {
            // If place is NOT referring to a globally declared function
            let pl_ty = ty_ctx.place_ty(&place)?;
            if !pl_ty.is_fully_alive() {
                return Err(TyError::String(format!(
                    "Part of Place {:?} was moved before.",
                    pl_expr
                )));
            }
            let res_ty_ctx = if pl_ty.copyable() {
                // TODO refactor
                borrow_check::ownership_safe(
                    self,
                    kind_ctx,
                    &ty_ctx,
                    exec,
                    &[],
                    Ownership::Shrd,
                    pl_expr,
                )
                .map_err(|err| {
                    TyError::ConflictingBorrow(Box::new(pl_expr.clone()), Ownership::Shrd, err)
                })?;
                ty_ctx
            } else {
                borrow_check::ownership_safe(
                    self,
                    kind_ctx,
                    &ty_ctx,
                    exec,
                    &[],
                    Ownership::Uniq,
                    pl_expr,
                )
                .map_err(|err| {
                    TyError::ConflictingBorrow(Box::new(pl_expr.clone()), Ownership::Uniq, err)
                })?;
                ty_ctx.kill_place(&place)
            };
            (res_ty_ctx, pl_ty)
        };

        Ok((res_ty_ctx, pl_ty))
    }

    fn ty_check_borrow(
        &self,
        kind_ctx: &KindCtx,
        ty_ctx: TyCtx,
        exec: Exec,
        prv_val_name: &Option<String>,
        own: Ownership,
        pl_expr: &mut PlaceExpr,
    ) -> TyResult<(TyCtx, Ty)> {
        // If borrowing a place uniquely, is it mutable?
        if let Some(place) = pl_expr.to_place() {
            if own == Ownership::Uniq && ty_ctx.ident_ty(&place.ident)?.mutbl == Mutability::Const {
                return Err(TyError::ConstBorrow(pl_expr.clone()));
            }
        }
        let (impl_ctx, prv_val_name) = TyChecker::infer_prv(ty_ctx, prv_val_name);

        if !impl_ctx.loans_in_prv(&prv_val_name)?.is_empty() {
            return Err(TyError::PrvValueAlreadyInUse(prv_val_name.to_string()));
        }
        let loans =
            borrow_check::ownership_safe(self, kind_ctx, &impl_ctx, exec, &[], own, pl_expr)
                .map_err(|err| TyError::ConflictingBorrow(Box::new(pl_expr.clone()), own, err))?;

        let mems =
            self.place_expr_ty_mems_under_exec_own(kind_ctx, &impl_ctx, exec, own, pl_expr)?;
        mems.iter()
            .try_for_each(|mem| Self::accessible_memory(exec, mem))?;

        let pl_expr_ty = pl_expr.ty.as_ref().unwrap();
        if !pl_expr_ty.is_fully_alive() {
            return Err(TyError::String(
                "The place was at least partially moved before.".to_string(),
            ));
        }
        let (reffed_ty, rmem) = match &pl_expr_ty.ty {
            TyKind::Data(DataTy {
                dty: DataTyKind::Dead(_),
                ..
            })
            | TyKind::Dead(_) => {
                panic!("Cannot happen because of the alive check.")
            }
            TyKind::Data(DataTy {
                dty: DataTyKind::ThreadHierchy(_),
                ..
            }) => {
                return Err(TyError::String(
                    "Trying to borrow thread hierarchy.".to_string(),
                ))
            }
            TyKind::Data(DataTy {
                dty: DataTyKind::At(inner_ty, m),
                ..
            }) => (inner_ty.deref().clone(), m.clone()),
            TyKind::Data(dty) => (
                dty.clone(),
                if !mems.is_empty() {
                    let m = mems.last().unwrap();
                    m.clone()
                } else {
                    return Err(TyError::String(
                        "Trying to borrow value that does not exist for the current \
            execution resource."
                            .to_string(),
                    ));
                },
            ),
            TyKind::Fn(_, _, _) => {
                return Err(TyError::String("Trying to borrow a function.".to_string()))
            }
            TyKind::Ident(_) => {
                return Err(TyError::String(
                    "Borrowing from value of unspecified type. This could be a view.\
            Therefore it is not allowed to borrow."
                        .to_string(),
                ))
            }
        };
        if rmem == Memory::GpuLocal {
            return Err(TyError::String(
                "Trying to take reference of unaddressable gpu.local memory.".to_string(),
            ));
        }
        let res_dty = DataTy::new(DataTyKind::Ref(
            Provenance::Value(prv_val_name.to_string()),
            own,
            rmem,
            Box::new(reffed_ty),
        ));
        let res_ty_ctx = impl_ctx.extend_loans_for_prv(&prv_val_name, loans)?;
        Ok((res_ty_ctx, Ty::new(TyKind::Data(res_dty))))
    }

    // Δ; Γ ⊢ω p:τ
    // p in an ω context has type τ under Δ and Γ
    fn place_expr_ty_under_exec_own(
        &self,
        kind_ctx: &KindCtx,
        ty_ctx: &TyCtx,
        exec: Exec,
        own: Ownership,
        pl_expr: &mut PlaceExpr,
    ) -> TyResult<()> {
        let _mem = self.place_expr_ty_mems_under_exec_own(kind_ctx, ty_ctx, exec, own, pl_expr)?;
        Ok(())
    }

    fn place_expr_ty_mems_under_exec_own(
        &self,
        kind_ctx: &KindCtx,
        ty_ctx: &TyCtx,
        exec: Exec,
        own: Ownership,
        pl_expr: &mut PlaceExpr,
    ) -> TyResult<Vec<Memory>> {
        let (mem, _) = self
            .place_expr_ty_mem_passed_prvs_under_exec_own(kind_ctx, ty_ctx, exec, own, pl_expr)?;
        Ok(mem)
    }

    // Δ; Γ ⊢ω p:τ,{ρ}
    // p in an ω context has type τ under Δ and Γ, passing through provenances in Vec<ρ>
    fn place_expr_ty_mem_passed_prvs_under_exec_own(
        &self,
        kind_ctx: &KindCtx,
        ty_ctx: &TyCtx,
        exec: Exec,
        own: Ownership,
        pl_expr: &mut PlaceExpr,
    ) -> TyResult<(Vec<Memory>, Vec<Provenance>)> {
        let (ty, mem, prvs) = match &mut pl_expr.pl_expr {
            // TC-Var
            PlaceExprKind::Ident(ident) => {
                self.var_expr_ty_mem_empty_prvs_under_exec_own(ty_ctx, exec, ident)?
            }
            // TC-Proj
            PlaceExprKind::Proj(tuple_expr, n) => self
                .proj_expr_ty_mem_passed_prvs_under_exec_own(
                    kind_ctx, ty_ctx, exec, own, tuple_expr, n,
                )?,
            // TC-Deref
            PlaceExprKind::Deref(borr_expr) => self.deref_expr_ty_mem_passed_prvs_under_exec_own(
                kind_ctx, ty_ctx, exec, own, borr_expr,
            )?,
        };
        pl_expr.ty = Some(ty);
        Ok((mem, prvs))
    }

    fn var_expr_ty_mem_empty_prvs_under_exec_own(
        &self,
        ty_ctx: &TyCtx,
        exec: Exec,
        ident: &Ident,
    ) -> TyResult<(Ty, Vec<Memory>, Vec<Provenance>)> {
        let ty = if let Ok(tty) = ty_ctx.ty_of_ident(ident) {
            tty
        } else {
            &self
                .gl_ctx
                .fun_ty_by_ident(ident, &FunctionKind::GlobalFun)?
                .mono_ty //TODO FunctionKind::GlobalFun right???
        };

        match &ty.ty {
            TyKind::Data(dty) => {
                if !dty.is_fully_alive() {
                    return Err(TyError::String(format!(
                        "The value in this identifier `{}` has been moved out.",
                        ident
                    )));
                }
                // FIXME Should throw an error if thread local memory is accessed by a block
                //  for example.
                let mem = Self::default_mem_by_exec(exec);
                Ok((
                    ty.clone(),
                    if mem.is_some() {
                        vec![mem.unwrap()]
                    } else {
                        vec![]
                    },
                    vec![],
                ))
            }
            TyKind::Fn(_, _, _) => {
                if !ty.is_fully_alive() {
                    panic!("This should never happen.")
                }
                Ok((ty.clone(), vec![], vec![]))
            }
            TyKind::Dead(_) => Err(TyError::DeadTy),
            // TODO this is probably wrong, should probably succeed instead
            //  but not in all cases. as long as these functions return the accessed memory region,
            //  the type MUST be known to do so.
            TyKind::Ident(ident) => {
                panic!("Identifier {} found. Expected instantiated type.", ident)
            }
        }
    }

    fn default_mem_by_exec(exec: Exec) -> Option<Memory> {
        match exec {
            Exec::CpuThread => Some(Memory::CpuMem),
            Exec::GpuThread => Some(Memory::GpuLocal),
            Exec::GpuGrid => Some(Memory::GpuLocal),
            Exec::GpuBlock => Some(Memory::GpuLocal),
            Exec::GpuWarp => Some(Memory::GpuLocal),
            Exec::View => None,
        }
    }

    fn proj_expr_ty_mem_passed_prvs_under_exec_own(
        &self,
        kind_ctx: &KindCtx,
        ty_ctx: &TyCtx,
        exec: Exec,
        own: Ownership,
        tuple_expr: &mut PlaceExpr,
        proj: &ProjEntry,
    ) -> TyResult<(Ty, Vec<Memory>, Vec<Provenance>)> {
        let (mem, passed_prvs) = self.place_expr_ty_mem_passed_prvs_under_exec_own(
            kind_ctx, ty_ctx, exec, own, tuple_expr,
        )?;
        match (&tuple_expr.ty.as_ref().unwrap().ty, proj) {
            (
                TyKind::Data(DataTy {
                    dty: DataTyKind::Tuple(elem_dtys),
                    ..
                }),
                ProjEntry::TupleAccess(n),
            ) => {
                if let Some(ty) = elem_dtys.get(*n) {
                    Ok((Ty::new(TyKind::Data(ty.clone())), mem, passed_prvs))
                } else {
                    Err(TyError::String(
                        "Trying to access non existing tuple element.".to_string(),
                    ))
                }
            }
            (
                TyKind::Data(DataTy {
                    dty: DataTyKind::Struct(struct_dt),
                    ..
                }),
                ProjEntry::StructAccess(attr_name),
            ) => {
                if let Some(ty) = struct_dt.get_ty(attr_name) {
                    Ok((Ty::new(TyKind::Data(ty.clone())), mem, passed_prvs))
                } else {
                    Err(TyError::String(
                        "Trying to access non existing struct attribute.".to_string(),
                    ))
                }
            }
            (TyKind::Ident(_), _) => Err(TyError::String(
                "Type unspecified. Cannot project from potentially non tuple/non struct type."
                    .to_string(),
            )),
            _ => Err(TyError::IllegalProjection(
                "Unexpected type or projection access.".to_string(),
            )),
        }
    }

    fn deref_expr_ty_mem_passed_prvs_under_exec_own(
        &self,
        kind_ctx: &KindCtx,
        ty_ctx: &TyCtx,
        exec: Exec,
        own: Ownership,
        borr_expr: &mut PlaceExpr,
    ) -> TyResult<(Ty, Vec<Memory>, Vec<Provenance>)> {
        let (mut inner_mem, mut passed_prvs) = self
            .place_expr_ty_mem_passed_prvs_under_exec_own(kind_ctx, ty_ctx, exec, own, borr_expr)?;
        if let TyKind::Data(DataTy {
            dty: DataTyKind::Ref(prv, ref_own, mem, dty),
            ..
        }) = &borr_expr.ty.as_ref().unwrap().ty
        {
            if ref_own < &own {
                return Err(TyError::String(
                    "Trying to dereference and mutably use a shrd reference.".to_string(),
                ));
            }
            let outl_rels = passed_prvs.iter().map(|passed_prv| (prv, passed_prv));
            subty::multiple_outlives(kind_ctx, ty_ctx.clone(), outl_rels)?;
            passed_prvs.push(prv.clone());
            inner_mem.push(mem.clone());
            Ok((
                Ty::new(TyKind::Data(dty.as_ref().clone())),
                inner_mem,
                passed_prvs,
            ))
        } else if let TyKind::Data(DataTy {
            dty: DataTyKind::RawPtr(dty),
            ..
        }) = &borr_expr.ty.as_ref().unwrap().ty
        {
            // TODO is anything of this correct?
            Ok((
                Ty::new(TyKind::Data(dty.as_ref().clone())),
                inner_mem,
                passed_prvs,
            ))
        } else {
            Err(TyError::String(
                "Trying to dereference non reference type.".to_string(),
            ))
        }
    }

    fn accessible_memory(exec: Exec, mem: &Memory) -> TyResult<()> {
        let gpu_exec_to_mem = vec![
            (Exec::CpuThread, Memory::CpuMem),
            (Exec::GpuThread, Memory::GpuGlobal),
            (Exec::GpuThread, Memory::GpuShared),
            (Exec::GpuThread, Memory::GpuLocal),
            (Exec::GpuGrid, Memory::GpuGlobal),
            (Exec::GpuGrid, Memory::GpuShared),
            (Exec::GpuGrid, Memory::GpuLocal),
            (Exec::GpuBlock, Memory::GpuGlobal),
            (Exec::GpuBlock, Memory::GpuShared),
            (Exec::GpuBlock, Memory::GpuLocal),
            (Exec::GpuWarp, Memory::GpuGlobal),
            (Exec::GpuWarp, Memory::GpuShared),
            (Exec::GpuWarp, Memory::GpuLocal),
        ];

        if gpu_exec_to_mem.contains(&(exec, mem.clone())) {
            Ok(())
        } else {
            Err(TyError::String(format!(
                "Trying to dereference pointer to `{}` from execution resource `{}`",
                mem, exec
            )))
        }
    }

    fn tyscheme_well_formed(
        &self,
        kind_ctx: &KindCtx,
        ty_ctx: &TyCtx,
        exec: Exec,
        ty: &TypeScheme,
    ) -> TyResult<()> {
        let kind_ctx = kind_ctx.clone().append_idents(ty.generic_params.clone());
        if ty.constraints.len() > 0 {
            self.well_formed_constraint_scheme(
                &kind_ctx,
                ty_ctx,
                &ConstraintScheme {
                    generics: vec![],
                    implican: ty.constraints.clone().drain(1..).collect(),
                    implied: ty.constraints.first().unwrap().clone(),
                },
            )?;
        }
        self.ty_well_formed(&kind_ctx, ty_ctx, exec, &ty.mono_ty)
    }

    // TODO respect memory
    fn ty_well_formed(
        &self,
        kind_ctx: &KindCtx,
        ty_ctx: &TyCtx,
        exec: Exec,
        ty: &Ty,
    ) -> TyResult<()> {
        match &ty.ty {
            TyKind::Data(dty) => match &dty.dty {
                // TODO variables of Dead types can be reassigned. So why do we not have to check
                //  well-formedness of the type in Dead(ty)? (According paper).
                DataTyKind::Scalar(_)
                | DataTyKind::Atomic(_)
                | DataTyKind::Range
                | DataTyKind::RawPtr(_)
                | DataTyKind::Dead(_) => {}
                DataTyKind::Ident(ident) => {
                    if !kind_ctx.ident_of_kind_exists(ident, Kind::DataTy) {
                        Err(CtxError::KindedIdentNotFound(ident.clone()))?
                    }
                }
                DataTyKind::Struct(struct_mono_ty) => {
                    let StructDataType {
                        name,
                        attributes,
                        generic_args,
                    } = struct_mono_ty;
                    let struct_def = self.gl_ctx.struct_by_name(name)?;
                    Self::check_args_have_correct_kinds(&struct_def.generic_params, generic_args)?;
                    iter_TyResult_to_TyResult!(attributes.iter().map(|field| self
                        .ty_well_formed(
                            kind_ctx,
                            ty_ctx,
                            exec,
                            &Ty::new(TyKind::Data(field.ty.clone()))
                        )))?;
                }
                DataTyKind::Ref(Provenance::Value(prv), own, mem, dty) => {
                    let elem_ty = Ty::new(TyKind::Data(dty.as_ref().clone()));
                    if !elem_ty.is_fully_alive() {
                        return Err(TyError::ReferenceToDeadTy);
                    }
                    let loans = ty_ctx.loans_in_prv(prv)?;
                    if !loans.is_empty() {
                        let mut exists = false;
                        for loan in loans {
                            let Loan {
                                place_expr,
                                own: l_own,
                            } = loan;
                            if l_own != own {
                                return Err(TyError::ReferenceToWrongOwnership);
                            }
                            let mut borrowed_pl_expr = place_expr.clone();
                            self.place_expr_ty_under_exec_own(
                                kind_ctx,
                                ty_ctx,
                                exec,
                                *l_own,
                                &mut borrowed_pl_expr,
                            )?;
                            if let TyKind::Data(pl_expr_dty) = borrowed_pl_expr.ty.unwrap().ty {
                                if !pl_expr_dty.is_fully_alive() {
                                    return Err(TyError::ReferenceToDeadTy);
                                }
                                if dty.occurs_in(&pl_expr_dty) {
                                    exists = true;
                                    break;
                                }
                            }
                        }
                        if !exists {
                            if let DataTyKind::ArrayShape(_, _) = &dty.dty {
                                eprintln!("WARNING: Did not check well-formedness of view type reference.")
                            } else {
                                return Err(TyError::ReferenceToIncompatibleType);
                            }
                        }
                    }
                    self.ty_well_formed(kind_ctx, ty_ctx, exec, &elem_ty)?;
                }
                DataTyKind::Ref(Provenance::Ident(ident), _, mem, dty) => {
                    let elem_ty = Ty::new(TyKind::Data(dty.as_ref().clone()));
                    if !kind_ctx.ident_of_kind_exists(ident, Kind::Provenance) {
                        Err(CtxError::KindedIdentNotFound(ident.clone()))?
                    }
                    self.ty_well_formed(kind_ctx, ty_ctx, exec, &elem_ty)?;
                }
                //FIXME check well-formedness of nats
                DataTyKind::ThreadHierchy(th_hy) => {}
                DataTyKind::SplitThreadHierchy(th_hy, n) => {}
                DataTyKind::Tuple(elem_dtys) => {
                    for elem_dty in elem_dtys {
                        self.ty_well_formed(
                            kind_ctx,
                            ty_ctx,
                            exec,
                            &Ty::new(TyKind::Data(elem_dty.clone())),
                        )?;
                    }
                }
                DataTyKind::Array(elem_dty, n) => {
                    self.ty_well_formed(
                        kind_ctx,
                        ty_ctx,
                        exec,
                        &Ty::new(TyKind::Data(elem_dty.as_ref().clone())),
                    )?;
                    // TODO well-formed nat
                }
                DataTyKind::ArrayShape(elem_dty, n) => {
                    self.ty_well_formed(
                        kind_ctx,
                        ty_ctx,
                        exec,
                        &Ty::new(TyKind::Data(elem_dty.as_ref().clone())),
                    )?
                    // TODO well-formed nat
                }
                DataTyKind::At(elem_dty, Memory::Ident(ident)) => {
                    if !kind_ctx.ident_of_kind_exists(ident, Kind::Memory) {
                        Err(TyError::CtxError(CtxError::KindedIdentNotFound(
                            ident.clone(),
                        )))?;
                    }
                    self.ty_well_formed(
                        kind_ctx,
                        ty_ctx,
                        exec,
                        &Ty::new(TyKind::Data(elem_dty.as_ref().clone())),
                    )?;
                }
                DataTyKind::At(elem_dty, _) => {
                    self.ty_well_formed(
                        kind_ctx,
                        ty_ctx,
                        exec,
                        &Ty::new(TyKind::Data(elem_dty.as_ref().clone())),
                    )?;
                }
            },
            TyKind::Ident(ident) => {
                if !kind_ctx.ident_of_kind_exists(ident, Kind::Ty) {
                    Err(CtxError::KindedIdentNotFound(ident.clone()))?
                }
            }
            // TODO check well-formedness of Nats
            TyKind::Fn(param_tys, exec, ret_ty) => {
                self.ty_well_formed(&kind_ctx, ty_ctx, *exec, ret_ty)?;
                let mut visitor = FreeKindedIdents::new();
                for param_ty in param_tys {
                    //Add free implicit Lifetime-parameter-idents to kind_ctx
                    visitor.set.clear();
                    visitor.bound_idents.clear();
                    visitor.visit_ty(param_ty);
                    let kind_ctx = kind_ctx.clone().append_idents(
                        visitor
                            .set
                            .iter()
                            .filter(|ident| {
                                ident.kind == Kind::Provenance && ident.ident.is_implicit
                            })
                            .map(|ident| ident.clone())
                            .collect(),
                    );

                    self.ty_well_formed(&kind_ctx, ty_ctx, *exec, param_ty)?;
                }
            }
            TyKind::Dead(_) => {}
        }
        Ok(())
    }

    fn well_formed_constraint_scheme(
        &self,
        kind_ctx: &KindCtx,
        ty_ctx: &TyCtx,
        cscheme: &ConstraintScheme,
    ) -> TyResult<()> {
        if cscheme.is_constraint() {
            self.ty_well_formed_constraint(&cscheme.implied)?;
            self.ty_well_formed(
                kind_ctx,
                ty_ctx,
                Exec::View,
                &Ty::new(TyKind::Data(cscheme.implied.param.clone())),
            )?; //TODO exec = View???
            iter_TyResult_to_TyResult!(cscheme.implied.trait_bound.generics.iter().map(|arg| {
                match arg {
                    ArgKinded::Ty(_) => panic!("types as generic params are not supported"),
                    ArgKinded::DataTy(dty) => self.ty_well_formed(
                        kind_ctx,
                        ty_ctx,
                        Exec::View,
                        &Ty::new(TyKind::Data(dty.clone())),
                    ), //TODO exec = View???
                    _ => unimplemented!("TODO"),
                }
            }))
        } else {
            let kind_ctx = kind_ctx.clone().append_idents(cscheme.generics.clone());

            iter_TyResult_to_TyResult!(cscheme.implican.iter().map(|implied| self
                .well_formed_constraint_scheme(
                    &kind_ctx,
                    ty_ctx,
                    &ConstraintScheme::new(implied)
                )))?;

            self.well_formed_constraint_scheme(
                &kind_ctx,
                ty_ctx,
                &ConstraintScheme::new(&cscheme.implied),
            )
        }
    }

    fn ty_well_formed_constraint(&self, constraint: &Constraint) -> TyResult<()> {
        let TraitMonoType { name, generics } = &constraint.trait_bound;
        let trait_def = self.gl_ctx.trait_ty_by_name(name)?;
        Self::check_args_have_correct_kinds(&trait_def.generic_params, generics)
    }
}

pub fn proj_elem_ty(ty: &Ty, proj: &ProjEntry) -> TyResult<Ty> {
    match (&ty.ty, proj) {
        (
            TyKind::Data(DataTy {
                dty: DataTyKind::Tuple(dtys),
                ..
            }),
            ProjEntry::TupleAccess(i),
        ) => match dtys.get(*i) {
            Some(dty) => Ok(Ty::new(TyKind::Data(dty.clone()))),
            None => Err(TyError::IllegalProjection(format!(
                "Cannot project element `{}` from tuple with {} elements.",
                i,
                dtys.len()
            ))),
        },
        (
            TyKind::Data(DataTy {
                dty: DataTyKind::Struct(struct_ty),
                ..
            }),
            ProjEntry::StructAccess(attr_name),
        ) => match struct_ty.get_ty(attr_name) {
            Some(ty) => Ok(Ty::new(TyKind::Data(ty.clone()))),
            None => Err(TyError::IllegalProjection(format!(
                "Cannot project element `{}` from struct {}.",
                attr_name, struct_ty.name
            ))),
        },
        _ => Err(TyError::IllegalProjection(
            "Unexpected type or projection access.".to_string(),
        )),
    }
}
