mod borrow_check;
mod constraint_check;
mod ctxs;
mod error;
mod infer_kinded_args;
pub mod pre_decl;
mod subty;
pub(crate) mod unify;

use crate::ast::internal::{FrameEntry, IdentTyped, Loan, Place, PrvMapping};
use crate::ast::utils::{fresh_name, FreeKindedIdents};
use crate::ast::visit::{walk_dty, Visit};
use crate::ast::visit_mut::VisitMut;
use crate::ast::DataTyKind::Scalar;
use crate::ast::ThreadHierchyTy;
use crate::ast::*;
use crate::error::ErrorReported;
use crate::ty_check::pre_decl::copy_Trait;
use crate::ty_check::unify::{ConstrainMap, Constrainable};
use crate::SourceCode;
use core::panic;
use ctxs::{GlobalCtx, KindCtx, TyCtx};
use error::*;
use std::collections::HashSet;
use std::ops::Deref;
use std::sync::Once;

use self::constraint_check::{ConstraintEnv, ConstraintScheme, IdentConstraints};
use self::pre_decl::bin_op_to_fun;

type TyResult<T> = Result<T, TyError>;

macro_rules! iter_TyResult_to_TyResult {
    ($err_iter: expr) => {{
        let mut err_vec: Vec<TyError> = $err_iter
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
        } else if err_vec.len() == 1 {
            Err(err_vec.remove(0))
        } else {
            Err(TyError::MultiError(err_vec))
        }
    }};
}

fn get_stdlib_compil_unit() -> CompilUnit<'static> {
    static STD_LIB_PATH: &'static str = "src/stdlib.desc";
    static mut STD_LIB_SRC: Option<SourceCode> = None;
    static mut STD_LIB_COMPIL: Option<CompilUnit> = None;
    static ONCE: Once = Once::new();

    unsafe {
        ONCE.call_once(|| {
            STD_LIB_SRC = Some(match SourceCode::from_file(STD_LIB_PATH) {
                Ok(s) => s,
                Err(err) => panic!("Reading stdlib failed\n{:#?}", err),
            });
            STD_LIB_COMPIL = Some(match crate::parser::parse(STD_LIB_SRC.as_ref().unwrap()) {
                Ok(c) => c,
                Err(err) => panic!("Parsing stdlib failed!\n{:#?}", err),
            });
        });

        STD_LIB_COMPIL.clone().unwrap()
    }
}

// ∀ε ∈ Σ. Σ ⊢ ε
// --------------
//      ⊢ Σ
pub fn ty_check(compil_unit: &mut CompilUnit) -> Result<(), ErrorReported> {
    let mut ty_checker = TyChecker::new();

    let mut std_compil_unit = get_stdlib_compil_unit();
    ty_checker.ty_check(&mut std_compil_unit).map_err(|err| {
        err.emit(&std_compil_unit.source);
        ErrorReported
    })?;

    ty_checker.ty_check(compil_unit).map_err(|err| {
        err.emit(compil_unit.source);
        ErrorReported
    })?;

    compil_unit.item_defs.extend(std_compil_unit.item_defs);

    Ok(())
}

struct TyChecker {
    //Global context with types of global functions, types of impl functions, structs
    //and trait definitions
    gl_ctx: GlobalCtx,
    //Environment with constraint_schemes
    constraint_env: ConstraintEnv,
    //A List of constraints of implicit identifiers which are checked when a
    //implicit identifier is substituted by a concrete type
    implicit_ident_cons: IdentConstraints,
    //A Map with substitutions for implicit identifiers which should be applied to the types of
    //all expressions inside a function
    //e.g. we infer for "let x = Vec::new()" the type Vec<$T> where $T is an implicit ident
    //Somewhere later in the code we may infer $T is f32. Then we must adjust the typecontext
    //but also the type of the expressions whose types contain $T
    implicit_ident_substitution: ConstrainMap,
}

impl TyChecker {
    pub fn new() -> Self {
        TyChecker {
            gl_ctx: GlobalCtx::new().append_fun_decls(&pre_decl::fun_decls()),
            constraint_env: ConstraintEnv::new(),
            implicit_ident_cons: IdentConstraints::new(),
            implicit_ident_substitution: ConstrainMap::new(),
        }
    }

    //Apply a substitution to multiple expressions and its subexpressions
    //and make sure all expressions does not contain implicit type identifiers after substitution
    fn apply_substitution_exprs<'a, 'b, I>(
        exprs: I,
        implicit_ident_substitution: &'b ConstrainMap,
    ) -> TyResult<()>
    where
        I: Iterator<Item = &'a mut Expr>,
    {
        struct ExprVisitor<'a> {
            implicit_ident_substitution: &'a ConstrainMap,
            error: Option<TyError>,
        }

        impl<'a> ExprVisitor<'a> {
            fn substitute<T, E>(&mut self, t: &mut T, err: E)
            where
                T: Constrainable,
                E: Fn(&mut T) -> TyError,
            {
                //Apply substitution
                t.substitute(self.implicit_ident_substitution);

                //Make sure the type does not contain any implicit type identifier anymore
                if self.error.is_none() {
                    if t.free_idents().iter().fold(false, |res, i_kinded| {
                        res || (i_kinded.ident.is_implicit && i_kinded.kind != Kind::Provenance)
                    }) {
                        self.error = Some(err(t))
                    }
                }
            }
        }

        impl<'a> VisitMut for ExprVisitor<'a> {
            fn visit_expr(&mut self, expr: &mut Expr) {
                match &mut expr.expr {
                    ExprKind::Lambda(params, _, ret_dty, body) => {
                        self.visit_expr(body);

                        params.iter_mut().for_each(|param_decl| {
                            self.substitute(param_decl.ty.as_mut().unwrap(), |t| {
                                TyError::TypeAnnotationsNeeded(format!(
                                    "in paramdecl of lambda_fun {:#?}",
                                    t
                                ))
                            })
                        });
                        self.substitute(ret_dty.as_mut(), |t| {
                            TyError::TypeAnnotationsNeeded(format!(
                                "in ret_ty of lambda_fun {:#?}",
                                t
                            ))
                        });
                    }
                    _ => {
                        visit_mut::walk_expr(self, expr);

                        self.substitute(
                            expr.ty
                                .as_mut()
                                .expect(&format!("Expr {:#?} has no type!", expr.expr)),
                            |t| TyError::TypeAnnotationsNeeded(format!("{:#?}", t)),
                        );
                    }
                }
            }

            fn visit_pl_expr(&mut self, pl_expr: &mut PlaceExpr) {
                visit_mut::walk_pl_expr(self, pl_expr);

                if pl_expr.ty.is_some() {
                    self.substitute(
                        pl_expr
                            .ty
                            .as_mut()
                            .expect(&format!("PlaceExpr {:#?} has no type!", pl_expr.pl_expr)),
                        |t| TyError::TypeAnnotationsNeeded(format!("{:#?}", t)),
                    );
                }
            }

            fn visit_arg_kinded(&mut self, arg_kinded: &mut ArgKinded) {
                self.substitute(arg_kinded, |t| {
                    TyError::TypeAnnotationsNeeded(format!("{:#?}", t))
                });
            }
        }

        let mut visitor = ExprVisitor {
            implicit_ident_substitution,
            error: None,
        };

        //Visit expr and subexpressions
        exprs.for_each(|expr| visitor.visit_expr(expr));

        if let Some(err) = visitor.error {
            Err(err)
        } else {
            Ok(())
        }
    }

    fn ty_check(&mut self, compil_unit: &mut CompilUnit) -> TyResult<()> {
        let errs: Vec<TyError> = self
            .gl_ctx
            .append_from_item_def(&compil_unit.item_defs, &mut self.constraint_env)
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
            Item::StructDecl(struct_decl) => self.ty_check_struct_decl(struct_decl),
            Item::TraitDef(trait_def) => self.ty_check_trait_def(trait_def),
            Item::ImplDef(impl_def) => self.ty_check_impl_def(impl_def),
        }
    }

    fn ty_check_struct_decl(&mut self, struct_decl: &mut StructDecl) -> TyResult<()> {
        //Append all generic params of the struct to the kinding context
        let kind_ctx = KindCtx::new().append_idents(struct_decl.generic_params.clone());
        let ty_ctx = TyCtx::new();

        //Check well formedness of datatypes of struct_fields
        iter_TyResult_to_TyResult!(struct_decl.decls.iter().map(|struct_field| {
            self.dty_well_formed(&kind_ctx, &ty_ctx, None, &struct_field.ty)
        }))?;
        //Check well formedness of all conatraints
        iter_TyResult_to_TyResult!(struct_decl
            .constraints
            .iter()
            .map(|constraint| self.constraint_well_formed(&kind_ctx, &ty_ctx, None, constraint)))
    }

    fn ty_check_trait_def(&mut self, trait_def: &mut TraitDef) -> TyResult<()> {
        //An empty kinding context (used to check well formedness
        //of typeschemes offunction declarations)
        let kind_ctx_empty = KindCtx::new();
        //Kinding context with "Self"-datatype and all generic params of the trait
        let kind_ctx_trait = KindCtx::new()
            .append_idents(vec![IdentKinded::new(&Ident::new("Self"), Kind::DataTy)])
            .append_idents(trait_def.generic_params.clone());
        let ty_ctx = TyCtx::new();

        //Check if all constrains are well_formed
        iter_TyResult_to_TyResult!(trait_def.constraints.iter().map(|contraint| {
            self.constraint_well_formed(&kind_ctx_trait, &ty_ctx, None, &contraint)
        }))?;

        //Assume all constraints of the trait (necessary to type_check function definitions)
        self.constraint_env
            .append_constraints(&trait_def.constraints);

        let result =
            iter_TyResult_to_TyResult!(trait_def.decls.iter_mut().map(|ass_item| match ass_item {
                //Check if typeschemes of function declarations are well_formed
                AssociatedItem::FunDecl(fun_decl) => {
                    let fun_ty = self.gl_ctx.fun_ty_by_name(FunctionName {
                        name: fun_decl.name.clone(),
                        fun_kind: FunctionKind::TraitFun(trait_def.name.clone()),
                    });
                    self.tyscheme_well_formed(&kind_ctx_empty, &ty_ctx, Some(fun_decl.exec), fun_ty)
                }
                //For function definitions: ty_check the whole fun_def
                AssociatedItem::FunDef(fun_def) => {
                    self.ty_check_fun_def(kind_ctx_trait.clone(), fun_def)
                }
                AssociatedItem::ConstItem(_, _, _) => unimplemented!("TODO"),
            }));

        //Remove all added constraints of the trait from global_context
        self.constraint_env
            .remove_constraints(&trait_def.constraints);

        result
    }

    fn ty_check_impl_def(&mut self, impl_def: &mut ImplDef) -> TyResult<()> {
        let kind_ctx = KindCtx::new();
        let ty_ctx = TyCtx::new();

        //If this impl implements a trait
        if impl_def.trait_impl.is_some() {
            //This is the trait (inclusive the generic_args) which is implemented by this impl
            let trait_impl = impl_def.trait_impl.clone().unwrap();
            //Find the trait definition in global context
            let trait_def = self.gl_ctx.trait_ty_by_name(&trait_impl.name)?.clone();

            //Check if the generic args in "trait_impl" have the expected kinds
            Self::check_args_have_correct_kinds(&trait_def.generic_params, &trait_impl.generics)?;

            //All generic parameter of the trait inclusive "Self"
            let mut generics_trait = Vec::with_capacity(trait_def.generic_params.len() + 1);
            generics_trait.push(IdentKinded::new(&Ident::new("Self"), Kind::DataTy));
            generics_trait.extend(trait_def.generic_params.clone());

            let mut generic_args_trait = Vec::with_capacity(trait_def.generic_params.len() + 1);
            //Add the datatype for which the trait is implemented
            //(this is the generic arg for "Self" in the trait)
            generic_args_trait.push(ArgKinded::DataTy(impl_def.dty.clone()));
            //These are the other generic args for the trait
            generic_args_trait.extend(trait_impl.generics.clone());

            assert!(generic_args_trait.len() == generics_trait.len());

            //Check every generic is a free type var in "generic_args_trait"
            //This is necessary to make sure that if all generic_args_trait are known
            //all generic_args for this impl can be inferred
            //This is on the other hand necessary to replace trait-function-calls with
            //suitable impl-function calls (monomorphiser)
            let free_idents = generic_args_trait
                .iter()
                .fold(HashSet::new(), |mut free, monoty| {
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
                    found: generics_trait.len(),
                });
            }

            //Check if all constraints, the datatype for which the trait is implemented
            //and the trait_mono_type which is implemented by this impl are well formed
            //(This also checks well-formedness "impl_def.dty" and "trait_impl")
            self.constraint_scheme_well_formed(
                &kind_ctx,
                &ty_ctx,
                None,
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
                    generics: generics_trait.clone(),
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
            //our impl really fullfills this supertrait constraints
            self.constraint_env
                .remove_constraint_schemes(&supertraits_constraints);
            //While typechecking the constraints specified in the where-clause of the impl can be assumed
            self.constraint_env
                .append_constraints(&impl_def.constraints);

            //Append generics from the impl to the kinding context
            let kind_ctx = kind_ctx.append_idents(impl_def.generic_params.clone());

            //Collect all errors in this vector
            let mut errors = Vec::new();

            //Check every supertrait constraint
            trait_def
                .supertraits_constraints()
                .iter()
                //and every constraint specified in the where-clause of the trait
                .chain(trait_def.constraints.iter())
                .for_each(|constraint| {
                    let constraint_sub = generics_trait.iter().zip(generic_args_trait.iter()).fold(
                        constraint.clone(),
                        |cons, (generic, generic_arg)| {
                            cons.subst_ident_kinded(generic, generic_arg)
                        },
                    );

                    if self
                        .constraint_env
                        .check_constraint(&constraint_sub, &mut self.implicit_ident_cons)
                        .is_err()
                    {
                        errors.push(TyError::UnfullfilledConstraint(constraint.clone()))
                    }
                });
            assert!(self.implicit_ident_cons.is_empty());

            //Check if all fun_decls from the trait are implemented here
            //This typescheme is only for error-messages
            let impl_def_ty = impl_def.ty();
            //List with all remaining, not-checked associated items from the impl
            let mut ass_items_to_check: Vec<&mut AssociatedItem> =
                impl_def.decls.iter_mut().collect();
            //For every associated item in the trait
            trait_def.decls.iter().for_each(|ass_item| {
                match ass_item {
                    //if associated item is a function definition or function declaration
                    AssociatedItem::FunDef(_) | AssociatedItem::FunDecl(_) => {
                        //Get the function name of the function
                        let fun_name = match ass_item {
                            AssociatedItem::FunDef(fun_def) => fun_def.name.clone(),
                            AssociatedItem::FunDecl(fun_decl) => fun_decl.name.clone(),
                            AssociatedItem::ConstItem(_, _, _) => panic!("This cannot happen"),
                        };

                        //if there is an function definition with same name in this impl
                        if let Some(index) =
                            ass_items_to_check.iter().position(
                                |impl_ass_item| match impl_ass_item {
                                    AssociatedItem::FunDef(fun) => fun.name == fun_name,
                                    _ => false,
                                },
                            )
                        {
                            //Remove the impl-function of the list of remaining, not-checked associated items
                            let fun_impl = match ass_items_to_check.swap_remove(index) {
                                AssociatedItem::FunDef(fun_def) => fun_def,
                                _ => panic!("This can not happen"),
                            };
                            //Get the typescheme of the trait-function from context
                            let fun_decl_ty = self
                                .gl_ctx
                                .fun_ty_by_name(FunctionName::from_trait(&fun_name, &trait_def));

                            //This is the expected type scheme
                            let expected_impl_fun_ty = TypeScheme {
                                generic_params: fun_decl_ty.generic_params.clone(),
                                //The first constraint is the "Self impl the trait"-constraint
                                //which should not part of the impl-type-scheme
                                constraints: fun_decl_ty.constraints[1..].to_vec(),
                                mono_ty: fun_decl_ty.mono_ty.clone(),
                            }
                            //Instantiate the generic_params of the trait-definition with "generic_args_trait"
                            .partial_apply(generic_args_trait.as_slice());
                            //This is the found type-scheme of the impl-function
                            let fun_impl_ty = fun_impl.ty();

                            //The both typeschemes are equal
                            if expected_impl_fun_ty.eq_structure(&fun_impl_ty) {
                                //Typecheck the function definition
                                if let Err(err) = self.ty_check_fun_def(kind_ctx.clone(), fun_impl)
                                {
                                    errors.push(err);
                                }
                            }
                            //if they are not equal, its an error
                            else {
                                errors.push(TyError::UnexpectedType {
                                    expected: expected_impl_fun_ty.mono_ty,
                                    found: fun_impl_ty.mono_ty,
                                })
                            }
                        }
                        //if there is not an function definition with same name in this impl
                        else {
                            match ass_item {
                                //If the trait has a default implementation, its fine
                                AssociatedItem::FunDef(_) => (),
                                //If not, this is an error because this impl must
                                //implemented this function
                                AssociatedItem::FunDecl(_) => {
                                    errors.push(TyError::from(CtxError::FunNotImplemented {
                                        function_name: fun_name.clone(),
                                        trait_name: trait_def.name.clone(),
                                        impl_dty: impl_def_ty.clone(),
                                    }))
                                }
                                _ => panic!("This cannot happen"),
                            }
                        }
                    }
                    AssociatedItem::ConstItem(_, _, _) => unimplemented!("TODO"),
                }
            });

            //Any additional associated items in the impl (which are not part of the trait)
            //are not allowed
            ass_items_to_check
                .iter()
                .for_each(|item| errors.push(TyError::UnexpectedAssItemInImpl((**item).clone())));

            //Remove constraints added to the global context
            self.constraint_env
                .remove_constraints(&impl_def.constraints);
            self.constraint_env
                .append_constraint_schemes(&supertraits_constraints);

            //Return Ok or collected errors
            if errors.is_empty() {
                Ok(())
            } else {
                if errors.len() == 1 {
                    Err(errors.remove(0))
                } else {
                    Err(TyError::MultiError(errors))
                }
            }
        }
        //This impl does not implement a trait
        else {
            //Append all generic params to the kinding context
            let kind_ctx = kind_ctx.append_idents(impl_def.generic_params.clone());

            //Check if all constrains are well_formed
            iter_TyResult_to_TyResult!(impl_def.constraints.iter().map(|contraint| {
                self.constraint_well_formed(&kind_ctx, &ty_ctx, None, &contraint)
            }))?;

            //Assume all constraints of the impl (necessary to type_check function definitions)
            self.constraint_env
                .append_constraints(&impl_def.constraints);

            let result =
                iter_TyResult_to_TyResult!(impl_def.decls.iter_mut().map(|decl| match decl {
                    //Function declarations in an impl are not allowed
                    AssociatedItem::FunDecl(fun_decl) => Err(TyError::UnexpectedAssItemInImpl(
                        AssociatedItem::FunDecl(fun_decl.clone())
                    )),
                    //Ty_check every function definition
                    AssociatedItem::FunDef(fun_def) =>
                        self.ty_check_fun_def(kind_ctx.clone(), fun_def),
                    AssociatedItem::ConstItem(_, _, _) => unimplemented!("TODO"),
                }));

            //Remove all added constraints of the impl from global_context
            self.constraint_env
                .remove_constraints(&impl_def.constraints);

            result
        }
    }

    // Σ ⊢ fn f <List[φ], List[ρ], List[α]> (x1: τ1, ..., xn: τn) → τr where List[ρ1:ρ2] { e }
    fn ty_check_fun_def(&mut self, kind_ctx: KindCtx, gf: &mut FunDef) -> TyResult<()> {
        let kind_ctx = kind_ctx.append_idents(gf.generic_params.clone());
        kind_ctx.well_kinded_prv_rels(&gf.prv_rels)?;
        let kind_ctx = kind_ctx.append_prv_rels(gf.prv_rels.clone());

        // If a reference with lifetime 'a references an other reference with lifetime 'b then a' < b'
        // This also applies for structs that contains references
        // Add corresponding provenance relations to kinding context
        struct PrvVistor {
            //Provenance of the reference whose data type is currently being visited
            current_prov: Option<Provenance>,
            //Result with all new provenance relations
            result_relations: Vec<PrvRel>,
        }
        impl Visit for PrvVistor {
            fn visit_dty(&mut self, dty: &DataTy) {
                match &dty.dty {
                    DataTyKind::Ref(prov, _, _, dty) => {
                        //if this reference is inside some other reference
                        if let Some(current_prov) = &self.current_prov {
                            match (current_prov, prov) {
                                //Add corresponding relation
                                (Provenance::Ident(p1), Provenance::Ident(p2)) => {
                                    self.result_relations.push(PrvRel {
                                        longer: p2.clone(),
                                        shorter: p1.clone(),
                                    })
                                }
                                _ => panic!(
                                    "There are non-ident-provenances in the types of
                                    the parameters of a function. How is that possible?"
                                ),
                            }
                        }
                        let tmp = self.current_prov.clone();

                        //Visit all datatypes inside this reference
                        self.current_prov = Some(prov.clone());
                        self.visit_dty(dty);

                        self.current_prov = tmp;
                    }
                    DataTyKind::Struct(structdty) => {
                        if let Some(current_prov) = &self.current_prov {
                            structdty.generic_args.iter().for_each(|arg| {
                                if let ArgKinded::Provenance(prov) = arg {
                                    match (current_prov, prov) {
                                        (Provenance::Ident(p1), Provenance::Ident(p2)) => {
                                            self.result_relations.push(PrvRel {
                                                longer: p2.clone(),
                                                shorter: p1.clone(),
                                            })
                                        }
                                        _ => panic!(
                                            "There are non-ident-provenances in the types of
                                            the parameters of a function. How is that possible?"
                                        ),
                                    }
                                }
                            });
                        }
                    }
                    _ => walk_dty(self, dty),
                }
            }
        }
        //Visit all types of params of this function and append provenance relations
        //calculated by "PrvVistor" to kinding context
        let kind_ctx = kind_ctx.append_prv_rels(
            gf.param_decls
                .iter()
                .fold(
                    PrvVistor {
                        current_prov: None,
                        result_relations: Vec::new(),
                    },
                    |mut res, param| {
                        res.visit_ty(param.ty.as_ref().unwrap());
                        res
                    },
                )
                .result_relations,
        );

        //Assume the constraints of the function
        self.constraint_env.append_constraints(&gf.constraints);

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

            //Check well formedness of the typescheme of this function
            self.tyscheme_well_formed(&kind_ctx, &ty_ctx, Some(gf.exec), &gf.ty())?;

            //Check body-expression
            self.ty_check_expr(&kind_ctx, ty_ctx, gf.exec, &mut gf.body_expr)?;
            if !self.implicit_ident_substitution.is_empty() {
                TyChecker::apply_substitution_exprs(
                    std::iter::once(&mut gf.body_expr),
                    &self.implicit_ident_substitution,
                )?;
                self.implicit_ident_substitution.clear();
            }

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

        //Remove added constraints from the global context
        self.constraint_env.remove_constraints(&gf.constraints);

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

        //Replace binary operation by function calls
        if let ExprKind::BinOp(bin_op, lhs, rhs) = &expr.expr {
            //TODO at the moment only implmented for GpuThread and "+" and "=="
            if exec == Exec::GpuThread && (*bin_op == BinOp::Add || *bin_op == BinOp::Eq) {
                let fun_app = bin_op_to_fun(bin_op, lhs.as_ref().clone(), rhs.as_ref().clone());
                expr.expr = fun_app;
            }
        }

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
                self.ty_check_lambda(kind_ctx, ty_ctx, *exec, params, ret_ty, body, &expr.ty)?
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
        mut ty_ctx: TyCtx,
        exec: Exec,
        struct_name: &String,
        generic_args: &mut Vec<ArgKinded>,
        inst_exprs: &mut Vec<(Ident, Expr)>,
    ) -> TyResult<(TyCtx, Ty)> {
        // get struct definition from context (cloning prevents borrowing errors)
        let struct_decl = self.gl_ctx.struct_by_name(struct_name)?.clone();

        //Apply kinded args
        let mut struct_ty = self.dep_app(
            kind_ctx,
            &mut ty_ctx,
            exec,
            &struct_decl.ty().fresh_generic_param_names(),
            generic_args,
            0,
        )?;
        let struct_dty = if let TyKind::Data(struct_dty) = &mut struct_ty.ty {
            struct_dty
        } else {
            panic!("Struct has a non-datatype type")
        };

        //Sort all inst_exprs to have the same order like in struct_decl
        //And check if all struct_fields are initialized
        let mut errs = Vec::new();
        let inst_exprs_sorted = struct_decl
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
                        struct_name: struct_decl.name.clone(),
                    });
                    None
                }
            })
            .collect();
        //Any remaing elements in inst_exprs are fields that do not appear in the struct declaration
        inst_exprs.iter().for_each(|(name, _)| {
            errs.push(TyError::UnexpectedStructField {
                unexpected_field: name.name.clone(),
                struct_name: struct_decl.name.clone(),
            })
        });
        if !errs.is_empty() {
            if errs.len() == 1 {
                Err(errs.remove(0))?;
            } else {
                Err(TyError::MultiError(errs))?;
            }
        }
        *inst_exprs = inst_exprs_sorted;

        //Tycheck expressions
        for i in 0..inst_exprs.len() {
            let ith_expr = &mut inst_exprs[i].1;
            let ith_field = if let DataTyKind::Struct(struct_dty) = &mut struct_dty.dty {
                &struct_dty.attributes[i]
            } else {
                panic!("Struct has a non-struct-datatype")
            };

            //Tycheck passed expr
            ty_ctx = self.ty_check_expr(kind_ctx, ty_ctx, exec, ith_expr)?;

            //Make sure the expr has a datatype as type
            let ith_expr_dty = if let TyKind::Data(dty) = &mut ith_expr.ty.as_mut().unwrap().ty {
                dty
            } else {
                Err(TyError::UnexpectedTypeKind {
                    expected_name: String::from("TyKind::Data"),
                    found: ith_expr.ty.as_mut().unwrap().clone(),
                })?
            };

            //Make sure the type of the expr has the expected type
            let (mut constr_map, _) = unify::constrain(&ith_field.ty, &ith_expr_dty)?;

            if !constr_map.is_empty() {
                unify::substitute_multiple(
                    &self.constraint_env,
                    &mut self.implicit_ident_cons,
                    &mut constr_map,
                    std::iter::once(ith_expr_dty).chain(std::iter::once(&mut *struct_dty)),
                )?;
                ty_ctx.substitute(&constr_map);
                self.implicit_ident_substitution.union(constr_map);
            }
        }

        Ok((ty_ctx, struct_ty))
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
        ret_dty: &mut DataTy,
        body: &mut Expr,
        expected_ty: &Option<Ty>,
    ) -> TyResult<(TyCtx, Ty)> {
        //Add missing lambda types
        //If we have some information about the expected type
        if let Some(expected_ty) = expected_ty {
            //The expected type should have function type
            if let TyKind::Fn(exp_params, _, _) = &expected_ty.ty {
                //The exptected fun type should have the same number of args
                if params.len() != exp_params.len() {
                    Err(TyError::WrongNumberOfArguments {
                        expected: exp_params.len(),
                        found: params.len(),
                        fun_name: Ident::new("lambda_fun"),
                    })?;
                }

                //Use expected type information to fill missing type annotations
                params.iter_mut().zip(exp_params.iter()).for_each(
                    |(param_decl, expected_param_ty)| {
                        if param_decl.ty.is_none() {
                            param_decl.ty = Some(expected_param_ty.clone())
                        }
                    },
                )
            } else {
                Err(TyError::UnexpectedType {
                    expected: expected_ty.clone(),
                    found: Ty::new(TyKind::Fn(
                        params
                            .iter()
                            .map(|decl| {
                                decl.ty
                                    .as_ref()
                                    .unwrap_or(&Ty::new(TyKind::Ident(Ident::new(
                                        &utils::fresh_name("type"),
                                    ))))
                                    .clone()
                            })
                            .collect(),
                        exec,
                        Box::new(Ty::new(TyKind::Data(ret_dty.clone()))),
                    )),
                })?
            }
        } else {
            //Else use fresh identifiers for missing type annotations
            params.iter_mut().for_each(|param_decl| {
                if param_decl.ty.is_none() {
                    param_decl.ty = Some(Ty::new(TyKind::Data(DataTy::new(DataTyKind::Ident(
                        Ident::new_impli(&utils::fresh_name("param_ty")),
                    )))))
                }
            })
        }

        // Build frame typing for this function
        let fun_frame = internal::append_idents_typed(
            &vec![],
            params
                .iter()
                .map(|ParamDecl { ident, ty, mutbl }| IdentTyped {
                    ident: ident.clone(),
                    ty: ty.as_ref().unwrap().clone(),
                    mutbl: *mutbl,
                })
                .collect(),
        );

        // Copy porvenance mappings into scope and append scope frame.
        // FIXME check that no variables are captured.
        let fun_ty_ctx = ty_ctx.clone().append_frame(fun_frame);

        //Check body of lambda_fun
        self.ty_check_expr(kind_ctx, fun_ty_ctx, exec, body)?;

        //Set type of params as type of idents in ty_ctx because some of the types
        //have may been inferred  my inferred while checking the body_expr
        params.iter_mut().for_each(|param_decl| {
            param_decl
                .ty
                .as_mut()
                .unwrap()
                .substitute(&self.implicit_ident_substitution);
        });

        // Check if the type of the body is a subtype of return_dty of lambda_fun
        // t <= t_f
        let ret_ty_is_implicit_ident = if let DataTyKind::Ident(ident) = &ret_dty.dty {
            ident.is_implicit
        } else {
            false
        };
        if !ret_ty_is_implicit_ident {
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
        }
        //if the return_dty is an implicit identifier: replace it by the type of the body
        else {
            ret_dty.dty = body.ty.as_ref().unwrap().dty().dty.clone();
        }

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
        let mut assigned_val_ty_ctx = self.ty_check_expr(kind_ctx, ty_ctx, exec, e)?;
        //TODO not very good solution
        if let PlaceExprKind::Deref(inner_pl) = &deref_expr.pl_expr {
            if let PlaceExprKind::Ident(ident) = &(**inner_pl).pl_expr {
                if let Ok(ident_ty) = assigned_val_ty_ctx.ty_of_ident(ident) {
                    if let TyKind::Data(ident_dty) = &ident_ty.ty {
                        if let DataTyKind::Ident(dty_ident) = &ident_dty.dty {
                            if dty_ident.is_implicit {
                                let new_dty = DataTy::new(DataTyKind::Ref(
                                    Provenance::Ident(Ident::new_impli(&fresh_name("$r"))),
                                    Ownership::Uniq,
                                    Memory::Ident(Ident::new_impli(&fresh_name("$m"))),
                                    Box::new(DataTy::new(DataTyKind::Ident(Ident::new_impli(
                                        &fresh_name("$d"),
                                    )))),
                                ));
                                let mut constr_map = ConstrainMap::new();
                                constr_map
                                    .dty_unifier
                                    .insert(dty_ident.name.clone(), new_dty);
                                println!("Inferred somethingA: {:#?}", constr_map);
                                assigned_val_ty_ctx.substitute(&constr_map);
                                self.implicit_ident_substitution.union(constr_map);
                            }
                        }
                    }
                }
            }
        }
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

        if is_dty_copyable(
            &elem_dty,
            &self.constraint_env,
            &mut self.implicit_ident_cons,
        ) {
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
        mut ty_ctx: TyCtx,
        exec: Exec,
        path: &mut Path,
        fun_kind: &mut Option<FunctionKind>,
        ef: &mut Expr,
        k_args: &mut Vec<ArgKinded>,
        args: &mut [Expr],
    ) -> TyResult<(TyCtx, Ty)> {
        //Get function name
        let fun_name = if let ExprKind::PlaceExpr(place_expr) = &ef.expr {
            let place = place_expr.to_place().unwrap();
            place.ident
        } else {
            panic!("function is not a place expr");
        };
        //Replace InferFromFirstArg-path by dty of first arg
        if let Path::InferFromFirstArg = path {
            let first_arg = args.first_mut().unwrap();
            ty_ctx = self.ty_check_expr(kind_ctx, ty_ctx, exec, first_arg)?;

            if let TyKind::Data(dty) = &first_arg.ty.as_ref().unwrap().ty {
                *path = Path::DataTy(match &dty.dty {
                    DataTyKind::Ref(_, _, _, dty) => (**dty).clone(),
                    _ => dty.clone(),
                })
            } else {
                Err(TyError::UnexpectedTypeKind {
                    expected_name: String::from("TyKind::Data"),
                    found: first_arg.ty.as_ref().unwrap().clone(),
                })?;
            }
        }

        //Infer function_kind from path
        let function_kind = match path {
            Path::Empty => FunctionKind::GlobalFun,
            Path::DataTy(dty) => {
                //TODO it would be nice to automaticlly infer not specified generics e.g allow
                //to write Point::function instead of Point::<T> function
                self.dty_well_formed(kind_ctx, &ty_ctx, Some(exec), dty)?;

                if fun_kind.is_none() {
                    let (fun_name, mut constr_map) = self.gl_ctx.fun_name_by_dty(
                        &self.constraint_env,
                        &mut self.implicit_ident_cons,
                        &fun_name.name,
                        dty,
                    )?;

                    if !constr_map.is_empty() {
                        unify::substitute_multiple(
                            &self.constraint_env,
                            &mut self.implicit_ident_cons,
                            &mut constr_map,
                            std::iter::once(dty),
                        )?;
                        ty_ctx.substitute(&constr_map);
                        self.implicit_ident_substitution.union(constr_map);
                    }

                    fun_name.fun_kind.clone()
                }
                //Binop-functions have already a function_kind
                else {
                    //Some hacky way to avoid some problems with InferFromFirstArgPath auto dereferencing
                    let first_arg = args.first_mut().unwrap();
                    if let TyKind::Data(dty) = &first_arg.ty.as_ref().unwrap().ty {
                        *path = Path::DataTy(dty.clone());
                    }

                    fun_kind.as_ref().unwrap().clone()
                }
            }
            Path::InferFromFirstArg => panic!("This should be already replaced by Path::DataTy"),
        };
        *fun_kind = Some(function_kind);

        //Get function type and number of implicit (inferred) kinded args (necessary for proper error messages)
        let (fun_ty, number_implicit_kargs) = {
            //Get function type from context
            let fun_ty = if let Ok(fun_ty) = self
                .gl_ctx
                .fun_ty_by_ident(&fun_name, fun_kind.as_ref().unwrap())
            {
                Ok(fun_ty)
            } else {
                Err(TyError::String(format!(
                "The provided function expression\n {:?}\n is not a identifier for a declared function",
                ef)))
            };

            //and infer implicit kinded args for traits and impls
            match fun_kind.as_ref().unwrap() {
                FunctionKind::GlobalFun => {
                    match fun_ty {
                        //if this is a global function in global context
                        Ok(fun_ty) => {
                            //Using fresh generic param names avoid name clashes
                            let fun_ty = fun_ty.fresh_generic_param_names();

                            (fun_ty, 0)
                        }
                        Err(err) => {
                            //if this is a lambda-function
                            if let Ok(ident_typed) = ty_ctx.ident_ty(&fun_name) {
                                (TypeScheme::new(ident_typed.ty.clone()), 0)
                            } else {
                                Err(err)?
                            }
                        }
                    }
                }
                FunctionKind::TraitFun(trait_name) => {
                    //Using fresh generic param names avoid name clashes
                    let fun_ty = fun_ty?.fresh_generic_param_names();

                    //Infer first generic parameter "Self" and other generic parameters of trait
                    let number_implicit_kargs = {
                        //Argument for "Self"
                        let path_dty = if let Path::DataTy(dty) = &path {
                            dty
                        } else {
                            panic!("Found a trait-function with an invalid path")
                        };
                        let self_arg = ArgKinded::DataTy(path_dty.clone());

                        //Find trait in context
                        let trait_def = self.gl_ctx.trait_ty_by_name(trait_name).unwrap();

                        //Implicit args for trait
                        let trait_args = trait_def.generic_params.iter().map(|gen| {
                            let mut gen = gen.clone();
                            gen.ident.name = fresh_name(&gen.ident.name);
                            gen.arg_kinded_implicit()
                        });

                        //Push self_arg and trait_args in front of k_args
                        let mut new_kargs = Vec::with_capacity(fun_ty.generic_params.len());
                        new_kargs.push(self_arg.clone());
                        new_kargs.extend(trait_args);
                        new_kargs.append(k_args);
                        *k_args = new_kargs;

                        1 + trait_def.generic_params.len()
                    };

                    (fun_ty, number_implicit_kargs)
                }
                FunctionKind::ImplFun(impl_ty_scheme, _) => {
                    //Using fresh generic param names avoid name clashes
                    let fun_ty = fun_ty?.fresh_generic_param_names();

                    //Use implicit identifier as args for impl
                    let impl_ty_scheme = impl_ty_scheme.fresh_generic_param_names();
                    let impl_args = impl_ty_scheme
                        .generic_params
                        .iter()
                        .map(|gen| gen.arg_kinded_implicit());

                    //Push impl_args in front of k_args
                    let mut new_kargs = Vec::with_capacity(fun_ty.generic_params.len());
                    new_kargs.extend(impl_args);
                    new_kargs.append(k_args);
                    *k_args = new_kargs;

                    //Unification of impl_ty_scheme and path-datatype to try to infer implicit identifier
                    let impl_mono_dty = if let TyKind::Data(dty) = &impl_ty_scheme.mono_ty.ty {
                        dty
                    } else {
                        panic!("Found invalid type of impl")
                    };
                    let path_dty = if let Path::DataTy(dty) = &path {
                        dty
                    } else {
                        panic!("Found a trait-function with an invalid path")
                    };
                    let (constr_map, _) = unify::constrain(impl_mono_dty, path_dty).unwrap();
                    k_args[0..impl_ty_scheme.generic_params.len()]
                        .iter_mut()
                        .for_each(|arg| arg.substitute(&constr_map));

                    (fun_ty, impl_ty_scheme.generic_params.len())
                }
            }
        };

        // TODO check well-kinded: FrameTyping, Prv, Ty
        //Apply kinded args
        let mut f_mono_ty = self.dep_app(
            kind_ctx,
            &mut ty_ctx,
            exec,
            &fun_ty,
            k_args,
            number_implicit_kargs,
        )?;

        //Check if this function is callable in this exec
        if let TyKind::Fn(_, exec_f, _) = &f_mono_ty.ty {
            if !exec_f.callable_in(exec) {
                Err(TyError::String(format!(
                    "Trying to apply function for execution resource `{}` \
                    under execution resource `{}`",
                    exec_f, exec
                )))?;
            }
        } else {
            panic!("Expected function type but found something else.")
        };

        //Tycheck args
        for i in 0..args.len() {
            let ith_arg: &mut Expr = &mut args[i];
            let ith_mono = if let TyKind::Fn(params, _, _) = &mut f_mono_ty.ty {
                &params[i]
            } else {
                panic!("Expected function type but found something else.")
            };

            //ith_arg.ty can be none if i is 0 and path is "InferFromFirstArg"
            if ith_arg.ty.is_none() {
                //Forward expected type to this expr to assist type inference when checking this expr
                ith_arg.ty = Some(ith_mono.clone());

                //Tycheck passed arg
                ty_ctx = self.ty_check_expr(kind_ctx, ty_ctx, exec, ith_arg)?;
            }

            //Make sure the type of the arg has the expected type
            let (mut constr_map, _) = unify::constrain(ith_arg.ty.as_ref().unwrap(), ith_mono)?;

            if !constr_map.is_empty() {
                unify::substitute_multiple(
                    &self.constraint_env,
                    &mut self.implicit_ident_cons,
                    &mut constr_map,
                    std::iter::once(&mut f_mono_ty),
                )?;
                ty_ctx.substitute(&constr_map);
                self.implicit_ident_substitution.union(constr_map);
            }
        }

        //Return type of the function
        let ret_dty = if let TyKind::Fn(_, _, ret_ty) = &f_mono_ty.ty {
            (**ret_ty).clone()
        } else {
            panic!("Expected function type but found something else.")
        };
        //Set function type of expr
        ef.ty = Some(f_mono_ty);

        // TODO check provenance relations
        return Ok((ty_ctx, ret_dty));
    }

    fn dep_app(
        &mut self,
        kind_ctx: &KindCtx,
        ty_ctx: &mut TyCtx,
        exec: Exec,
        ty_scheme: &TypeScheme,
        k_args: &mut Vec<ArgKinded>,
        //Number of implicit kinded args which are always automatically inferred and should not regarded in Err-messages
        number_implicit_kargs: usize,
    ) -> TyResult<Ty> {
        //Check the amount of kinded args
        if ty_scheme.generic_params.len() < k_args.len() {
            return Err(TyError::WrongNumberOfGenericParams {
                expected: ty_scheme.generic_params.len() - number_implicit_kargs,
                found: k_args.len() - number_implicit_kargs,
            });
        }
        //Check well-formedness of kinded args
        iter_TyResult_to_TyResult!(k_args.iter().map(|k_arg| self.arg_kinded_well_formed(
            kind_ctx,
            ty_ctx,
            Some(exec),
            k_arg
        )))?;
        //Check the kind of kinded args are like expected
        Self::check_args_have_correct_kinds(
            &ty_scheme.generic_params[0..k_args.len()].to_vec(),
            &k_args.to_vec(),
        )?;

        //Use implicit identifier for the remaing, missing kinded_args
        k_args.extend(
            ty_scheme.generic_params[k_args.len()..]
                .iter()
                .map(|i| i.arg_kinded_implicit()),
        );

        //Instantiate type_scheme
        let mut mono_ty = ty_scheme.partial_apply(k_args);

        //Check if there are some unfulfilled constraints
        //And add constraints on implicit identifier, which are necessary to fulfills the constraints, to theta
        //The constraints for implicit identifier are checked in unfication when they are replaces by other types
        for con in &mono_ty.constraints {
            if let Ok(mut constr_map) = self
                .constraint_env
                .check_constraint(con, &mut self.implicit_ident_cons)
            {
                //Constraint check may also infer some generic args
                if !constr_map.is_empty() {
                    unify::substitute_multiple(
                        &self.constraint_env,
                        &mut self.implicit_ident_cons,
                        &mut constr_map,
                        std::iter::once(&mut mono_ty.mono_ty),
                    )?;
                    ty_ctx.substitute(&constr_map);
                    self.implicit_ident_substitution.union(constr_map);
                }
            } else {
                Err(TyError::UnfullfilledConstraint(con.clone()))?;
            }
        }

        Ok(mono_ty.mono_ty)
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
        mut ty_ctx: TyCtx,
        exec: Exec,
        pl_expr: &mut PlaceExpr,
    ) -> TyResult<(TyCtx, Ty)> {
        //if the pl_expr is a deref of an implicit ident: replace it
        //by a reference to an implicit ident
        //TODO not very good solution
        if let PlaceExprKind::Deref(inner_pl) = &pl_expr.pl_expr {
            if let PlaceExprKind::Ident(ident) = &(**inner_pl).pl_expr {
                if let Ok(ident_ty) = ty_ctx.ty_of_ident(ident) {
                    if let TyKind::Data(ident_dty) = &ident_ty.ty {
                        if let DataTyKind::Ident(dty_ident) = &ident_dty.dty {
                            if dty_ident.is_implicit {
                                let new_dty = DataTy::new(DataTyKind::Ref(
                                    Provenance::Ident(Ident::new_impli(&fresh_name("$r"))),
                                    Ownership::Shrd,
                                    Memory::Ident(Ident::new_impli(&fresh_name("$m"))),
                                    Box::new(DataTy::new(DataTyKind::Ident(Ident::new_impli(
                                        &fresh_name("$d"),
                                    )))),
                                ));
                                let mut constr_map = ConstrainMap::new();
                                constr_map
                                    .dty_unifier
                                    .insert(dty_ident.name.clone(), new_dty);
                                println!("Inferred somethingA: {:#?}", constr_map);
                                ty_ctx.substitute(&constr_map);
                                self.implicit_ident_substitution.union(constr_map);
                            }
                        }
                    }
                }
            }
        }

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
        if is_ty_copyable(
            pl_expr.ty.as_ref().unwrap(),
            &self.constraint_env,
            &mut self.implicit_ident_cons,
        ) {
            Ok((ty_ctx, pl_expr.ty.as_ref().unwrap().clone()))
        } else {
            Err(TyError::String("Data type is not copyable.".to_string()))
        }
    }

    fn ty_check_pl_expr_without_deref(
        &mut self,
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
            let res_ty_ctx =
                if is_ty_copyable(&pl_ty, &self.constraint_env, &mut self.implicit_ident_cons) {
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
            _ => Err(TyError::IllegalProjection(format!(
                "Unexpected type or projection access. Found access: {:?} on ty {:#?}",
                proj,
                tuple_expr.ty.as_ref().unwrap()
            ))),
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
        exec: Option<Exec>,
        ty: &TypeScheme,
    ) -> TyResult<()> {
        let kind_ctx = kind_ctx.clone().append_idents(ty.generic_params.clone());
        for constaint in &ty.constraints {
            self.constraint_well_formed(&kind_ctx, ty_ctx, exec, constaint)?;
        }
        self.ty_well_formed(&kind_ctx, ty_ctx, exec, &ty.mono_ty)
    }

    fn arg_kinded_well_formed(
        &self,
        kind_ctx: &KindCtx,
        ty_ctx: &TyCtx,
        exec: Option<Exec>,
        arg: &ArgKinded,
    ) -> TyResult<()> {
        match arg {
            ArgKinded::Ident(_) => panic!("This should have been replaced in parser."),
            ArgKinded::Nat(nat) => self.nat_well_formed(kind_ctx, nat),
            ArgKinded::Memory(mem) => self.memory_well_formed(kind_ctx, mem),
            ArgKinded::Ty(ty) => self.ty_well_formed(kind_ctx, ty_ctx, exec, ty),
            ArgKinded::DataTy(dty) => self.dty_well_formed(kind_ctx, ty_ctx, exec, dty),
            ArgKinded::Provenance(prov) => self.prov_well_formed(kind_ctx, ty_ctx, prov),
        }
    }

    fn nat_well_formed(&self, kind_ctx: &KindCtx, nat: &Nat) -> TyResult<()> {
        match nat {
            Nat::Ident(ident) => {
                if kind_ctx.ident_of_kind_exists(ident, Kind::Nat) {
                    Ok(())
                } else {
                    Err(TyError::from(CtxError::KindedIdentNotFound(ident.clone())))
                }
            }
            Nat::Lit(_) => Ok(()),
            Nat::BinOp(_, nat1, nat2) => {
                self.nat_well_formed(kind_ctx, nat1)?;
                self.nat_well_formed(kind_ctx, nat2)
            }
            Nat::App(ident, nats) => {
                for nat in nats {
                    self.nat_well_formed(kind_ctx, nat)?
                }
                panic!("What is ident {:?}?", ident)
            }
        }
    }

    fn memory_well_formed(&self, kind_ctx: &KindCtx, mem: &Memory) -> TyResult<()> {
        match mem {
            Memory::CpuMem => Ok(()),
            Memory::GpuGlobal => Ok(()),
            Memory::GpuShared => Ok(()),
            Memory::GpuLocal => Ok(()),
            Memory::Ident(ident) => {
                if ident.is_implicit || kind_ctx.ident_of_kind_exists(ident, Kind::Memory) {
                    Ok(())
                } else {
                    Err(TyError::from(CtxError::KindedIdentNotFound(ident.clone())))
                }
            }
        }
    }

    // TODO respect memory
    fn ty_well_formed(
        &self,
        kind_ctx: &KindCtx,
        ty_ctx: &TyCtx,
        exec: Option<Exec>,
        ty: &Ty,
    ) -> TyResult<()> {
        match &ty.ty {
            TyKind::Data(dty) => self.dty_well_formed(kind_ctx, ty_ctx, exec, dty)?,
            TyKind::Ident(ident) => {
                if !ident.is_implicit && !kind_ctx.ident_of_kind_exists(ident, Kind::Ty) {
                    Err(CtxError::KindedIdentNotFound(ident.clone()))?
                }
            }
            TyKind::Fn(param_tys, exec, ret_ty) => {
                self.ty_well_formed(&kind_ctx, ty_ctx, Some(*exec), ret_ty)?;
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

                    self.ty_well_formed(&kind_ctx, ty_ctx, Some(*exec), param_ty)?;
                }
            }
            TyKind::Dead(_) => {}
        }

        Ok(())
    }

    // TODO respect memory
    fn dty_well_formed(
        &self,
        kind_ctx: &KindCtx,
        ty_ctx: &TyCtx,
        exec: Option<Exec>,
        dty: &DataTy,
    ) -> TyResult<()> {
        match &dty.dty {
            // TODO variables of Dead types can be reassigned. So why do we not have to check
            //  well-formedness of the type in Dead(ty)? (According paper).
            DataTyKind::Scalar(_)
            | DataTyKind::Atomic(_)
            | DataTyKind::Range
            | DataTyKind::RawPtr(_)
            | DataTyKind::Dead(_) => {}
            DataTyKind::Ident(ident) => {
                if !ident.is_implicit && !kind_ctx.ident_of_kind_exists(ident, Kind::DataTy) {
                    Err(CtxError::KindedIdentNotFound(ident.clone()))?
                }
            }
            DataTyKind::Struct(struct_mono_ty) => {
                let StructDataType {
                    name,
                    attributes,
                    generic_args,
                } = struct_mono_ty;
                let struct_decl = self.gl_ctx.struct_by_name(name)?;
                Self::check_args_have_correct_kinds(&struct_decl.generic_params, generic_args)?;
                iter_TyResult_to_TyResult!(attributes
                    .iter()
                    .map(|field| self.dty_well_formed(kind_ctx, ty_ctx, exec, &field.ty)))?;
            }
            DataTyKind::Ref(Provenance::Value(prv), own, mem, dty) => {
                self.memory_well_formed(kind_ctx, mem)?;
                let elem_ty = dty.as_ref();
                if !elem_ty.is_fully_alive() {
                    return Err(TyError::ReferenceToDeadTy);
                }
                let loans = ty_ctx.loans_in_prv(prv)?;
                if !loans.is_empty() {
                    let mut exists = false;
                    //TODO what to do if exec is None?
                    if exec.is_some() {
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
                                exec.unwrap(),
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
                    }
                    if !exists {
                        if let DataTyKind::ArrayShape(_, _) = &dty.dty {
                            eprintln!(
                                "WARNING: Did not check well-formedness of view type reference."
                            )
                        } else {
                            return Err(TyError::ReferenceToIncompatibleType);
                        }
                    }
                }
                self.dty_well_formed(kind_ctx, ty_ctx, exec, elem_ty)?;
            }
            DataTyKind::Ref(Provenance::Ident(ident), _, mem, dty) => {
                self.memory_well_formed(kind_ctx, mem)?;
                self.prov_well_formed(kind_ctx, ty_ctx, &Provenance::Ident(ident.clone()))?;
                self.dty_well_formed(kind_ctx, ty_ctx, exec, dty.as_ref())?;
            }
            DataTyKind::ThreadHierchy(th_hy) => {
                self.thread_hierchy_ty_well_formed(kind_ctx, th_hy)?
            }
            DataTyKind::SplitThreadHierchy(th_hy, n) => {
                self.thread_hierchy_ty_well_formed(kind_ctx, th_hy)?;
                self.nat_well_formed(kind_ctx, n)?;
            }
            DataTyKind::Tuple(elem_dtys) => {
                for elem_dty in elem_dtys {
                    self.dty_well_formed(kind_ctx, ty_ctx, exec, elem_dty)?;
                }
            }
            DataTyKind::Array(elem_dty, n) => {
                self.dty_well_formed(kind_ctx, ty_ctx, exec, elem_dty.as_ref())?;
                self.nat_well_formed(kind_ctx, n)?;
            }
            DataTyKind::ArrayShape(elem_dty, n) => {
                self.dty_well_formed(kind_ctx, ty_ctx, exec, &elem_dty.as_ref().clone())?;
                self.nat_well_formed(kind_ctx, n)?;
            }
            DataTyKind::At(elem_dty, Memory::Ident(ident)) => {
                if !kind_ctx.ident_of_kind_exists(ident, Kind::Memory) {
                    Err(TyError::CtxError(CtxError::KindedIdentNotFound(
                        ident.clone(),
                    )))?;
                }
                self.dty_well_formed(kind_ctx, ty_ctx, exec, &elem_dty.as_ref())?;
            }
            DataTyKind::At(elem_dty, _) => {
                self.dty_well_formed(kind_ctx, ty_ctx, exec, elem_dty.as_ref())?;
            }
        }

        Ok(())
    }

    fn thread_hierchy_ty_well_formed(
        &self,
        kind_ctx: &KindCtx,
        tht: &ThreadHierchyTy,
    ) -> TyResult<()> {
        match tht {
            ThreadHierchyTy::BlockGrp(n1, n2, n3, n4, n5, n6) => {
                self.nat_well_formed(kind_ctx, n1)?;
                self.nat_well_formed(kind_ctx, n2)?;
                self.nat_well_formed(kind_ctx, n3)?;
                self.nat_well_formed(kind_ctx, n4)?;
                self.nat_well_formed(kind_ctx, n5)?;
                self.nat_well_formed(kind_ctx, n6)
            }
            ThreadHierchyTy::ThreadGrp(n1, n2, n3) => {
                self.nat_well_formed(kind_ctx, n1)?;
                self.nat_well_formed(kind_ctx, n2)?;
                self.nat_well_formed(kind_ctx, n3)
            }
            ThreadHierchyTy::WarpGrp(n) => self.nat_well_formed(kind_ctx, n),
            ThreadHierchyTy::Warp => Ok(()),
            ThreadHierchyTy::Thread => Ok(()),
        }
    }

    fn prov_well_formed(
        &self,
        kind_ctx: &KindCtx,
        ty_ctx: &TyCtx,
        prov: &Provenance,
    ) -> TyResult<()> {
        match prov {
            Provenance::Value(prv) => match ty_ctx.loans_in_prv(prv) {
                Ok(_) => Ok(()),
                Err(err) => Err(TyError::from(err)),
            },
            Provenance::Ident(ident) => {
                if ident.is_implicit || kind_ctx.ident_of_kind_exists(ident, Kind::Provenance) {
                    Ok(())
                } else {
                    Err(TyError::from(CtxError::KindedIdentNotFound(ident.clone())))
                }
            }
        }
    }

    fn constraint_scheme_well_formed(
        &self,
        kind_ctx: &KindCtx,
        ty_ctx: &TyCtx,
        exec: Option<Exec>,
        cscheme: &ConstraintScheme,
    ) -> TyResult<()> {
        let kind_ctx = kind_ctx.clone().append_idents(cscheme.generics.clone());

        iter_TyResult_to_TyResult!(cscheme
            .implican
            .iter()
            .map(|implied| self.constraint_well_formed(&kind_ctx, ty_ctx, exec, implied)))?;

        self.constraint_well_formed(&kind_ctx, ty_ctx, exec, &cscheme.implied)
    }

    fn constraint_well_formed(
        &self,
        kind_ctx: &KindCtx,
        ty_ctx: &TyCtx,
        exec: Option<Exec>,
        constraint: &Constraint,
    ) -> TyResult<()> {
        let TraitMonoType { name, generics } = &constraint.trait_bound;
        let trait_def = self.gl_ctx.trait_ty_by_name(name)?;
        self.dty_well_formed(kind_ctx, ty_ctx, exec, &constraint.param)?;
        Self::check_args_have_correct_kinds(&trait_def.generic_params, generics)?;
        iter_TyResult_to_TyResult!(generics
            .iter()
            .map(|gen| self.arg_kinded_well_formed(kind_ctx, ty_ctx, exec, gen)))
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
        _ => Err(TyError::IllegalProjection(format!(
            "Unexpected type or projection access. Found access: {:?} on ty {:#?}",
            proj, ty
        ))),
    }
}

fn is_ty_copyable(
    ty: &Ty,
    constraint_env: &ConstraintEnv,
    implicit_ident_cons: &mut IdentConstraints,
) -> bool {
    match &ty.ty {
        TyKind::Data(dty) => is_dty_copyable(dty, constraint_env, implicit_ident_cons),
        TyKind::Fn(_, _, _) => true,
        TyKind::Ident(_) => false,
        TyKind::Dead(_) => panic!(
            "This case is not expected to mean anything.\
            The type is dead. There is nothing we can do with it."
        ),
    }
}

fn is_dty_copyable(
    dty: &DataTy,
    constraint_env: &ConstraintEnv,
    implicit_ident_cons: &mut IdentConstraints,
) -> bool {
    use DataTyKind::*;

    let is_dty_copy_constraint = Constraint {
        param: dty.clone(),
        trait_bound: copy_Trait(),
    };

    match &dty.dty {
        // FIXME thread hierarchies and their splits should be non-copyable!
        ThreadHierchy(_) => true,
        SplitThreadHierchy(_, _) => true,
        Dead(_) => panic!(
            "This case is not expected to mean anything.\
            The type is dead. There is nothign we can do with it."
        ),
        _ => constraint_env
            .check_constraint(&is_dty_copy_constraint, implicit_ident_cons)
            .is_ok(),
    }
}
