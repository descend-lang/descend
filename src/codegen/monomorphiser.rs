use std::{
    collections::{hash_map::RandomState, HashMap, HashSet},
    vec,
};

use crate::{
    ast::{
        visit_mut::{walk_expr, VisitMut},
        *,
    },
    ty_check::unify::{constrain, ConstrainMap, Constrainable},
};

/// Convert all non-struct items to global functions and monomorphise all constraint generic parameters. <br>
/// The global functions will have new unique non-C++-keywords names.
///
/// Input:
///  * Well typed items (structs, traits, global functions, impls)
///
/// Output:
///  * list of all structs without constraints
///  * global functions which have no constraint generic parameters anymore
pub fn monomorphise_constraint_generics(mut items: Vec<Item>) -> (Vec<StructDecl>, Vec<FunDef>) {
    // Copy all trait_defs to prevent borrowing errors in next statement
    let trait_defs = items
        .iter()
        .filter_map(|item| {
            if let Item::TraitDef(trait_def) = item {
                Some(trait_def.clone())
            } else {
                None
            }
        })
        .collect::<Vec<TraitDef>>();
    // Add all default function implementations from traits to impls which does not override this function
    items.iter_mut().for_each(|item| match item {
        Item::ImplDef(impl_def) => {
            add_inherited_fun_defs(impl_def, &trait_defs);
        }
        _ => (),
    });

    // Monomorphise global functions, traits, impls to multiple global functions
    let fun_defs = Monomorphiser::monomorphise(&items);

    // Collect struct defs
    let struct_decls = items
        .into_iter()
        .filter_map(|item| {
            if let Item::StructDecl(mut struct_decl) = item {
                // Constraints of structs are checked while Typechecking are not needed anymore
                struct_decl.constraints.clear();
                Some(struct_decl)
            } else {
                None
            }
        })
        .collect::<Vec<StructDecl>>();

    (struct_decls, fun_defs)
}

/// Struct which includes all information which are to remove all function applications
/// of functions with constraint kinded identifiers. <br>
/// This is used to implement `Visitor` for this struct and visit every function
/// application and replace it if necessary
struct Monomorphiser<'a> {
    /// Reference to items (to search impls or traits)
    items: &'a Vec<Item>,
    /// List of all function definitions in the input-program (global functions, impl-Methods, trait-funs). <br>
    /// The "String"-value describes the new unique global function-name of the function
    funs: Vec<(FunctionName, FunDef, String)>,
    /// * `FunctionName` - uniqly describes a function in input-program
    /// * `Vec<ArgKinded>` - consists of the arguments for the constraint-parameter
    /// of the function corresponding to `FunctionName`
    /// * a pair of these two describes a function application
    /// * `String` - describes the new unique global function-name of the monomorphised function which
    /// is generated for the function application
    generated: HashMap<(FunctionName, Vec<ArgKinded>), String>,
    /// List of new generated functions which must be still visited
    /// * `FunctionName` - corresponding to the name of the original function which is monomorphised
    /// * `FunDef` - functiond definition of monomorphised function
    generated_funs: Vec<(FunctionName, FunDef)>,
    /// NameGenerator to generate unique names and prevents name conflicts
    name_generator: NameGenerator,
}

impl<'a> Monomorphiser<'a> {
    /// Convert all non-struct items to global functions and monomorphise all constraint generic parameters.
    ///
    /// Input:
    ///  * Well typed items (structs, traits, global functions, impls
    /// where trait-impls override all function-definitions of the trait)
    ///
    /// Output:
    ///  * global functions which have no constraint generic parameters anymore
    pub fn monomorphise(items: &Vec<Item>) -> Vec<FunDef> {
        // Create a vector of all functions including global functions, methods in impls and trait functions
        let (mut funs, name_generator) = items.iter().fold(
            (Vec::new(), NameGenerator::new()),
            |(mut funs, mut name_generator), item| {
                match item {
                    Item::ImplDef(impl_def) => {
                        funs.extend(impl_to_global_funs(impl_def).map(|(fun_name, fun_def)| {
                            (
                                fun_name.clone(),
                                fun_def,
                                name_generator.generate_name(&fun_name, None),
                            )
                        }))
                    }
                    Item::FunDef(fun_def) => {
                        let fun_name = FunctionName::global_fun(&fun_def.name);
                        funs.push((
                            fun_name.clone(),
                            fun_def.clone(),
                            name_generator.generate_name(&fun_name, None),
                        ));
                    }
                    Item::TraitDef(trait_def) => {
                        funs.extend(trait_to_global_funs(trait_def).map(|(fun_name, fun_def)| {
                            (
                                fun_name.clone(),
                                fun_def,
                                name_generator.generate_name(&fun_name, None),
                            )
                        }))
                    }
                    Item::StructDecl(_) => (),
                };
                (funs, name_generator)
            },
        );

        // List of all new generated monomorphised functions
        let mut mono_funs: HashMap<FunctionName, Vec<FunDef>, RandomState> = HashMap::new();
        // Monomorphiser to visit all function applications
        let mut monomorphiser = Monomorphiser {
            items: items,
            funs: funs.clone(),
            generated: HashMap::new(),
            generated_funs: Vec::new(),
            name_generator,
        };

        // Visit original functions to monomorphise function calls
        funs.iter_mut().for_each(|(_, fun_def, _)| {
            // Visit only functions without constraint generic params
            if fun_def.generic_params.iter().fold(true, |res, gen| {
                res && !fun_def
                    .constraints
                    .iter()
                    .find(|con| {
                        if let DataTyKind::Ident(ident) = &con.param.dty {
                            ident.name == gen.ident.name
                        } else {
                            false
                        }
                    })
                    .is_some()
            }) {
                monomorphiser.visit_fun_def(fun_def)
            }
        });
        // And visit all new generated monomorphised functions
        while !monomorphiser.generated_funs.is_empty() {
            let (fun_name, mut mono_fun) = monomorphiser.generated_funs.pop().unwrap();
            // get entry in `mono_funs` or create a new entry
            let mono_funs_with_name = match mono_funs.get_mut(&fun_name) {
                Some(mono_funs) => mono_funs,
                None => {
                    let mono_funs_with_name = Vec::new();
                    mono_funs.insert(fun_name.clone(), mono_funs_with_name);
                    mono_funs.get_mut(&fun_name).unwrap()
                }
            };
            // Visit this function to monomorphise function calls
            monomorphiser.visit_fun_def(&mut mono_fun);
            // And insert it in list of generated monomorphised function
            mono_funs_with_name.push(mono_fun);
        }

        // Create a result vector of all monomorphised functions and all original functions which did not need to be monomorphised
        // Keep the original order of functions
        funs.into_iter().fold(
            Vec::<FunDef>::new(), |mut funs, (fun_name, mut fun_def, global_fun_name)| {
                match fun_name.fun_kind {
                    FunctionKind::GlobalFun |
                    FunctionKind::ImplFun(_, _) =>
                        match mono_funs.remove(&fun_name) {
                            // If there are multiple monomorphised functions of the original function
                            Some(mut mono_funs) => {
                                // Sort them by name
                                mono_funs.sort_by(|a, b| a.name.partial_cmp(&b.name).unwrap());
                                // And insert them into result list
                                funs.extend(
                                    mono_funs.into_iter().map(|fun|
                                        fun
                                    )
                                );
                            },
                            // The original function was not monomorphised
                            None => {
                                let fun_generics = &fun_def.generic_params;

                                // Because the original functions is never called but has constraint generics
                                if fun_generics.iter()
                                    .find(|gen|{
                                        fun_def.constraints.iter()
                                        .find(|con|
                                            if let DataTyKind::Ident(ident) = &con.param.dty {
                                                ident.name == gen.ident.name
                                            } else {
                                                false
                                            }
                                        ).is_some()
                                    }).is_some() {
                                    eprintln!("function \"{}\" of kind {:?} is never used. Because this function has constraint \
                                        generic params, which needs to be monomoprhised, no code can be generated \
                                        for this function.",
                                        fun_name.name,
                                        match fun_name.fun_kind {
                                            FunctionKind::GlobalFun => "GlobalFun".to_string(),
                                            FunctionKind::TraitFun(name) => format!("TraitFun({})", name),
                                            FunctionKind::ImplFun(_, _) => "ImplFun".to_string()
                                        })
                                }
                                // Because the original functions did not need to be monomorphised
                                else {
                                    fun_def.name = global_fun_name;
                                    funs.push(fun_def);
                                }
                            }
                        }
                    // Ignore trait_functions
                    FunctionKind::TraitFun(_) => (),
                }
            funs
        })
    }

    /// Monomorphise a function application. The function application must not
    /// contain any kinded identifier as arguments for constraint identifiers. <br>
    /// If this calls a non-global function or a function which contains constraint kinded identifier,
    /// it will be replaced by a function call of a global function which does not contain constraints
    /// * `fun_kind` - FunctionKind of the function which is applied
    /// * `fun` - expression containing the name of the function
    /// * `generic_args` - kinded arguments for the kinded identifier of the function
    fn monomorphise_fun_app(
        &mut self,
        fun_kind: &mut Option<FunctionKind>,
        fun: &mut Box<Expr>,
        generic_args: &mut Vec<ArgKinded>,
    ) {
        // Function to set the new global function name and kind of a function within an function application
        fn set_gl_fun_name(
            fun: &mut Box<Expr>,
            fun_kind: &mut Option<FunctionKind>,
            new_fun_name: String,
        ) {
            *fun_kind = Some(FunctionKind::GlobalFun);
            match &mut fun.expr {
                ExprKind::PlaceExpr(place_expr) => {
                    if let PlaceExprKind::Ident(ident) = &mut place_expr.pl_expr {
                        ident.name = new_fun_name;
                    } else {
                        panic!("Dont know how to set function name")
                    }
                }
                _ => panic!("Dont know how to set function name"),
            }
        }

        // Find name, reference to FunDef and the unique global function name of this application
        let (mut fun_name, mut fun_def, mut global_fun_name) = {
            let fun_name = match &fun.expr {
                ExprKind::PlaceExpr(place_expr) => {
                    if let PlaceExprKind::Ident(ident) = &place_expr.pl_expr {
                        &ident.name
                    } else {
                        panic!("Dont know how to get function name")
                    }
                }
                _ => panic!("Dont know how to get function name"),
            };
            let fun_name = FunctionName {
                name: fun_name.clone(),
                fun_kind: fun_kind.as_ref().unwrap().clone(),
            };
            // Search function definition
            let (_, fun_def, global_fun_name) =
                match self.funs.iter().find(|(name, _, _)| *name == fun_name) {
                    Some(res) => res,
                    //If we dont find function definition of this function this must
                    //be a predeclared or already monomorphised function
                    None => return,
                };
            (fun_name, fun_def, global_fun_name)
        };

        // if the called function is a trait function, replace it by the correct impl-function
        if let FunctionKind::TraitFun(_) = fun_kind.as_ref().unwrap() {
            self.replace_trait_fun_app(&mut fun_name, fun_kind, generic_args);
            // Refresh reference to FunDef and the unique global function name of this application
            match self.funs.iter().find(|(name, _, _)| *name == fun_name) {
                Some((_, new_fun_name, new_global_fun_name)) => {
                    fun_def = new_fun_name;
                    global_fun_name = new_global_fun_name;
                }
                None => panic!("did not find function {:#?}", fun_name),
            };
        }

        // if the called function has no constraints, it is sufficient to adjust the name of the function
        // to refer the global function instead of e.g. an impl-method
        if fun_def.constraints.len() == 0 {
            set_gl_fun_name(fun, fun_kind, global_fun_name.clone());
            return;
        }

        // Prevents borrowing errors
        let fun_generics = fun_def.generic_params.clone();
        // Find now all constraint kinded identifier with their corresponding generic arguments of
        // this function call
        let (con_generics, con_generic_args): (Vec<IdentKinded>, Vec<ArgKinded>) = fun_generics
            .iter()
            .zip(generic_args.iter())
            .filter_map(|(gen, gen_arg)| {
                assert!(gen.kind == gen_arg.kind());
                // Check if the generic param "gen" has constraint
                if fun_def
                    .constraints
                    .iter()
                    .find(|con| {
                        if let DataTyKind::Ident(ident) = &con.param.dty {
                            ident.name == gen.ident.name
                        } else {
                            false
                        }
                    })
                    .is_some()
                {
                    //The arg must not be an identifier
                    assert!(match gen_arg {
                        ArgKinded::DataTy(dty) => !matches!(dty.dty, DataTyKind::Ident(_)),
                        _ => false,
                    });

                    Some((gen.clone(), gen_arg.clone()))
                } else {
                    None
                }
            })
            .unzip();

        // This key describes uniquely the monomorphised function
        let key_generated = (fun_name, con_generic_args);
        let new_fun_name =
            // Does a corresponding function definition already exists?
            if let Some(fun_name) = self.generated.get(&key_generated) {
                fun_name.clone()
            } else {
                // Create a new function definition for this specific function call
                let mut mono_fun = monomorphise_fun(&fun_def, &con_generics, &key_generated.1);
                let new_fun_name = self.name_generator.generate_name(&key_generated.0, Some(&key_generated.1));
                mono_fun.name = new_fun_name.clone();
                // And insert it in corresponding lists
                self.generated_funs.push((key_generated.0.clone(), mono_fun));
                self.generated.insert(key_generated, new_fun_name.clone());
                new_fun_name
            };

        // Reduce the number of generic arguments of this function call to match the
        // required number of generic args of the monomorphised function
        *generic_args = fun_generics
            .iter()
            .zip(generic_args.into_iter())
            .filter_map(|(generic, generic_arg)| {
                if con_generics
                    .iter()
                    .find(|con_generic| con_generic.ident.name == generic.ident.name)
                    .is_none()
                {
                    Some(generic_arg.clone())
                } else {
                    None
                }
            })
            .collect();
        // Adjust also function name
        set_gl_fun_name(fun, fun_kind, new_fun_name);
    }

    /// Replace a trait-function application by the application of the correct impl-fun
    fn replace_trait_fun_app(
        &mut self,
        fun_name: &mut FunctionName,
        fun_kind: &mut Option<FunctionKind>,
        generic_args: &mut Vec<ArgKinded>,
    ) {
        // Find the trait-definition of trait-fun
        let trait_def = if let FunctionKind::TraitFun(name) = fun_kind.as_ref().unwrap() {
            if let Some(Item::TraitDef(trait_def)) = self.items.iter().find(|item| match item {
                Item::TraitDef(trait_def) => trait_def.name == *name,
                _ => false,
            }) {
                trait_def
            } else {
                panic!("did not found a trait-item with name: {}", name)
            }
        } else {
            panic!("trait_fun_call with non TraitFun-Kind!")
        };

        // The generic arg for "Self" which is the datatype of the impl
        let impl_dty = match generic_args.first().unwrap() {
            ArgKinded::DataTy(dty) => dty.clone(),
            _ => panic!("Found non-datatype ArgKinded as generic arg for Self"),
        };

        // Find the definition of the impl which implements the trait
        // and remember the substitutions which are necessary to unify
        // "impl_dty" with the datatype of the impl
        let (impl_def, dty_unfication) = {
            let mut result: Option<(&ImplDef, ConstrainMap)> = None;
            if self
                .items
                .iter()
                .find(|item| match item {
                    Item::ImplDef(impl_def) if impl_def.trait_impl.is_some() => {
                        if impl_def.trait_impl.as_ref().unwrap().name == trait_def.name {
                            // Get typescheme from impl_def
                            let impl_ty_scheme = impl_def.ty().make_generic_params_implicit();
                            // The type should be a datatype
                            let impl_dty_canidate =
                                if let TyKind::Data(dty) = impl_ty_scheme.mono_ty.ty {
                                    dty.clone()
                                } else {
                                    panic!("Expected a datatype but found a non-datatype")
                                };

                            // Try to unify "impl_dty" with current datatype-candidate for the impl
                            if let Ok((dty_unfication, _)) =
                                constrain(&impl_dty_canidate, &impl_dty)
                            {
                                result = Some((impl_def, dty_unfication));
                                true
                            } else {
                                false
                            }
                        } else {
                            false
                        }
                    }
                    _ => false,
                })
                .is_some()
            {
                result.unwrap()
            } else {
                panic!(
                    "could not find implementation of trait {} for dty {:#?}",
                    trait_def.name, impl_dty
                );
            }
        };

        // The first generic arg is for "Self"
        // The next args are the generic args for the generic params of the trait
        let trait_mono_args =
            Vec::from_iter(generic_args.drain(1..trait_def.generic_params.len() + 1));
        // And the remaining generic args are for the generic params of the function itself
        let fun_generic_args = generic_args.drain(1..);

        // Infer generic args of impl from impl_dty and trait_mono_args
        // E.g. Infer "A,B,C" in "impl<A, B, C> Eq<A, B> for Point<B, C> ..."
        // Therefore unify "Eq<A, B>" and "Eq<trait_mono_args>" where trait_mono_args are the
        // passed generic arguments in the function application for the generic params of the trait
        let impl_trait_mono = TraitMonoType {
            name: trait_def.name.clone(),
            // Use as generics args for the trait the same generic args like in the impl_def,
            // but replace explicit identifiers with implicit identifiers and apply "dty_unfication"
            generic_args: impl_def
                .trait_impl
                .as_ref()
                .unwrap()
                .generic_args
                .iter()
                .map(|gen_arg| {
                    let mut gen_arg = gen_arg.clone();
                    gen_arg = gen_arg.subst_idents_kinded(
                        impl_def.generic_params.iter(),
                        impl_def
                            .generic_params
                            .iter()
                            .map(|k_ident| k_ident.arg_kinded_implicit())
                            .collect::<Vec<_>>()
                            .iter(),
                    );
                    gen_arg.substitute(&dty_unfication);
                    gen_arg
                })
                .collect(),
        };
        let trait_mono = TraitMonoType {
            name: trait_def.name.clone(),
            generic_args: trait_mono_args,
        };
        let dty_unfication2 =
            if let Ok((dty_unfication, _)) = constrain(&impl_trait_mono, &trait_mono) {
                dty_unfication
            } else {
                panic!(
                "Cannot unify trait_mono with trait_mono_ty of impl\nconstrain {:#?}\nwith {:#?}",
                impl_trait_mono, trait_mono
                )
            };

        // Collect inferred generic args by apply substitutions to the generic params of the impl
        let substitute_impl_args = {
            let mut substitution = dty_unfication;
            substitution.composition(dty_unfication2);
            substitution
        };
        let impl_generics_args = impl_def
            .generic_params
            .iter()
            .map(|generic| {
                let mut arg = generic.arg_kinded();
                arg.substitute(&substitute_impl_args);
                arg
            })
            .collect::<Vec<ArgKinded>>();

        *fun_name = FunctionName::from_impl(&fun_name.name, impl_def);
        *fun_kind = Some(fun_name.fun_kind.clone());
        *generic_args = impl_generics_args
            .into_iter()
            .chain(fun_generic_args.into_iter())
            .collect();
    }
}

// Visit-Implementation for Monomorphiser
// Visit all function applications and call "monomorphise_fun_app"
impl<'a> VisitMut for Monomorphiser<'a> {
    fn visit_expr(&mut self, expr: &mut Expr) {
        match &mut expr.expr {
            ExprKind::App(path, fun_kind, fun, generic_args, exprs) => {
                // Path is not longer needed
                *path = Path::Empty;

                self.monomorphise_fun_app(fun_kind, fun, generic_args);
                exprs.iter_mut().for_each(|expr| self.visit_expr(expr))
            }
            ExprKind::DepApp(_, _) => panic!("Does this happen? What to do now?"),
            _ => walk_expr(self, expr),
        }
    }
}

/// Create a new FunDef without constraint generics. The constraint generics inside the function are substituted by the passed ArgKinded
/// * `fun_def` - function definition which should be monomorphised
/// * `cons_generics` - constraint kinded identifier which should be removed and replaced by `cons_generic_args`
/// * `cons_generic_args` kinded arguments for the kinded identifier
fn monomorphise_fun(
    fun_def: &FunDef,
    cons_generics: &Vec<IdentKinded>,
    cons_generic_args: &Vec<ArgKinded>,
) -> FunDef {
    FunDef {
        name: fun_def.name.clone(),
        generic_params: fun_def
            .generic_params
            .iter()
            .filter_map(|generic| {
                if cons_generics
                    .iter()
                    .find(|cons_generic| cons_generic.ident.name == generic.ident.name)
                    .is_none()
                {
                    Some(generic.clone())
                } else {
                    None
                }
            })
            .collect(),
        constraints: vec![],
        param_decls: fun_def
            .param_decls
            .iter()
            .map(|param_decl| ParamDecl {
                ident: param_decl.ident.clone(),
                ty: Some(
                    param_decl
                        .ty
                        .as_ref()
                        .unwrap()
                        .subst_idents_kinded(cons_generics.iter(), cons_generic_args.iter()),
                ),
                mutbl: param_decl.mutbl,
            })
            .collect(),
        ret_dty: fun_def
            .ret_dty
            .subst_idents_kinded(cons_generics.iter(), cons_generic_args.iter()),
        exec: fun_def.exec,
        prv_rels: fun_def.prv_rels.clone(),
        body_expr: {
            let mut body = fun_def.body_expr.clone();
            body.subst_kinded_idents(HashMap::from_iter(
                cons_generics
                    .iter()
                    .zip(cons_generic_args.iter())
                    .map(|(generic, generic_arg)| (&*generic.ident.name, generic_arg)),
            ));
            body
        },
    }
}

/// Copy all default implementations from the trait which are not overridden by this impl to the impl
fn add_inherited_fun_defs(impl_def: &mut ImplDef, trait_defs: &Vec<TraitDef>) {
    if let Some(trait_ty) = &impl_def.trait_impl {
        let trait_def = trait_defs
            .iter()
            .find(|trait_def| trait_def.name == trait_ty.name)
            .expect(&format!(
                "Did not find trait \"{}\" in global context",
                trait_ty.name
            ));

        trait_def.ass_items.iter().for_each(|decl| match decl {
            AssociatedItem::FunDef(fun_def) => {
                if impl_def
                    .ass_items
                    .iter()
                    .find(|ass_item| match ass_item {
                        AssociatedItem::FunDef(fun_def_impl) => fun_def_impl.name == fun_def.name,
                        AssociatedItem::FunDecl(_) => {
                            panic!("ImplDef should not contain fun_decls")
                        }
                        AssociatedItem::ConstItem(_, _, _) => false,
                    })
                    .is_none()
                {
                    impl_def
                        .ass_items
                        .push(AssociatedItem::FunDef(trait_fun_to_impl_fun(
                            fun_def, impl_def, trait_def,
                        )));
                }
            }
            AssociatedItem::FunDecl(_) => (),
            AssociatedItem::ConstItem(_, _, _) => unimplemented!("TODO"),
        });
    }
}

/// Create a global function for every method in the impl
fn impl_to_global_funs(impl_def: &ImplDef) -> impl Iterator<Item = (FunctionName, FunDef)> + '_ {
    impl_def
        .ass_items
        .iter()
        .filter_map(|ass_item| match ass_item {
            AssociatedItem::FunDef(fun_def) => Some((
                FunctionName::from_impl(&fun_def.name, impl_def),
                polymorhpise_fun(fun_def, &impl_def.generic_params, &impl_def.constraints),
            )),
            AssociatedItem::FunDecl(_) => panic!("impls should not conatain fun_decls"),
            AssociatedItem::ConstItem(_, _, _) => unimplemented!("TODO"),
        })
}

/// Create a global function for every function declaration and every function definition in the trait
fn trait_to_global_funs(trait_def: &TraitDef) -> impl Iterator<Item = (FunctionName, FunDef)> + '_ {
    //Using a function instead of a let-statement avoids lifetime problems
    fn self_and_trait_generics(trait_def: &TraitDef) -> Vec<IdentKinded> {
        std::iter::once(IdentKinded::new(&Ident::new("Self"), Kind::DataTy))
            .chain(trait_def.generic_params.clone())
            .collect()
    }

    trait_def
        .ass_items
        .iter()
        .filter_map(|ass_item| match ass_item {
            AssociatedItem::FunDef(fun_def) => Some((
                FunctionName::from_trait(&fun_def.name, trait_def),
                polymorhpise_fun(
                    fun_def,
                    &self_and_trait_generics(trait_def),
                    &trait_def.constraints,
                ),
            )),
            // Create for every function declaration a function with empty body
            AssociatedItem::FunDecl(fun_decl) => Some((
                FunctionName::from_trait(&fun_decl.name, trait_def),
                polymorhpise_fun(
                    &FunDef {
                        name: fun_decl.name.clone(),
                        generic_params: fun_decl.generic_params.clone(),
                        constraints: fun_decl.constraints.clone(),
                        param_decls: vec![],
                        ret_dty: fun_decl.ret_dty.clone(),
                        exec: fun_decl.exec,
                        prv_rels: fun_decl.prv_rels.clone(),
                        body_expr: Expr::new(ExprKind::Seq(vec![])),
                    },
                    &self_and_trait_generics(trait_def),
                    &trait_def.constraints,
                ),
            )),
            AssociatedItem::ConstItem(_, _, _) => unimplemented!("TODO"),
        })
}

/// Create a new function definition with additional kinded identifier and constraints
fn polymorhpise_fun(
    fun_def: &FunDef,
    generics: &Vec<IdentKinded>,
    constraints: &Vec<Constraint>,
) -> FunDef {
    FunDef {
        name: fun_def.name.clone(),
        generic_params: generics
            .iter()
            .chain(fun_def.generic_params.iter())
            .map(|c| c.clone())
            .collect(),
        constraints: constraints
            .iter()
            .chain(fun_def.constraints.iter())
            .map(|c| c.clone())
            .collect(),
        param_decls: fun_def.param_decls.clone(),
        ret_dty: fun_def.ret_dty.clone(),
        exec: fun_def.exec,
        prv_rels: fun_def.prv_rels.clone(),
        body_expr: fun_def.body_expr.clone(),
    }
}

/// Create a new impl-method for a trait-function definition
fn trait_fun_to_impl_fun(fun_def: &FunDef, impl_def: &ImplDef, trait_def: &TraitDef) -> FunDef {
    assert!(impl_def.trait_impl.as_ref().unwrap().name == trait_def.name);

    // Substitute kinded identifier from the trait by arguments given in the impl
    let generics_subs: Vec<IdentKinded> =
        std::iter::once(IdentKinded::new(&Ident::new("Self"), Kind::DataTy))
            .chain(trait_def.generic_params.clone())
            .collect();
    let args_subs: Vec<ArgKinded> = std::iter::once(ArgKinded::DataTy(impl_def.dty.clone()))
        .chain(impl_def.trait_impl.as_ref().unwrap().generic_args.clone())
        .collect();

    FunDef {
        name: fun_def.name.clone(),
        generic_params: fun_def.generic_params.clone(),
        constraints: fun_def.constraints.clone(),
        param_decls: fun_def
            .param_decls
            .iter()
            .map(|param_decl| ParamDecl {
                ident: param_decl.ident.clone(),
                ty: Some(
                    param_decl
                        .ty
                        .as_ref()
                        .unwrap()
                        .clone()
                        .subst_idents_kinded(generics_subs.iter(), args_subs.iter()),
                ),
                mutbl: param_decl.mutbl,
            })
            .collect(),
        ret_dty: fun_def
            .ret_dty
            .subst_idents_kinded(generics_subs.iter(), args_subs.iter()),
        exec: fun_def.exec,
        prv_rels: fun_def.prv_rels.clone(),
        body_expr: {
            let mut body = fun_def.body_expr.clone();
            body.subst_kinded_idents(HashMap::from_iter(
                generics_subs
                    .iter()
                    .zip(args_subs.iter())
                    .map(|(generic, generic_arg)| (&*generic.ident.name, generic_arg)),
            ));
            body
        },
    }
}

/// NameGenerator to generate new unique names
struct NameGenerator {
    /// List of all generated names so far
    generated_names: HashSet<String>,
}

impl NameGenerator {
    /// List of all C++-Keywords which should be avoided as names
    const CPP_KEYWORDS: [&'static str; 101] = [
        "alignas",
        "alignof",
        "and",
        "and_eq",
        "asm",
        "atomic_cancel",
        "atomic_commit",
        "atomic_noexcept",
        "auto",
        "bitand",
        "bitor",
        "bool",
        "break",
        "case",
        "catch",
        "char",
        "char8_t",
        "char16_t",
        "char32_t",
        "class",
        "compl",
        "concept",
        "const",
        "consteval",
        "constexpr",
        "constinit",
        "const_cast",
        "continue",
        "co_await",
        "co_return",
        "co_yield",
        "decltype",
        "default",
        "delete",
        "do",
        "double",
        "dynamic_cast",
        "else",
        "enum",
        "explicit",
        "export",
        "extern",
        "false",
        "final",
        "float",
        "for",
        "friend",
        "goto",
        "if",
        "import",
        "inline",
        "int",
        "long",
        "module",
        "mutable",
        "namespace",
        "new",
        "noexcept",
        "not",
        "not_eq",
        "nullptr",
        "operator",
        "or",
        "or_eq",
        "override",
        "private",
        "protected",
        "public",
        "reflexpr",
        "register",
        "reinterpret_cast",
        "requires",
        "return",
        "short",
        "signed",
        "sizeof",
        "static",
        "static_assert",
        "static_cast",
        "struct",
        "switch",
        "synchronized",
        "template",
        "this",
        "thread_local",
        "throw",
        "true",
        "try",
        "typedef",
        "typeid",
        "typename",
        "union",
        "unsigned",
        "using",
        "virtual",
        "void",
        "volatile",
        "wchar_t",
        "while",
        "xor",
        "xor_eq",
    ];

    pub fn new() -> Self {
        NameGenerator {
            generated_names: HashSet::from_iter(
                NameGenerator::CPP_KEYWORDS
                    .iter()
                    .map(|str| String::from(*str)),
            ),
        }
    }

    /// Generate a new uniq function name
    /// * `function_name` - FunctionName of the function for which the name is generated
    /// * `arg_kinded` - vector of kinded arguments for the constraint kinded identifiers
    /// if this is monomorphised function
    pub fn generate_name(
        &mut self,
        function_name: &FunctionName,
        arg_kinded: Option<&Vec<ArgKinded>>,
    ) -> String {
        // original name of the function
        let name = &function_name.name;
        // generate a string from for the ArgKinded if exists
        let arg_kinded = match arg_kinded {
            Some(args) => Some(args.iter().fold(String::new(), |res, arg| {
                format!("{}_{}", res, NameGenerator::arg_kinded_to_string(arg))
            })),
            None => None,
        };
        match &function_name.fun_kind {
            FunctionKind::GlobalFun => {
                if let Some(arg_kinded) = arg_kinded {
                    self.generate_name_internal(&format!("{}_{}", name, arg_kinded))
                } else {
                    self.generate_name_internal(name)
                }
            }
            FunctionKind::ImplFun(impl_dty_scheme, _) => {
                let ty = NameGenerator::ty_to_string(&impl_dty_scheme.mono_ty);
                if let Some(arg_kinded) = arg_kinded {
                    self.generate_name_internal(&format!("{}__{}__{}", ty, arg_kinded, name))
                } else {
                    self.generate_name_internal(&format!("{}__{}", ty, name))
                }
            }
            FunctionKind::TraitFun(trait_name) => {
                // Trait functions are eliminated by the Monomorphiser anyway
                self.generate_name_internal(&format!("_TRAIT_FUN_{}_{}", trait_name, name))
            }
        }
    }

    /// Returns the name if a function with the same name wasnt generated before.
    /// Else a counter is incremented and appended to the name until a name is reached
    /// which is not generated before
    fn generate_name_internal(&mut self, name: &String) -> String {
        let res =
            // Is this name generated before?
            if self.generated_names.get(name).is_none() {
                name.clone()
            }
            // Else append a counter to the function-name
            else {
                let mut counter = 2;
                let mut result = format!("{}_{}", name, counter);
                while self.generated_names.get(&result).is_some() {
                    counter += 1;
                    result = format!("{}_{}", name, counter)
                }
                result
            };
        // Do not generated the same name again
        self.generated_names.insert(res.clone());
        res
    }

    /// Transform a ArgKinded to a string, so it can be used in a function name
    fn arg_kinded_to_string(arg: &ArgKinded) -> String {
        match arg {
            ArgKinded::Ident(_) => panic!("There should be no idents without kinds"),
            ArgKinded::Nat(nat) => format!("{}", nat),
            ArgKinded::Memory(mem) => format!("{}", mem),
            ArgKinded::Ty(ty) => NameGenerator::ty_to_string(ty),
            ArgKinded::DataTy(dty) => NameGenerator::dty_to_string(dty),
            ArgKinded::Provenance(prov) => format!("{}", prov),
        }
    }

    fn ty_to_string(ty: &Ty) -> String {
        match &ty.ty {
            TyKind::Data(dty) => NameGenerator::dty_to_string(dty),
            TyKind::Fn(_, _, _) => unimplemented!("needed?"),
            TyKind::Ident(_) => unimplemented!("needed?"),
            TyKind::Dead(_) => panic!("This should not contain dead types"),
        }
    }

    fn dty_to_string(dty: &DataTy) -> String {
        match &dty.dty {
            DataTyKind::Ident(i) => format!("{}", i.name),
            DataTyKind::Scalar(s) => String::from(match s {
                ScalarTy::Bool => "bool",
                ScalarTy::Unit => "Unit",
                ScalarTy::I32 => "i32",
                ScalarTy::U32 => "u32",
                ScalarTy::F32 => "f32",
                ScalarTy::F64 => "f64",
                ScalarTy::Gpu => "gpu",
            }),
            DataTyKind::Atomic(s) => format!(
                "Atomic_{}_",
                NameGenerator::dty_to_string(&DataTy::new(DataTyKind::Scalar(s.clone())))
            ),
            DataTyKind::Array(dty, nat) => {
                format!("Array_{}_{}_", NameGenerator::dty_to_string(dty), nat)
            }
            DataTyKind::ArrayShape(dty, nat) => {
                format!("ArrayShape_{}_{}_", NameGenerator::dty_to_string(dty), nat)
            }
            DataTyKind::Tuple(dtys) => format!(
                "{}_",
                dtys.iter().fold(String::from("Tuple"), |res, dty| format!(
                    "{}_{}",
                    res,
                    NameGenerator::dty_to_string(dty)
                ))
            ),
            DataTyKind::Struct(sdty) => {
                if sdty.generic_args.len() > 0 {
                    format!(
                        "{}{}_",
                        sdty.name,
                        sdty.generic_args
                            .iter()
                            .fold(String::new(), |res, arg| format!(
                                "{}_{}",
                                res,
                                NameGenerator::arg_kinded_to_string(arg)
                            ))
                    )
                } else {
                    sdty.name.clone()
                }
            }
            DataTyKind::At(_, _) => todo!(),
            DataTyKind::Ref(_, _, _, dty) => format!("Ref_{}_", NameGenerator::dty_to_string(dty)),
            DataTyKind::ThreadHierchy(_) => todo!(),
            DataTyKind::SplitThreadHierchy(_, _) => todo!(),
            DataTyKind::RawPtr(dty) => format!("RawPtr_{}_", NameGenerator::dty_to_string(dty)),
            DataTyKind::Range => String::from("Range"),
            DataTyKind::Dead(_) => panic!("This should not contain dead types"),
        }
    }
}
