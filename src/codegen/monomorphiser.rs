use core::panic;
use std::{
    collections::{hash_map::RandomState, HashMap, HashSet},
    vec,
};

use crate::{
    ast::{
        visit_mut::{walk_expr, VisitMut},
        *,
    },
    ty_check::unify::{constrain, Constrainable},
};

//Monomorphise functions
//Convert all non-struct items to global functions and monomorphise all constraint generic parameters.
//The global functions will have new unique non-C++-keywords names.
//Input: Well typed items (structs, traits, global functions, impls)
//Output:
//  -unchanged list of all structs
//  -global functions which have no constraint generic parameters anymore
pub fn monomorphise_constraint_generics(mut items: Vec<Item>) -> (Vec<StructDef>, Vec<FunDef>) {
    //Copy all trait_defs to prevent borrowing errors in next statement
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

    //Monomorphise global functions, traits, impls to multiple global functions
    let fun_defs = Monomorphiser::monomorphise(&items);
    //Collect struct defs
    let struct_defs = items
        .into_iter()
        .filter_map(|item| {
            if let Item::StructDef(struct_def) = item {
                Some(struct_def)
            } else {
                None
            }
        })
        .collect::<Vec<StructDef>>();
    (struct_defs, fun_defs)
}

struct Monomorphiser<'a> {
    //Refence to items (to search impls or traits)
    items: &'a Vec<Item>,
    //List of all global- and impl functions
    //The "String"-value describes the new unique global function-name of the function
    funs: Vec<(FunctionName, FunDef, String)>,
    //Map of all new generated functions (which can be identified by their
    //Functionname and their ArgKindeds for the constraint generic params)
    //and their new unique global function-name
    generated: HashMap<(FunctionName, Vec<ArgKinded>), String>,
    //List of new generated functions which must be still visited
    generated_funs: Vec<(FunctionName, FunDef)>,
    //NameGenerator to generate unique names which prevents name conflicts
    name_generator: NameGenerator,
}

impl<'a> Monomorphiser<'a> {
    pub fn monomorphise(items: &Vec<Item>) -> Vec<FunDef> {
        //Create a vector of all functions including global functions, functions in impls and trait functions
        let mut funs = items
            .iter()
            .fold(
                (Vec::new(), NameGenerator::new()),
                |(mut funs, mut name_generator), item| {
                    match item {
                        Item::ImplDef(impl_def) => {
                            funs.extend(impl_to_global_funs(impl_def).map(|(fun_name, fun_def)| {
                                (
                                    fun_name.clone(),
                                    fun_def,
                                    name_generator.generate_name(&fun_name),
                                )
                            }))
                        }
                        Item::FunDef(fun_def) => {
                            let fun_name = FunctionName::global_fun(&fun_def.name);
                            funs.push((
                                fun_name.clone(),
                                fun_def.clone(),
                                name_generator.generate_name(&fun_name),
                            ));
                        }
                        Item::TraitDef(trait_def) => funs.extend(
                            trait_to_global_funs(trait_def).map(|(fun_name, fun_def)| {
                                (
                                    fun_name.clone(),
                                    fun_def,
                                    name_generator.generate_name(&fun_name),
                                )
                            }),
                        ),
                        Item::StructDef(_) => (),
                    };
                    (funs, name_generator)
                },
            )
            .0;
        //List of all new generated monomorphised functions
        let mut mono_funs: HashMap<FunctionName, Vec<FunDef>, RandomState> = HashMap::new();
        //Monomorphiser to visit all function applications
        let mut monomorphiser = Monomorphiser {
            items: items,
            funs: funs.clone(),
            generated: HashMap::new(),
            generated_funs: Vec::with_capacity(funs.len() * 4),
            name_generator: NameGenerator::new(),
        };

        //Vist orginal functions to monomorphise function calls
        funs.iter_mut().for_each(|(_, fun_def, _)| {
            //Visit only functions without constraint generic params
            if fun_def.generic_params.iter().fold(true, |res, gen| {
                res && fun_def
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
        //And visit all new generated monomorphised functions
        while !monomorphiser.generated_funs.is_empty() {
            let (fun_name, mut mono_fun) = monomorphiser.generated_funs.pop().unwrap();
            let mono_funs_with_name = match mono_funs.get_mut(&fun_name) {
                Some(mono_funs) => mono_funs,
                None => {
                    let mono_funs_with_name = Vec::with_capacity(8);
                    mono_funs.insert(fun_name.clone(), mono_funs_with_name);
                    mono_funs.get_mut(&fun_name).unwrap()
                }
            };
            //Visit this function to monomorphise function calls
            monomorphiser.visit_fun_def(&mut mono_fun);
            //And insert it in list of generated monomorphised function
            mono_funs_with_name.push(mono_fun);
        }

        //Create a result vector of all monomorphised functions and all orginal functions which didnt need to be monomorphised
        //Keep the orginal order of functions
        funs.into_iter().fold(
            Vec::<FunDef>::new(), |mut funs, (fun_name, mut fun_def, global_fun_name)| {
                match fun_name.fun_kind {
                    FunctionKind::GlobalFun |
                    FunctionKind::ImplFun(_, _) =>
                        match mono_funs.remove(&fun_name) {
                            //If there are multiple monomorphised functions of the original function
                            Some(mut mono_funs) => {
                                //Sort them by name
                                mono_funs.sort_by(|a, b| a.name.partial_cmp(&b.name).unwrap());
                                //And insert them into result list
                                funs.extend(
                                    mono_funs.into_iter().map(|fun|
                                        fun
                                    )
                                );
                            },
                            //The orginal functions was not monomorphised
                            None => {
                                let fun_generics = &fun_def.generic_params;

                                //Because the orginal functions is never called but has constraint generics
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
                                    eprintln!("function {} \"{}\" is never used. Because this function has constraint \
                                        generic params, which needs to be monomoprhised, no code can be generated \
                                        for this function.",
                                        match fun_name.fun_kind {
                                            FunctionKind::GlobalFun => "global_fun",
                                            FunctionKind::TraitFun(_) => "trait_fun",
                                            FunctionKind::ImplFun(_, _) => "impl_fun"
                                        }, fun_name.name)
                                }
                                //Because the orginal functions didnt need to be monomorphised
                                else {
                                    fun_def.name = global_fun_name;
                                    funs.push(fun_def);
                                }
                            }
                        }
                    //Ignore trait_functions
                    FunctionKind::TraitFun(_) => (),
                }
            funs
        })
    }

    fn monomorphise_fun_app(
        &mut self,
        fun_kind: &mut Option<FunctionKind>,
        fun: &mut Box<Expr>,
        generic_args: &mut Vec<ArgKinded>,
    ) {
        //Function to set the name of a function within an funtcion application
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

        //Find name, reference to FunDef and the unique global function name of this application
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
            let (_, fun_def, global_fun_name) =
                match self.funs.iter().find(|(name, _, _)| *name == fun_name) {
                    Some(res) => res,
                    //If we dont find function definition of this function this must
                    //be a predeclared function (because this program is well typed)
                    None => return,
                };
            (fun_name, fun_def, global_fun_name)
        };

        //if the lengths are different: This is an already monomorphised function call
        if fun_def.generic_params.len() != generic_args.len() {
            assert!(fun_def.generic_params.len() > generic_args.len());
            return;
        }

        //if the called function is a trait function, replace it by the correct impl-function
        if let FunctionKind::TraitFun(_) = fun_kind.as_ref().unwrap() {
            self.replace_trait_fun_app(&mut fun_name, fun_kind, generic_args);
            //Refresh reference to FunDef and the unique global function name of this application
            match self.funs.iter().find(|(name, _, _)| *name == fun_name) {
                Some((_, new_fun_name, new_global_fun_name)) => {
                    fun_def = new_fun_name;
                    global_fun_name = new_global_fun_name;
                }
                None => panic!("did not find function {:#?}", fun_name),
            };
        }

        //if the called function has no constraints, it is sufficient to adjust the name of the function
        //to refer the global function instead of e.g. an impl-function
        if fun_def.constraints.len() == 0 {
            set_gl_fun_name(fun, fun_kind, global_fun_name.clone());
            return;
        }

        let fun_generics = fun_def.generic_params.clone(); //Prevents borrowing errors
                                                           //Find now all generic params and corresponding generic arguments of
                                                           //this function call which are constraint
        let (con_generics, con_generic_args): (Vec<IdentKinded>, Vec<ArgKinded>) = fun_generics
            .iter()
            .zip(generic_args.iter())
            .filter_map(|(gen, gen_arg)| {
                assert!(gen.kind == gen_arg.kind());
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
                    Some((gen.clone(), gen_arg.clone()))
                } else {
                    None
                }
            })
            .unzip();

        //This key describes uniquely the monomorphised function
        let key_generated = (fun_name, con_generic_args);
        let new_fun_name =
            //Does a corresponding function definition already exists?
            if let Some(fun_name) = self.generated.get(&key_generated) {
                fun_name.clone()
            } else {
                //Create a new function definition for this specific function call
                let mut mono_fun = monomorphise_fun(&fun_def, &con_generics, &key_generated.1);
                let new_fun_name = self.name_generator.generate_name(&key_generated.0);
                mono_fun.name = new_fun_name.clone();
                //And insert it in corresponding lists
                self.generated_funs.push((key_generated.0.clone(), mono_fun));
                self.generated.insert(key_generated, new_fun_name.clone());
                new_fun_name
            };

        //Reduce the number of generic arguments of this function call to match the
        //required number of generic args of the monomorphised function
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
        //Adjust also function name
        set_gl_fun_name(fun, fun_kind, new_fun_name);
    }

    //Replace a trait-function application by the application of the correct impl-fun
    fn replace_trait_fun_app(
        &mut self,
        fun_name: &mut FunctionName,
        fun_kind: &mut Option<FunctionKind>,
        generic_args: &mut Vec<ArgKinded>,
    ) {
        //Find the trait-definition of trait-fun
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
        //The generic arg for "Self" which is the datatype of the impl
        let impl_dty = match generic_args.first().unwrap() {
            ArgKinded::DataTy(dty) => dty.clone(),
            _ => panic!("Found non-datatype ArgKinded as generic arg for Self"),
        };
        //Find the defintion of the impl which implements the trait
        //and remember the Substitutions which are necassary to unfiy
        //"impl_dty" with the datatype of the impl
        let (impl_def, dty_unfication) = if let Err((impl_def, dty_unfication)) =
            self.items.iter().try_fold((), |_, item| match item {
                Item::ImplDef(impl_def) if impl_def.trait_impl.is_some() => {
                    let trait_mono = impl_def.trait_impl.as_ref().unwrap();
                    if trait_mono.name == trait_def.name {
                        let mut impl_dty = impl_dty.clone();
                        let mut impl_dty_canidate = impl_def.dty.clone();
                        if let Ok((dty_unfication, _)) =
                            constrain(&mut impl_dty_canidate, &mut impl_dty)
                        {
                            Err((impl_def, dty_unfication))
                        } else {
                            Ok(())
                        }
                    } else {
                        Ok(())
                    }
                }
                _ => Ok(()),
            }) {
            (impl_def, dty_unfication)
        } else {
            panic!(
                "could not find implementation of trait {} for dty {:#?}",
                trait_def.name, impl_dty
            );
        };

        //The first generic arg is the arg for "Self"
        //The next args are the generic args for the generic params of the trait
        let trait_mono_args =
            Vec::from_iter(generic_args.drain(1..trait_def.generic_params.len() + 1));
        //And the rest are generic args for the generic params of the function itself
        let fun_generic_args = generic_args.drain(1..);
        //Infer generic args of impl from impl_dty and trait_mono_args
        //E.g. Infer "A,B,C" in "impl<A, B, C> Eq<A, B> for Point<B, C> ..."
        let mut impl_trait_mono = TraitMonoType {
            name: impl_def.trait_impl.as_ref().unwrap().name.clone(),
            generics: impl_def
                .trait_impl
                .as_ref()
                .unwrap()
                .generics
                .iter()
                .map(|gen_arg| {
                    let mut gen_arg = gen_arg.clone();
                    gen_arg.substitute(&dty_unfication);
                    gen_arg
                })
                .collect(),
        };
        let mut trait_mono = TraitMonoType {
            name: trait_def.name.clone(),
            generics: trait_mono_args,
        };
        let dty_unfication2 =
            if let Ok((dty_unfication, _)) = constrain(&mut impl_trait_mono, &mut trait_mono) {
                dty_unfication
            } else {
                panic!("Cannot unify trait_mono with trait_mono_ty of impl")
            };
        //Collect als inferred generic args
        let impl_generics_args = impl_def
            .generic_params
            .iter()
            .map(|generic| {
                let mut arg = generic.arg_kinded();
                arg.substitute(&dty_unfication);
                arg.substitute(&dty_unfication2);
                assert!(arg != generic.arg_kinded()); //All generic_args are inferrable!
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

//Visit-Implementation for Monomorphiser
//Visit all function applications and call "monomorphise_fun_app"
impl<'a> VisitMut for Monomorphiser<'a> {
    fn visit_expr(&mut self, expr: &mut Expr) {
        match &mut expr.expr {
            ExprKind::App(_, fun_kind, fun, generic_args, _) => {
                self.monomorphise_fun_app(fun_kind, fun, generic_args)
            }
            ExprKind::DepApp(_, _) => panic!("Does this happen? What to do now?"),
            _ => walk_expr(self, expr),
        }
    }
}

//Copy all default implementations from implemented trait to this impl
fn add_inherited_fun_defs(impl_def: &mut ImplDef, trait_defs: &Vec<TraitDef>) {
    if let Some(trait_ty) = &impl_def.trait_impl {
        let trait_def = trait_defs
            .iter()
            .find(|trait_def| trait_def.name == trait_ty.name)
            .unwrap();

        trait_def.decls.iter().for_each(|decl| match decl {
            AssociatedItem::FunDef(fun_def) => {
                if impl_def
                    .decls
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
                        .decls
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

//Create a new FunDef without constraint generics. The constraint generics inside the function are subsituted by the passed ArgKinded
fn monomorphise_fun(
    fun_def: &FunDef,
    generics: &Vec<IdentKinded>,
    generic_args: &Vec<ArgKinded>,
) -> FunDef {
    FunDef {
        name: fun_def.name.clone(),
        generic_params: fun_def
            .generic_params
            .iter()
            .filter_map(|generic| {
                if generics
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
                        .clone()
                        .subst_idents_kinded(generics.iter(), generic_args.iter()),
                ),
                mutbl: param_decl.mutbl,
            })
            .collect(),
        ret_dty: fun_def
            .ret_dty
            .subst_idents_kinded(generics.iter(), generic_args.iter()),
        exec: fun_def.exec,
        prv_rels: fun_def.prv_rels.clone(),
        body_expr: {
            let mut body = fun_def.body_expr.clone();
            body.subst_kinded_idents(HashMap::from_iter(
                generics
                    .iter()
                    .zip(generic_args.iter())
                    .map(|(generic, generic_arg)| (&*generic.ident.name, generic_arg)),
            ));
            body
        },
    }
}

//Create multiple global functions from an impl
fn impl_to_global_funs(impl_def: &ImplDef) -> impl Iterator<Item = (FunctionName, FunDef)> + '_ {
    impl_def.decls.iter().filter_map(|ass_item| match ass_item {
        AssociatedItem::FunDef(fun_def) => Some((
            FunctionName::from_impl(&fun_def.name, impl_def),
            polymorhpise_fun(fun_def, &impl_def.generic_params, &impl_def.constraints),
        )),
        AssociatedItem::FunDecl(_) => panic!("impls should not conatain fun_decls"),
        AssociatedItem::ConstItem(_, _, _) => unimplemented!("TODO"),
    })
}

//Create multiple global functions (with empty bodys) from an trait
fn trait_to_global_funs(trait_def: &TraitDef) -> impl Iterator<Item = (FunctionName, FunDef)> + '_ {
    fn self_chain_generics(trait_def: &TraitDef) -> Vec<IdentKinded> {
        std::iter::once(IdentKinded::new(&Ident::new("Self"), Kind::DataTy))
            .chain(trait_def.generic_params.clone())
            .collect()
    }

    trait_def
        .decls
        .iter()
        .filter_map(|ass_item| match ass_item {
            AssociatedItem::FunDef(fun_def) => Some((
                FunctionName::from_trait(&fun_def.name, trait_def),
                polymorhpise_fun(
                    fun_def,
                    &self_chain_generics(trait_def),
                    &trait_def.constraints,
                ),
            )),
            AssociatedItem::FunDecl(fun_decl) => Some((
                FunctionName::from_trait(&fun_decl.name, trait_def),
                FunDef {
                    name: fun_decl.name.clone(),
                    generic_params: self_chain_generics(trait_def)
                        .into_iter()
                        .chain(fun_decl.generic_params.clone().into_iter())
                        .collect(),
                    constraints: trait_def
                        .constraints
                        .clone()
                        .into_iter()
                        .chain(fun_decl.constraints.clone().into_iter())
                        .collect(),
                    param_decls: vec![],
                    ret_dty: fun_decl.ret_dty.clone(),
                    exec: fun_decl.exec,
                    prv_rels: fun_decl.prv_rels.clone(),
                    body_expr: Expr::new(ExprKind::Seq(vec![])),
                },
            )),
            AssociatedItem::ConstItem(_, _, _) => unimplemented!("TODO"),
        })
}

fn polymorhpise_fun(
    fun_def: &FunDef,
    generics: &Vec<IdentKinded>,
    constraints: &Vec<Constraint>,
) -> FunDef {
    FunDef {
        name: fun_def.name.clone(),
        generic_params: generics
            .clone()
            .into_iter()
            .chain(fun_def.generic_params.clone().into_iter())
            .collect(),
        constraints: constraints
            .clone()
            .into_iter()
            .chain(fun_def.constraints.clone().into_iter())
            .collect(),
        param_decls: fun_def.param_decls.clone(),
        ret_dty: fun_def.ret_dty.clone(),
        exec: fun_def.exec,
        prv_rels: fun_def.prv_rels.clone(),
        body_expr: fun_def.body_expr.clone(),
    }
}

//Create a new fun for an impl from a fun_def in a trait
fn trait_fun_to_impl_fun(fun_def: &FunDef, impl_def: &ImplDef, trait_def: &TraitDef) -> FunDef {
    assert!(impl_def.trait_impl.as_ref().unwrap().name == trait_def.name);

    let generics_subs: Vec<IdentKinded> =
        std::iter::once(IdentKinded::new(&Ident::new("Self"), Kind::DataTy))
            .chain(trait_def.generic_params.clone())
            .collect();
    let args_subs: Vec<ArgKinded> = std::iter::once(ArgKinded::DataTy(impl_def.dty.clone()))
        .chain(impl_def.trait_impl.as_ref().unwrap().generics.clone())
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

//NameGenerator to generate new unique names
struct NameGenerator {
    generated_names: HashSet<String>,
}

impl NameGenerator {
    //List of all C++-Keywords which should be avoided as names
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

    fn is_keyword(name: &str) -> bool {
        NameGenerator::CPP_KEYWORDS
            .iter()
            .find(|str| ***str == *name)
            .is_some()
    }

    pub fn new() -> Self {
        NameGenerator {
            generated_names: HashSet::from_iter(
                NameGenerator::CPP_KEYWORDS
                    .iter()
                    .map(|str| String::from(*str)),
            ),
        }
    }

    pub fn generate_name(&mut self, function_name: &FunctionName) -> String {
        let name = &function_name.name;
        if let FunctionKind::ImplFun(impl_dty_scheme, _) = &function_name.fun_kind {
            if let TyKind::Data(dty) = &impl_dty_scheme.mono_ty.ty {
                match &dty.dty {
                    //e.g. Point::function() or Point::_new()
                    DataTyKind::Struct(struct_dty) => self.generate_name_internal(&match (
                        NameGenerator::is_keyword(&struct_dty.name),
                        NameGenerator::is_keyword(name),
                    ) {
                        (true, true) => format!("_{}::_{}", struct_dty.name, name),
                        (true, false) => format!("_{}::{}", struct_dty.name, name),
                        (false, true) => format!("{}::_{}", struct_dty.name, name),
                        (false, false) => format!("{}::{}", struct_dty.name, name),
                    }),
                    _ => self.generate_name_internal(name),
                }
            } else {
                self.generate_name_internal(name)
            }
        } else {
            self.generate_name_internal(name)
        }
    }

    fn generate_name_internal(&mut self, name: &String) -> String {
        let res =
            //Can the orginal name still be used
            if self.generated_names.get(name).is_none() {
                name.clone()
            }
            //Else append a counter to the function-name
            else {
                let mut counter = 2;
                let mut result = format!("{}{}", name, counter);
                while self.generated_names.get(&result).is_some() {
                    counter += 1;
                    result = format!("{}{}", name, counter)
                }
                result
            };
        self.generated_names.insert(res.clone());
        res
    }
}
