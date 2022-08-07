use core::panic;
use std::{collections::HashMap, vec};

use crate::{ast::{*, visit_mut::{VisitMut, walk_expr}, visit::{Visit}}, ty_check::unify::{constrain, Constrainable}};

pub fn monomorphise_constraint_generics(items: &mut Vec<Item>) -> (Vec<StructDef>, Vec<FunDef>) {
    Monomorphiser::monomorphise(items)
}

struct Monomorphiser<'a> {
    items: &'a Vec<Item>,
    funs: HashMap<FunctionName, FunDef>,
    mono_fun_defs: Vec<FunDef>,
    mono_funs: HashMap<FunctionName, Vec<usize>>,
    constraint_generics_in_scope: Vec<IdentKinded>
}

impl<'a> Monomorphiser<'a> {
    pub fn monomorphise(items: &mut Vec<Item>) -> (Vec<StructDef>, Vec<FunDef>) {
        items.iter_mut().for_each(|item|
            match item {
                Item::ImplDef(impl_def) => {
                    add_inherited_fun_defs(&mut impl_def, &items);
                },
                _ => (),
            }
        );
        let funs = 
            items.iter().fold(HashMap::new(), |funs, item| {
                match item {
                    Item::ImplDef(impl_def) => 
                    funs.extend(impl_to_global_funs(impl_def)),
                    Item::FunDef(fun_def) => {
                        funs.insert(FunctionName::global_fun(&fun_def.name), fun_def.clone());
                    },
                    _ => (),
                };
                funs
            });
        let mut monomorphiser = Monomorphiser {
            items,
            funs,
            mono_fun_defs: Vec::with_capacity(funs.len() * 4),
            mono_funs: HashMap::from_iter(
                funs.keys().map(|name|
                    (name.clone(), Vec::with_capacity(8))
                )),
            constraint_generics_in_scope: vec![],
        };

        monomorphiser.funs.values_mut().for_each(|fun_def| {
            monomorphiser.constraint_generics_in_scope =
                fun_def.generic_params.iter()
                .filter_map(|generic|
                    if fun_def.constraints.iter()
                        .find(|con|
                            if let DataTyKind::Ident(ident) = &con.param.dty {
                                ident.name == generic.ident.name
                            } else {
                                false
                            }
                        ).is_some() {
                        Some(generic.clone())
                    } else {
                        None
                    }
                ).collect();
            monomorphiser.visit_fun_def(fun_def)
        });
        monomorphiser.constraint_generics_in_scope = vec![];
        let mut counter = 0;
        while counter < monomorphiser.mono_fun_defs.len() {
            monomorphiser.visit_fun_def(&mut monomorphiser.mono_fun_defs[counter]);
            counter += 1;
        }

        (items.into_iter().filter_map(|item|
            match item {
                Item::StructDef(struct_def) => Some(*struct_def),
                _ => None
            }
        ).collect(),
        monomorphiser.funs.into_iter().fold(
            Vec::<FunDef>::with_capacity(monomorphiser.mono_fun_defs.len()), 
            |funs, (fun_name, fun_def)| {
                let mono_funs = monomorphiser.mono_funs.get(&fun_name).unwrap();
                if mono_funs.len() > 0 {
                    funs.extend(
                        mono_funs.iter().map(|fun_index|
                            monomorphiser.mono_fun_defs[*fun_index]
                        )
                    );
                } else {
                    //TODO change name of fun_def
                    funs.push(fun_def);
                }
                funs
        }))
    }

    fn monomorphise_fun_app(&mut self, path: &Path, fun_kind: &mut Option<FunctionKind>, fun: &mut Box<Expr>,
        generic_args: &mut Vec<ArgKinded>) {
        let (mut fun_name, fun_def) = {
            let fun_name = match fun.expr {
                ExprKind::PlaceExpr(place_expr) =>
                    if let PlaceExprKind::Ident(ident) = place_expr.pl_expr {
                        ident.name
                    } else {
                        panic!("Dont know how to get function name")
                    },
                _ => panic!("Dont know how to get function name"),
            };
            let fun_name = FunctionName { name: fun_name.clone(), fun_kind: fun_kind.unwrap() };
            (fun_name.clone(),
            self.funs.get(&fun_name).unwrap())
        };

        //if the lengths are different: This is a call of a already monomorphised function
        if fun_def.generic_params.len() != generic_args.len() {
            return;
        }

        //if the called function has no constraints there is nothing to do
        if fun_def.constraints.len() == 0 {
            return;
        }

        let (con_generics, con_generic_args): (Vec<&IdentKinded>, Vec<&ArgKinded>) =
            fun_def.generic_params.iter()
            .zip(generic_args.iter())
            .filter(|(gen, gen_arg)|{
                assert!(gen.kind == gen_arg.kind());
                fun_def.constraints.iter()
                .find(|con|
                    if let DataTyKind::Ident(ident) = &con.param.dty {
                        ident.name == gen.ident.name
                    } else {
                        false
                    }
                ).is_some()
        }).unzip();

        if !contains_dty_identifier(&con_generic_args, &self.constraint_generics_in_scope) {
            if let FunctionKind::TraitFun(trait_name) = fun_kind.unwrap() {
                self.replace_trait_fun_app(path, &mut fun_name, fun_kind, generic_args);
            }

            //TODO change name to avoid name conflicts
            let mut mono_fun = monomorphise_fun(fun_def, &con_generics, &con_generic_args);
            self.monomorphise_fun_call(fun_kind, generic_args, &fun_def.generic_params, &con_generics);
            if (*self.mono_funs.get(&fun_name).unwrap()).into_iter().find(|fun_index|
                    self.mono_fun_defs[*fun_index] == mono_fun).is_none() {
                self.mono_fun_defs.push(mono_fun.clone());
                self.mono_funs.get_mut(&fun_name).unwrap().push(self.mono_fun_defs.len() - 1);
            }
        }
    }

    fn replace_trait_fun_app(&mut self, path: &Path, fun_name: &mut FunctionName,
        fun_kind: &mut Option<FunctionKind>, generic_args: &mut Vec<ArgKinded>) {
        let trait_def =
            if let FunctionKind::TraitFun(name) = fun_kind.unwrap() {
                if let Some(Item::TraitDef(trait_def)) = self.items.iter().find(|item|
                    match item {
                        Item::TraitDef(trait_def) => trait_def.name == name,
                        _ => false
                    }
                ) {
                    trait_def
                } else {
                    panic!("did not found a trait-item with name: {}", name)
                }
            } else {
                panic!("trait_fun_call with non TraitFun-Kind!")
            };
        let impl_dty =
            match path {
                Path::DataTy(dty) => dty,
                Path::InferFromFirstArg => panic!("this should be replaced while type_checking"),
                Path::Empty => panic!("found a trait_fun_call without a path"),
        };
        let (impl_def, dty_unfication) =
            if let Err((impl_def, dty_unfication)) =
                self.items.iter().try_fold((), |res, item|
                    match item {
                        Item::ImplDef(impl_def) if impl_def.trait_impl.is_some() => {
                            let trait_mono = impl_def.trait_impl.unwrap();
                            if trait_mono.name == trait_def.name {
                                let mut impl_dty = impl_dty.clone();
                                let mut impl_dty_canidate = impl_def.dty.clone();
                                if let Ok((dty_unfication, _)) = constrain(&mut impl_dty_canidate, &mut impl_dty) {
                                    Err((impl_def, dty_unfication))
                                } else {
                                    Ok(())
                                }
                            } else {
                                Ok(())
                            }
                        },
                        _ => Ok(())
                    }
                ) {
                (impl_def, dty_unfication)
            } else {
                panic!("could not find implementation of trait {} for dty {:#?}", trait_def.name, impl_dty);
        };
        
        let trait_mono_args = &generic_args[0..trait_def.generic_params.len()];
        let fun_generic_args = &generic_args[trait_def.generic_params.len()+1..];
        //Infer generic_args of impl from impl_dty and trait_mono_args
        let mut impl_trait_mono =
            TraitMonoType {
                name: impl_def.trait_impl.unwrap().name.clone(),
                generics: impl_def.trait_impl.unwrap().generics.iter().map(|gen_arg| {
                    let mut gen_arg = gen_arg.clone();
                    gen_arg.substitute(&dty_unfication);
                    gen_arg
                }).collect()
            };
        let mut trait_mono =
            TraitMonoType {
                name: trait_def.name,
                generics: Vec::from(trait_mono_args.clone())
            };
        let dty_unfication2 = 
            if let Ok((dty_unfication, _)) = constrain(&mut impl_trait_mono, &mut trait_mono) {
                dty_unfication
            } else {
                panic!("Cannot unify trait_mono with trait_mono_ty of impl")
            };
        let impl_generics_args = impl_def.generic_params.iter().map(|generic| {
            let mut arg = generic.arg_kinded();
            arg.substitute(&dty_unfication);
            arg.substitute(&dty_unfication2);
            assert!(arg != generic.arg_kinded()); //All generic_args are inferrable!
            arg
        }).collect::<Vec<ArgKinded>>();

        *fun_kind = Some(FunctionName::from_impl(&fun_name.name, impl_def).fun_kind);
        fun_name.fun_kind = fun_kind.unwrap().clone();
        *generic_args =
            impl_generics_args.into_iter().chain(
                (*fun_generic_args).into_iter().map(|g| *g)
            ).collect();
    }

    fn monomorphise_fun_call(&mut self, fun_kind: &mut Option<FunctionKind>, generic_args: &mut Vec<ArgKinded>,
        fun_generics: &Vec<IdentKinded>, constraint_generics: &Vec<&IdentKinded>) {
        *generic_args = 
            fun_generics.iter()
            .zip(generic_args)
            .filter_map(|(generic, generic_arg)|
                if constraint_generics.iter()
                    .find(|con_generic|
                        con_generic.ident.name == generic.ident.name).is_none() {
                    Some(generic_arg.clone())
                } else {
                    None
                }
            ).collect();
        *fun_kind = Some(FunctionKind::GlobalFun)
    }
}

impl<'a> VisitMut for Monomorphiser<'a> {
    fn visit_expr(&mut self, expr: &mut Expr) {
        match &mut expr.expr {
            ExprKind::App(path, fun_kind, fun, generic_args, _) =>
                self.monomorphise_fun_app(path, fun_kind, fun, generic_args),
            ExprKind::DepApp(_, _) => panic!("Does this happen? What to do now?"),
            _ => walk_expr(self, expr)
        }
    }
}

//Copy all default implementations from implemented trait to this impl
fn add_inherited_fun_defs(impl_def: &mut ImplDef, comp_unit: &[Item]) {
    if let Some(trait_ty) = &impl_def.trait_impl {
        let trait_def =
            match
                comp_unit.iter().find(|item_def|
                    if let Item::TraitDef(trait_def) = item_def {
                        trait_def.name == trait_ty.name
                    } else {
                        false
                    }
                ).unwrap() {
            Item::TraitDef(trait_def) => trait_def,
            _ => panic!("This cannot happen"),
        };

        trait_def.decls.iter().for_each(|decl|
            match decl {
                AssociatedItem::FunDef(fun_def) =>
                    if impl_def.decls.iter().find(|ass_item|
                        match ass_item {
                            AssociatedItem::FunDef(fun_def_impl) =>
                                fun_def_impl.name == fun_def.name,
                            AssociatedItem::FunDecl(_) =>
                                panic!("ImplDef should not contain fun_decls"),
                            AssociatedItem::ConstItem(_, _, _) =>
                                false    
                        }
                        ).is_none() {
                        impl_def.decls.push(AssociatedItem::FunDef(
                            trait_fun_to_impl_fun(fun_def, impl_def, trait_def)));
                    },
                AssociatedItem::FunDecl(_) => (),
                AssociatedItem::ConstItem(_, _, _) => unimplemented!("TODO"),
            }
        );
    }
}

//Create a new FunDef without constraint generics. The constraint generics inside the function are subsituted by the passed ArgKinded
fn monomorphise_fun(fun_def: &FunDef, generics: &Vec<&IdentKinded>, generic_args: &Vec<&ArgKinded>) -> FunDef {
    FunDef {
        name: fun_def.name.clone(),
        generic_params:
            fun_def.generic_params.iter().filter_map(|generic|
                if generics.iter().find(|cons_generic|
                    cons_generic.ident.name == generic.ident.name
                    ).is_none() {
                    Some(generic.clone())
                } else {
                    None
                }
            ).collect(),
        constraints: vec![],
        param_decls: fun_def.param_decls.iter().map(|param_decl|
            ParamDecl{
                ident: param_decl.ident.clone(),
                ty: Some(param_decl.ty.unwrap()
                    .subst_idents_kinded((*generics).into_iter(), (*generic_args).into_iter())),
                mutbl: param_decl.mutbl,
            }).collect(),
        ret_dty: fun_def.ret_dty
            .subst_idents_kinded((*generics).into_iter(), (*generic_args).into_iter()),
        exec: fun_def.exec,
        prv_rels: fun_def.prv_rels.clone(),
        body_expr: {
            let mut body = fun_def.body_expr.clone();
            body.subst_kinded_idents(HashMap::from_iter(
                generics.iter()
                .zip(generic_args.iter())
                .map(|(generic, generic_arg)|
                    (&*generic.ident.name, *generic_arg)
             )));
            body
        }
    }
}

//Create multiple global functions from an impl
fn impl_to_global_funs(impl_def: &ImplDef) -> impl Iterator<Item = (FunctionName, FunDef)> + '_ {
    impl_def.decls.iter().filter_map(|ass_item|
        match ass_item {
            AssociatedItem::FunDef(fun_def) => {
                let mut fun_def = fun_def.clone();
                fun_def.generic_params =
                    impl_def.generic_params.clone().into_iter()
                    .chain(fun_def.generic_params.into_iter())
                    .collect();
                fun_def.constraints = 
                    impl_def.constraints.clone().into_iter()
                    .chain(fun_def.constraints.into_iter())
                    .collect();   
                Some((FunctionName::from_impl(&fun_def.name, impl_def), fun_def))
            },
            AssociatedItem::FunDecl(_) => panic!("impls should not conatain fun_decls"),
            AssociatedItem::ConstItem(_, _, _) => unimplemented!("TODO"),
        }
    )
}

//Create a new fun for an impl from a fun_def in a trait
fn trait_fun_to_impl_fun(fun_def: &FunDef, impl_def: &ImplDef, trait_def: &TraitDef) -> FunDef {
    assert!(impl_def.trait_impl.unwrap().name == trait_def.name);

    let generics_subs: Vec<IdentKinded> =
        std::iter::once(IdentKinded::new(&Ident::new("Self"), Kind::DataTy))
        .chain(trait_def.generic_params.clone())
        .collect();
    let args_subs: Vec<ArgKinded> = 
        std::iter::once(ArgKinded::DataTy(impl_def.dty))
        .chain(impl_def.trait_impl.unwrap().generics.clone())
        .collect();    

    FunDef {
        name: fun_def.name.clone(),
        generic_params: fun_def.generic_params.clone(),
        constraints: fun_def.constraints.clone(),
        param_decls: fun_def.param_decls.iter().map(|param_decl|
            ParamDecl {
                ident: param_decl.ident.clone(),
                ty: Some(param_decl.ty.unwrap()
                    .subst_idents_kinded(generics_subs.iter(), args_subs.iter())),
                mutbl: param_decl.mutbl,
            }).collect(),
        ret_dty: fun_def.ret_dty
            .subst_idents_kinded(generics_subs.iter(), args_subs.iter()),
        exec: fun_def.exec,
        prv_rels: fun_def.prv_rels.clone(),
        body_expr: {
            let mut body = fun_def.body_expr.clone();
            body.subst_kinded_idents(HashMap::from_iter(
                generics_subs.iter()
                .zip(args_subs.iter())
                .map(|(generic, generic_arg)|
                    (&*generic.ident.name, generic_arg)
             )));
            body
        }
    }
}

//Does the generic_args contains some dty-identifer of the passed identifier list
fn contains_dty_identifier(generics_args: &Vec<&ArgKinded>, identifier: &Vec<IdentKinded>) -> bool {
    struct ContainsIdentifier<'a> {
        result: bool,
        identifier: &'a Vec<IdentKinded>
    }

    impl<'a> Visit for ContainsIdentifier<'a> {
        fn visit_ident(&mut self, ident: &Ident) {
            if !self.result {
                self.result = self.identifier.iter().find(|gen|
                    gen.ident.name == ident.name
                ).is_some()
            }
        }

        fn visit_arg_kinded(&mut self, arg_kinded: &ArgKinded) {
            match arg_kinded {
                ArgKinded::DataTy(dty) => self.visit_dty(dty),
                _ => (),
            }
        }
    }

    let contains_identifier = ContainsIdentifier {
        result: false,
        identifier
    };
    generics_args.iter().fold(contains_identifier, |mut res: ContainsIdentifier, gen| {
        if !res.result {
            res.visit_arg_kinded(gen);
        }
        res
    }).result
}
