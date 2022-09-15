use crate::ast::{Constraint, DataTyKind, Ident, IdentKinded};

use crate::ast::SubstKindedIdents;
use crate::ty_check::unify::{ConstrainMap, Constrainable};
use crate::ty_check::utils::fresh_name;
use crate::ty_check::{pre_decl, unify};

use super::unify::substitute;

#[derive(Debug, Clone)]
pub struct ConstraintScheme {
    pub generics: Vec<IdentKinded>,
    pub implican: Vec<Constraint>,
    pub implied: Constraint,
}

#[derive(Debug)]
pub struct IdentConstraints {
    //List of pairs of names of implicit idents with a constraint of the implicit ident
    //which must be checked when the implicit ident is replaced by a concrete type
    ident_cons: Vec<(String, Constraint)>,
}

#[derive(Debug)]
pub struct ConstraintEnv {
    theta: Vec<ConstraintScheme>,
}

impl ConstraintScheme {
    pub fn new(implied: &Constraint) -> Self {
        ConstraintScheme {
            generics: vec![],
            implican: vec![],
            implied: implied.clone(),
        }
    }

    pub fn generic_param_fresh_implicit_names(&self) -> Self {
        //Create new fresh names for every generic param to avoid name clashes
        let new_generics = self
            .generics
            .iter()
            .map(|generic| {
                IdentKinded::new(
                    &Ident::new_impli(&fresh_name(&generic.ident.name)),
                    generic.kind,
                )
            })
            .collect::<Vec<_>>();
        let new_generic_args = new_generics
            .iter()
            .map(|gen| gen.arg_kinded())
            .collect::<Vec<_>>();

        ConstraintScheme {
            generics: new_generics,
            implican: self
                .implican
                .iter()
                .map(|con| con.subst_idents_kinded(self.generics.iter(), new_generic_args.iter()))
                .collect(),
            implied: self
                .implied
                .subst_idents_kinded(self.generics.iter(), new_generic_args.iter()),
        }
    }
}

impl PartialEq for ConstraintScheme {
    fn eq(&self, other: &Self) -> bool {
        if self.generics.len() != other.generics.len()
            || self.implican.len() != other.implican.len()
        {
            return false;
        }

        //Substitute names of "other" with names of
        let generic_args = self
            .generics
            .iter()
            .map(|generic| generic.arg_kinded())
            .collect::<Vec<_>>();

        self.implican
            .iter()
            .zip(other.implican.iter())
            .chain(std::iter::once(&self.implied).zip(std::iter::once(&other.implied)))
            .fold(true, |res, (con1, con2)| {
                res && *con1 == con2.subst_idents_kinded(other.generics.iter(), generic_args.iter())
            })
    }
}

impl IdentConstraints {
    pub fn new() -> Self {
        Self {
            ident_cons: Vec::new(),
        }
    }

    pub fn add_ident_constraints<I>(&mut self, ident_constraints: I)
    where
        I: Iterator<Item = (String, Constraint)>,
    {
        self.ident_cons.extend(ident_constraints)
    }

    pub fn consume_constraints(&mut self, ident: &str) -> impl Iterator<Item = Constraint> + '_ {
        let index_ident_constraints = self
            .ident_cons
            .iter_mut()
            .partition_in_place(|(name, _)| *name != *ident);
        self.ident_cons
            .drain(index_ident_constraints..)
            .map(|(_, con)| con)
    }

    pub fn is_empty(&self) -> bool {
        self.ident_cons.is_empty()
    }

    pub fn into_iter(self) -> impl Iterator<Item = (String, Constraint)> {
        self.ident_cons.into_iter()
    }
}

impl ConstraintEnv {
    pub fn new() -> Self {
        Self { theta: Vec::new() }
    }

    pub fn append_constraint_scheme(&mut self, con: &ConstraintScheme) {
        self.theta.push(con.generic_param_fresh_implicit_names());
    }

    pub fn append_constraint_schemes(&mut self, cons: &Vec<ConstraintScheme>) {
        self.theta.extend(
            cons.iter()
                .map(|con| con.generic_param_fresh_implicit_names()),
        );
    }

    pub fn append_constraints(&mut self, cons: &Vec<Constraint>) {
        self.theta
            .extend(cons.iter().map(|con| ConstraintScheme::new(con)));
    }

    pub fn remove_constraints(&mut self, cons: &Vec<Constraint>) {
        cons.iter().for_each(|con_remove| {
            let con_remove = ConstraintScheme::new(con_remove);
            self.theta.swap_remove(
                (self.theta.len() - 1)
                    - self
                        .theta
                        .iter()
                        .rev()
                        .position(|con| *con == con_remove)
                        .unwrap(),
            );
        });
    }

    pub fn remove_constraint_schemes(&mut self, cons: &Vec<ConstraintScheme>) {
        cons.iter().for_each(|con_remove| {
            self.theta.swap_remove(
                (self.theta.len() - 1)
                    - self
                        .theta
                        .iter()
                        .rev()
                        .position(|con| *con == *con_remove)
                        .unwrap(),
            );
        });
    }

    pub(crate) fn check_constraint(
        &self,
        //Goal which should be proved
        constraint: &Constraint,
        //List of constraints for implicit idents which are necessary to prove the goal
        implicit_ident_cons: &mut IdentConstraints,
    ) -> Result<ConstrainMap, ()> {
        //For the simple case that the param of "constraint" is an implicit identifier
        if let DataTyKind::Ident(ident) = &constraint.param.dty {
            if ident.is_implicit {
                //Remember this constraint and assume its fulfilled
                //The constraint is checked when the identifier is replaced by a concrete type
                implicit_ident_cons
                    .ident_cons
                    .push((ident.name.clone(), constraint.clone()));
                return Ok(ConstrainMap::new());
            }
        }

        //A struct for backtracking
        struct Backtrack {
            //the last goal that was tried to prove
            current_goal: Constraint,
            //the number of goals at the moment
            //this is used to restore the state of the goals-list
            current_number_of_goals: usize,
            //the index of the constraint_scheme in theta that was tried to use to prove the goal
            current_index: usize,
            //the length of implicit_ident_constraints
            implicit_ident_cons_len: usize,
            //state of passed constraint with applied substitutions
            constraint: Constraint,
        }

        //Save the length of implicit ident constraints
        let implicit_ident_cons_len = implicit_ident_cons.ident_cons.len();

        //Mutable clone of constraint which is used to apply substitutions
        //which are made to prove the constraint
        let mut constraint_mut = constraint.clone();

        //For the unify::constrain-method
        let mut constr_map = ConstrainMap::new();
        let mut prv_rels = Vec::new();

        //List with all constraints which are tried to prove
        let mut goals: Vec<Constraint> = Vec::new();
        //List of backtrack-objects for backtracking
        let mut backtracks: Vec<Backtrack> = Vec::new();
        //Index to run over all type_schemes in theta
        let mut index = 0;

        let copy_trait = pre_decl::copy_trait();

        //Start with passed constraint as first goal
        goals.push(constraint.clone());
        //Prove all goals
        while !goals.is_empty() {
            //Try to prove goal
            let goal = {
                //Take the next goal from list of goals which must be checked
                let mut goal = goals.pop().unwrap();

                //if the goal is to prove if a tuple is "Copy": check if every dty in tuple is "Copy"
                while goal.trait_bound == copy_trait {
                    if let DataTyKind::Tuple(dtys) = goal.param.dty {
                        if dtys.len() == 0 {
                            panic!("Found a tuple with zero length!")
                        }

                        goals.extend(dtys.into_iter().map(|dty| Constraint {
                            param: dty,
                            trait_bound: copy_trait.clone(),
                        }));
                        goal = goals.pop().unwrap()
                    } else {
                        break;
                    }
                }

                goal
            };


            //is this a constraint for an implicit identifier?
            let constrait_param_ident = if let DataTyKind::Ident(ident) = &goal.param.dty {
                if ident.is_implicit {
                    Some(ident.name.clone())
                } else {
                    None
                }
            } else {
                None
            };

            //if this a constraint for an implicit identifier
            if let Some(ident_name) = constrait_param_ident {
                //Remember this constraint and assume its fulfilled
                //The constraint is checked when the identifier is replaced by a concrete type
                implicit_ident_cons.ident_cons.push((ident_name, goal));
            }
            //Else try to prove the goal
            else {
                //For every constraint in theta
                while index < self.theta.len() {
                    //This is a constraint_scheme which may proves the goal
                    let current_con = &self.theta[index];

                    constr_map.clear();
                    prv_rels.clear();

                    //Can implied from "current_con" and current goal be unified?
                    if goal
                        .constrain(&current_con.implied, &mut constr_map, &mut prv_rels)
                        .is_ok()
                    {
                        //The constraint_scheme has some preconditions which must be checked
                        if !current_con.implican.is_empty() {
                            //Push all constraints which implies the current implied constraint to list of goals which must be proved
                            goals.extend(current_con.implican.iter().map(|con| {
                                let mut goal = con.clone();
                                //Apply substitution which unifies implied from "current_con" and "goal"
                                substitute(&constr_map, &mut goal);
                                goal
                            }));

                            //Make sure there are no cycles
                            //There is a cyle exactly when a new goal (from list of constraints which implies
                            //implied from "current_con") is in backtrack-list
                            let cycle = backtracks.iter().fold(false, |res, backtrack| {
                                goals[goals.len() - current_con.implican.len()..]
                                    .iter()
                                    .fold(res, |res, goal| res || backtrack.current_goal == *goal)
                            });

                            //if this is a cycle remove new added goal from goals list
                            //and try to find another constraint-scheme which prove "goal"
                            if cycle {
                                goals.truncate(goals.len() - current_con.implican.len());

                                index = index + 1;
                            }
                            //Else save backtrack-entry and continue to check goals-list
                            else {
                                //Save current status to be able to restore it later
                                backtracks.push(Backtrack {
                                    current_goal: goal.clone(),
                                    current_number_of_goals: goals.len()
                                        - current_con.implican.len(),
                                    current_index: index,
                                    implicit_ident_cons_len: implicit_ident_cons.ident_cons.len(),
                                    constraint: constraint_mut.clone(),
                                });

                                //Apply substitution which unifies implied from "current_con" and "goal"
                                constraint_mut.substitute(&constr_map);

                                index = 0;
                                break;
                            }
                        } else {
                            //Sucessfully proved a subgoal with a fact
                            if !backtracks.is_empty() {
                                let last_backtrack = backtracks.last().unwrap();
                                if goals.len() <= last_backtrack.current_number_of_goals {
                                    backtracks.pop();
                                }
                            }

                            //Apply substitution which unifies implied from "current_con" and "goal"
                            constraint_mut.substitute(&constr_map);

                            index = 0;
                            break;
                        }
                    }
                    //Else implied from "current_con" and current goal can not be unified
                    //Try the next constraint_scheme in theta
                    else {
                        index = index + 1;
                    }
                }
            } //End try to prove goal

            //all "implied"-parts of all constraint_schemes in theta were tried to unify
            //with "goal", but nothing works => goal can not be proved
            if index >= self.theta.len() {
                //try to backtrack
                if !backtracks.is_empty() {
                    let backtrack = backtracks.pop().unwrap();
                    //Restore the state before trying to prove this unprovable goal
                    goals.truncate(backtrack.current_number_of_goals);
                    goals.push(backtrack.current_goal);
                    index = backtrack.current_index + 1;
                    implicit_ident_cons
                        .ident_cons
                        .truncate(backtrack.implicit_ident_cons_len);
                    constraint_mut = backtrack.constraint;
                }
                //no more possibilities for backtracking -> proving the constrain failed
                else {
                    //Restore state of "implicit_ident_cons"
                    implicit_ident_cons
                        .ident_cons
                        .truncate(implicit_ident_cons_len);

                    return Err(());
                }
            }
        }

        //Sucessfull computation
        let (const_map, _) = unify::constrain(constraint, &constraint_mut)
        .expect("This can not happen because \"constraint_mut\" is just a substituted version of \"constraint\"");
        Ok(const_map)
    }
}
