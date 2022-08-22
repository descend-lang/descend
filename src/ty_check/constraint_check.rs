use crate::ast::{Constraint, DataTyKind, IdentKinded};

use crate::ast::SubstKindedIdents;
use crate::ty_check::unify::{ConstrainMap, Constrainable};
use crate::ty_check::utils::fresh_name;

use super::unify::substitute;

#[derive(Debug)]
pub struct ConstraintEnv {
    theta: Vec<ConstraintScheme>,
    ident_constraints: Vec<(String, Constraint)>,
}

#[derive(Debug, Clone)]
pub struct ConstraintScheme {
    pub generics: Vec<IdentKinded>,
    pub implican: Vec<Constraint>,
    pub implied: Constraint,
}

impl ConstraintScheme {
    pub fn new(implied: &Constraint) -> Self {
        ConstraintScheme {
            generics: vec![],
            implican: vec![],
            implied: implied.clone(),
        }
    }

    pub fn fresh_generic_param_names(&self) -> Self {
        //Create new fresh names for every generic param to avoid name clashes
        let new_generics = self
            .generics
            .iter()
            .map(|generic| {
                let mut new_gen = generic.clone();
                new_gen.ident.name = fresh_name(&new_gen.ident.name);
                new_gen
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

impl ConstraintEnv {
    pub fn new() -> Self {
        Self {
            theta: Vec::new(),
            ident_constraints: Vec::new(),
        }
    }

    pub fn append_constraint_scheme(&mut self, con: &ConstraintScheme) {
        self.theta.push(con.fresh_generic_param_names());
    }

    pub fn append_constraint_schemes(&mut self, cons: &Vec<ConstraintScheme>) {
        self.theta
            .extend(cons.iter().map(|con| con.fresh_generic_param_names()));
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

    pub fn add_ident_constraints<I>(&mut self, ident_constraints: I)
    where
        I: Iterator<Item = (String, Constraint)>,
    {
        self.ident_constraints.extend(ident_constraints)
    }

    pub fn get_constraints<'a, 'b>(
        &'a self,
        ident: &'b str,
    ) -> impl Iterator<Item = &'a Constraint> + '_
    where
        'b: 'a,
    {
        self.ident_constraints
            .iter()
            .filter_map(|(name, constraint)| {
                if *name == *ident {
                    Some(constraint)
                } else {
                    None
                }
            })
    }

    pub fn remove_ident_constraint(&mut self, ident: &str) {
        self.ident_constraints.retain(|(name, _)| *name != *ident);
    }

    pub fn check_constraints<'a, I>(&self, goals: I) -> Result<Vec<(String, Constraint)>, ()>
    where
        I: Iterator<Item = &'a Constraint>,
    {
        //TODO there exists a more efficient way to do this
        goals.fold(Ok(vec![]), |res, constraint| {
            if let Ok(mut res_cons) = res {
                if let Ok(cons) = self.check_constraint(constraint) {
                    res_cons.extend(cons.into_iter());
                    Ok(res_cons)
                } else {
                    Err(())
                }
            } else {
                res
            }
        })
    }

    pub fn check_constraint(&self, goal: &Constraint) -> Result<Vec<(String, Constraint)>, ()> {
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
            implicit_ident_constraints_len: usize,
        }

        let mut constr_map = ConstrainMap::new();
        let mut prv_rels = Vec::new();

        //List with all constraints which are tried to prove
        let mut goals: Vec<Constraint> = Vec::new();
        //List of constraints for implicit idents which are necessary to prove the goal
        let mut implicit_ident_constraints: Vec<(String, Constraint)> = Vec::new();
        //List of backtrack-objects for backtracking
        let mut backtracks: Vec<Backtrack> = Vec::new();
        //Index to run over all type_schemes in theta
        let mut index = 0;

        //Start with passed constraint as first goal
        goals.push(goal.clone());
        //Prove all goals
        while !goals.is_empty() {
            //Try to prove goal
            let goal = goals.pop().unwrap();

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
                implicit_ident_constraints.push((ident_name, goal));
            }
            //Else try to prove the goal
            else {
                //For every constraint in theta
                while index < self.theta.len() {
                    let current_con = &self.theta[index];

                    constr_map.clear();
                    prv_rels.clear();

                    //Can implied from "current_con" and current goal be unified?
                    if goal
                        .constrain(&current_con.implied, &mut constr_map, &mut prv_rels)
                        .is_ok()
                    {
                        if !current_con.implican.is_empty() {
                            //Push all constraints which implies the current implied constraint to list of goals which must be prooved
                            goals.extend(current_con.implican.iter().map(|con| {
                                let mut goal = con.clone();
                                substitute(&constr_map, &mut goal);
                                goal
                            }));

                            //Make sure there are no cycles
                            let cycle = backtracks.iter().fold(false, |res, backtrack| {
                                goals[goals.len() - current_con.implican.len()..]
                                    .iter()
                                    .fold(res, |res, goal| res || backtrack.current_goal == *goal)
                            });

                            if cycle {
                                goals.truncate(goals.len() - current_con.implican.len());

                                index = index + 1;
                            } else {
                                //Save current status to be able to restore it later
                                backtracks.push(Backtrack {
                                    current_goal: goal.clone(),
                                    current_number_of_goals: goals.len()
                                        - current_con.implican.len(),
                                    current_index: index,
                                    implicit_ident_constraints_len: implicit_ident_constraints
                                        .len(),
                                });

                                index = 0;
                                break;
                            }
                        } else {
                            //Sucessfully prooved a subgoal with a fact
                            if !backtracks.is_empty() {
                                let last_backtrack = backtracks.last().unwrap();
                                if goals.len() <= last_backtrack.current_number_of_goals {
                                    backtracks.pop();
                                }
                            }

                            index = 0;
                            break;
                        }
                    } else {
                        index = index + 1;
                    }
                }
            }

            //if there are no constraint-schemes in theta which implies the current goal
            if index >= self.theta.len() {
                //try to backtrack
                if !backtracks.is_empty() {
                    let backtrack = backtracks.pop().unwrap();
                    goals.truncate(backtrack.current_number_of_goals);
                    goals.push(backtrack.current_goal);
                    index = backtrack.current_index + 1;
                    implicit_ident_constraints.truncate(backtrack.implicit_ident_constraints_len)
                }
                //no more possibilities for backtracking -> prooving the constrain failed
                else {
                    return Err(());
                }
            }
        }

        Ok(implicit_ident_constraints)
    }
}
