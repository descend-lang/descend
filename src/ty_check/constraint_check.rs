use crate::ast::{Constraint, IdentKinded};

use crate::ty_check::unify::{ConstrainMap, Constrainable};

use super::unify::substitute;

#[derive(Debug, Clone, PartialEq)]
pub struct ConstraintScheme {
    pub generics: Vec<IdentKinded>,
    pub implican: Vec<Constraint>,
    pub implied: Constraint,
}

#[derive(Debug, Clone)]
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

    pub fn is_constraint(&self) -> bool {
        self.generics.len() == 0 && self.implican.len() == 0
    }
}

impl ConstraintEnv {
    pub fn new() -> Self {
        Self { theta: Vec::new() }
    }

    pub fn append_constraint_scheme(&mut self, con: &ConstraintScheme) {
        self.theta.push(con.clone());
    }

    pub fn append_constraint_schemes(&mut self, cons: &Vec<ConstraintScheme>) {
        self.theta.extend(cons.clone());
    }

    pub fn append_constraints(&mut self, cons: &Vec<Constraint>) {
        self.theta
            .extend(cons.iter().map(|con| ConstraintScheme::new(con)));
    }

    pub fn remove_constraints(&mut self, cons: &Vec<Constraint>) {
        cons.iter().for_each(|con_remove| {
            let con_remove = ConstraintScheme::new(con_remove);
            self.theta.swap_remove(
                self.theta
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
                self.theta
                    .iter()
                    .rev()
                    .position(|con| *con == *con_remove)
                    .unwrap(),
            );
        });
    }

    pub fn check_constraint(&self, goal: &Constraint) -> bool {
        struct Backtrack {
            current_goal: Constraint,
            current_number_of_goals: usize,
            current_index: usize,
        }

        let mut constr_map = ConstrainMap::new();
        let mut prv_rels = Vec::new();

        let mut goals: Vec<Constraint> = Vec::with_capacity(16);
        let mut backtracks: Vec<Backtrack> = Vec::with_capacity(8);
        let mut index = 0;

        //Start with passed constraint as first goal
        goals.push(goal.clone());
        //Prove all goals
        while !goals.is_empty() {
            //Try to prove goal
            let goal = goals.pop().unwrap();

            //Check for every constraint in theta
            while index < self.theta.len() {
                let current_con = &self.theta[index];

                let mut goal_clone = goal.clone();
                constr_map.clear();
                prv_rels.clear();

                //Can current from constraint-scheme implied constraint and current goal can be unified?
                if goal_clone
                    .constrain(
                        &mut current_con.implied.clone(),
                        &mut constr_map,
                        &mut prv_rels,
                    )
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
                                current_number_of_goals: goals.len() - current_con.implican.len(),
                                current_index: index,
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

            //if there are no constraint-schemes in theta which implies the current goal
            if index >= self.theta.len() {
                //try to backtrack
                if !backtracks.is_empty() {
                    let backtrack = backtracks.pop().unwrap();
                    goals.truncate(backtrack.current_number_of_goals);
                    goals.push(backtrack.current_goal);
                    index = backtrack.current_index + 1;
                }
                //no more possibilities for backtracking -> prooving the constrain failed
                else {
                    return false;
                }
            }
        }

        true
    }
}
