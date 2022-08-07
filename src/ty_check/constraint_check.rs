use crate::ast::{IdentKinded, Constraint};

use crate::ty_check::unify::{ConstrainMap, Constrainable};

use super::unify::substitute;

#[derive(Debug, Clone, PartialEq)]
pub struct ConstraintScheme {
    pub generics: Vec<IdentKinded>,
    pub implican: Vec<Constraint>,
    pub implied: Constraint
}

#[derive(Debug, Clone)]
pub struct ConstraintEnv {
    theta: Vec<ConstraintScheme>
}

impl ConstraintScheme {
    pub fn new(implied: &Constraint) -> Self {
        ConstraintScheme { generics: vec![], implican: vec![], implied: implied.clone() }
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
        self.theta.extend(cons.iter().map(|con| ConstraintScheme::new(con)));
    }

    pub fn remove_constraints(&mut self, cons: &Vec<Constraint>) {
        cons.iter().for_each(|con_remove| {
            let con_remove = ConstraintScheme::new(con_remove);
            self.theta
            .swap_remove(
                self.theta
                .iter()
                .rev()
                .position(|con|
                    *con == con_remove).unwrap()
                );
        });
    }

    pub fn remove_constraint_schemes(&mut self, cons: &Vec<ConstraintScheme>) {
        cons.iter().for_each(|con_remove| {
            self.theta
            .swap_remove(
                self.theta
                .iter()
                .rev()
                .position(|con|
                    *con == *con_remove).unwrap()
                );
        });
    }

    pub fn check_constraint(&self, goal: &Constraint) -> bool {
        let mut constr_map = ConstrainMap::new();
        let mut prv_rels = Vec::new();

        self.theta.iter().find(|con| {
            constr_map.clear();
            prv_rels.clear();
            
            let mut goal_clone = goal.clone();

            if goal_clone.constrain(&mut con.implied.clone(), &mut constr_map, &mut prv_rels).is_ok() {
                con.implican.iter().fold(true, |res, c| {
                    let mut goal = c.clone();
                    substitute(&constr_map, &mut goal);
                    res && self.check_constraint(&goal)
                })
            } else {
                false
            }
        }).is_some()
    }
}