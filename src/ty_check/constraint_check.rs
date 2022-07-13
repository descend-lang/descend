use crate::ast::{IdentKinded, WhereClauseItem, ArgKinded, SubstKindedIdents};

#[derive(Debug, Clone)]
pub struct ConstraintScheme {
    pub generics: Vec<IdentKinded>,
    pub implican: Vec<WhereClauseItem>,
    pub implied: WhereClauseItem
}

#[derive(Debug, Clone)]
pub struct ConstraintEnv {
    theta: Vec<ConstraintScheme>
}

impl ConstraintScheme {
    pub fn new(implied: &WhereClauseItem) -> Self {
        ConstraintScheme { generics: vec![], implican: vec![], implied: implied.clone() }
    }

    pub fn is_where_clause_item(&self) -> bool {
        self.generics.len() == 0 && self.implican.len() == 0
    }

    pub fn subst_ident_kinded(&mut self, ident_kinded: &IdentKinded, with: &ArgKinded) {
        if !self.generics.contains(ident_kinded) {
            self.implican.iter_mut().for_each(|wc| *wc = wc.subst_ident_kinded(ident_kinded, with))
        }
    }
}

impl ConstraintEnv {
    pub fn new() -> Self {
        Self { theta: Vec::new() }
    } 

    pub fn append_constraint(&mut self, con: &ConstraintScheme) {
        self.theta.push(con.clone());
    }

    pub fn append_constraints(&mut self, cons: &Vec<ConstraintScheme>) {
        self.theta.extend(cons.clone());
    }

    pub fn remove_constraints(&mut self, cons: &Vec<ConstraintScheme>) -> bool {
        unimplemented!("TODO");
    }

    pub fn check_predicate(&self, constraint: &WhereClauseItem) -> bool {
        unimplemented!("TODO");
    }
}