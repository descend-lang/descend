use super::error::TyError;
use super::TyResult;
use crate::ast::SubstKindedIdents;
use crate::ast::{Constraint, DataTyKind, Ident, IdentKinded};
use crate::ty_check::unify::{ConstrainMap, Constrainable};
use crate::ty_check::utils::fresh_name;
use crate::ty_check::{pre_decl, unify};
use std::collections::HashSet;

#[derive(Debug, Clone)]
pub struct ConstraintScheme {
    pub generics: Vec<IdentKinded>,
    pub implican: Vec<Constraint>,
    pub implied: Constraint,
}

/// Used to collect constraint on implicit identifiers which cannot checked until the
/// identifier is replaced by a concrete type
#[derive(Debug, Clone)]
pub struct IdentConstraints {
    /// Vector of pairs consisting of a name of an implicit identifier
    /// and a constraint on this identifier
    ident_cons: Vec<(String, Constraint)>,
}

/// Environment with all constraint-schemes
#[derive(Debug)]
pub struct ConstraintEnv {
    constraint_schemes: Vec<ConstraintScheme>,
}

impl ConstraintScheme {
    pub fn new(implied: &Constraint) -> Self {
        ConstraintScheme {
            generics: vec![],
            implican: vec![],
            implied: implied.clone(),
        }
    }

    /// Create a new ConstraintScheme where all kinded identifiers are replaced by
    /// new fresh identifiers
    pub fn generic_param_fresh_implicit_names(&self) -> Self {
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

impl Eq for ConstraintScheme {}
impl PartialEq for ConstraintScheme {
    fn eq(&self, other: &Self) -> bool {
        if self.generics.len() != other.generics.len()
            || self.implican.len() != other.implican.len()
        {
            return false;
        }

        // Substitute names of kinded identifiers of "other" with names of kinded identifiers of "self"
        // and check if every constraint is identical
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

    /// Add constraints on identifiers to this context
    pub fn add_ident_constraints<I>(&mut self, ident_constraints: I)
    where
        I: Iterator<Item = (String, Constraint)>,
    {
        self.ident_cons.extend(ident_constraints)
    }

    /// Returns and removes all constraints on the identifier with passed name
    pub fn consume_constraints(
        &mut self,
        ident: &str,
    ) -> impl ExactSizeIterator<Item = Constraint> + '_ {
        let index_ident_constraints = self
            .ident_cons
            .iter_mut()
            .partition_in_place(|(name, _)| *name != *ident);
        self.ident_cons
            .drain(index_ident_constraints..)
            .map(|(_, con)| con)
    }

    /// Returns true if this context is empty
    pub fn is_empty(&self) -> bool {
        self.ident_cons.is_empty()
    }

    /// Check if a substitution respect all constraints on identifiers in `self`. <br>
    /// For every substitution of an implicit identifier are all constraints on this identifier checked.
    /// This can also infer new substitutions and constraints on identifiers. <br>
    /// Returns a TyResult with a pair of a substitution extended with all types that are inferred while
    /// checking this substitution and the modified list of constraints on identifiers without checked
    /// constraints
    pub(crate) fn constraint_subs(
        &self,
        constraint_env: &ConstraintEnv,
        subs: &ConstrainMap,
    ) -> TyResult<(ConstrainMap, Self)> {
        // Result substitution with all substitutions of inferred types
        let mut res_subs: ConstrainMap = ConstrainMap::new();
        res_subs.composition(subs.clone());
        // Result list of constraints on identifiers
        let mut res_ident_constraints = self.clone();

        let mut subs = subs.clone();

        loop {
            let mut subs_new = ConstrainMap::new();

            // Check if this substitution fulfills all implicit_ident_constraints
            for (name, dty) in subs.dty_unifier {
                // Check if all constraints on the implicit identifier which is substituted are fulfilled

                // Using a HashSet removes duplicates
                let constraints_to_check: HashSet<_> =
                    res_ident_constraints.consume_constraints(&name).collect();

                // if the substituted type is an implicit ident: add constraints of this ident to other ident
                if let DataTyKind::Ident(ident) = dty.dty {
                    if ident.is_implicit {
                        res_ident_constraints.add_ident_constraints(
                            constraints_to_check
                                .into_iter()
                                .map(|con| (ident.name.clone(), con)),
                        );
                        continue;
                    }
                }

                // Check every constraint
                for mut con in &mut constraints_to_check.into_iter() {
                    // Substitute inferred types
                    con.substitute(&res_subs);

                    // Check if constraint is fulfilled
                    if let Ok(constr_map) =
                        constraint_env.check_constraint(&con, &mut res_ident_constraints)
                    {
                        if !constr_map.is_empty() {
                            subs_new.composition(constr_map);
                        }
                    } else {
                        Err(TyError::UnfulfilledConstraint(con.clone()))?
                    }
                }
            }

            // If no new substitutions found: break loop
            if subs_new.is_empty() {
                break;
            }
            // Else check if new substitutions are valid
            else {
                // Add new substitutions to result substitutions
                res_subs.composition(subs_new.clone());

                // Check all new substitutions
                subs = subs_new;
            }
        }

        // Apply substitution to all constraints on implicit idents
        res_ident_constraints
            .ident_cons
            .iter_mut()
            .for_each(|(_, con)| {
                con.substitute(&res_subs);
            });

        return Ok((res_subs, res_ident_constraints));
    }
}

impl ConstraintEnv {
    pub fn new() -> Self {
        Self {
            constraint_schemes: Vec::new(),
        }
    }

    /// Append a constraint-scheme to this environment
    pub fn append_constraint_scheme(&mut self, con: &ConstraintScheme) {
        self.constraint_schemes
            .push(con.generic_param_fresh_implicit_names());
    }

    /// Append multiple constraint-schemes to this environment
    pub fn append_constraint_schemes(&mut self, cons: &Vec<ConstraintScheme>) {
        self.constraint_schemes.extend(
            cons.iter()
                .map(|con| con.generic_param_fresh_implicit_names()),
        );
    }

    /// Append a constraint (which is transformed into a constraint-scheme without
    /// kinded identifier and without constraints) to this environment
    pub fn append_constraints(&mut self, cons: &Vec<Constraint>) {
        self.constraint_schemes
            .extend(cons.iter().map(|con| ConstraintScheme::new(con)));
    }

    /// Remove multiple constraints from this environment
    pub fn remove_constraints(&mut self, cons: &Vec<Constraint>) {
        cons.iter().for_each(|con_remove| {
            let con_remove = ConstraintScheme::new(con_remove);
            self.constraint_schemes.swap_remove(
                (self.constraint_schemes.len() - 1)
                    - self
                        .constraint_schemes
                        .iter()
                        .rev()
                        .position(|con| *con == con_remove)
                        .unwrap(),
            );
        });
    }

    /// Remove multiple constraint-schemes from this environment
    pub fn remove_constraint_schemes(&mut self, cons: &Vec<ConstraintScheme>) {
        cons.iter().for_each(|con_remove| {
            self.constraint_schemes.swap_remove(
                (self.constraint_schemes.len() - 1)
                    - self
                        .constraint_schemes
                        .iter()
                        .rev()
                        .position(|con| *con == *con_remove)
                        .unwrap(),
            );
        });
    }

    /// Check if a constraint if fulfilled. <br>
    /// Returns a substitution with inferred types if the constraint is fulfilled.
    /// `implicit_ident_cons` stays unchanged when the constraint is not fulfilled.
    /// * `constraint` - goal which should be proved
    /// * `implicit_ident_cons` - list of constraints on implicit identifiers which
    /// must be respected by all substitutions. This list is extended by all constraints
    /// on implicit identifiers which must be fulfilled to prove this goal
    pub(crate) fn check_constraint(
        &self,
        constraint: &Constraint,
        implicit_ident_cons: &mut IdentConstraints,
    ) -> Result<ConstrainMap, ()> {
        // For the simple case that the param of "constraint" is an implicit identifier
        if let DataTyKind::Ident(ident) = &constraint.param.dty {
            if ident.is_implicit {
                // Remember this constraint and assume its fulfilled
                // The constraint is checked when the identifier is replaced by a concrete type
                implicit_ident_cons
                    .ident_cons
                    .push((ident.name.clone(), constraint.clone()));
                return Ok(ConstrainMap::new());
            }
        }

        /// A struct for backtracking
        struct Backtrack {
            /// the current goal that was tried to prove
            current_goal: Constraint,
            /// the number of goals at the moment <br>
            /// this is used to restore the state of the goals-list
            current_number_of_goals: usize,
            /// the index of the constraint_scheme in theta that was tried to use to prove the goal
            current_index: usize,
            /// implicit_ident_constraints
            implicit_ident_cons: IdentConstraints,
            /// substitution with inferred types
            inferred_types: ConstrainMap,
        }

        // Save implicit ident constraints
        let implicit_ident_cons_clone = implicit_ident_cons.clone();
        // Check the copy trait is a special case
        let copy_trait = pre_decl::copy_trait();

        // For the unify::constrain-method
        let mut constr_map = ConstrainMap::new();
        let mut prv_rels = Vec::new();

        // List with all constraints which must be proved
        let mut goals: Vec<Constraint> = Vec::new();
        // List of backtrack-objects for backtracking
        let mut backtracks: Vec<Backtrack> = Vec::new();
        // Index to run over all type_schemes in theta
        let mut index = 0;
        // Substitutions of inferred types while proving goals
        let mut inferred_types = ConstrainMap::new();

        // Vector used to reduce number of fresh-name substitutions
        // applied_cscheme[i] == true iff the ith constraint-scheme needs new fresh names
        let mut applied_cscheme = vec![false; self.constraint_schemes.len()];

        // Start with passed constraint as first goal
        goals.push(constraint.clone());
        // Prove all goals
        while !goals.is_empty() {
            // Try to prove goal
            let goal = {
                // Take the next goal from list of goals which must be checked
                let mut goal = goals.pop().unwrap();

                // if the goal is to prove if a tuple is "Copy": check if every dty in tuple is "Copy"
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

                // Apply substitution with inferred types
                if !inferred_types.is_empty() {
                    goal.substitute(&inferred_types);
                }

                goal
            };

            // is this a constraint for an implicit identifier?
            let constrait_param_ident = if let DataTyKind::Ident(ident) = &goal.param.dty {
                if ident.is_implicit {
                    Some(ident.name.clone())
                } else {
                    None
                }
            } else {
                None
            };

            // if this a constraint for an implicit identifier
            if let Some(ident_name) = constrait_param_ident {
                // Remember this constraint and assume its fulfilled
                // The constraint is checked when the identifier is replaced by a concrete type
                implicit_ident_cons.ident_cons.push((ident_name, goal));

                // the last backtracking-entries can maybe be removed
                while !backtracks.is_empty()
                    && goals.len() <= backtracks.last().unwrap().current_number_of_goals
                {
                    backtracks.pop();
                }
            }
            // Else try to prove the goal
            else {
                // For every constraint-scheme in environment
                while index < self.constraint_schemes.len() {
                    // Only exists to prevent borrowing errors
                    let fresh_cscheme;
                    // This is a constraint_scheme which may proves the goal
                    let current_con = if !applied_cscheme[index] {
                        &self.constraint_schemes[index]
                    } else {
                        // Use fresh names to avoid name conflicts
                        fresh_cscheme =
                            self.constraint_schemes[index].generic_param_fresh_implicit_names();
                        &fresh_cscheme
                    };

                    constr_map.clear();
                    prv_rels.clear();

                    // Can implied from "current_con" and current goal be unified?
                    if goal
                        .constrain(&current_con.implied, &mut constr_map, &mut prv_rels)
                        .is_ok()
                    {
                        // Make sure the unification is allowed under context of constraints on implicit identifiers
                        let implicit_ident_cons_new;
                        match implicit_ident_cons.constraint_subs(self, &constr_map) {
                            Ok((constr_map_ext, implicit_ident_cons_ext)) => {
                                constr_map = constr_map_ext;
                                implicit_ident_cons_new = implicit_ident_cons_ext;
                            }
                            Err(_) => {
                                index = index + 1;
                                continue;
                            }
                        }

                        // Use fresh names if this constraint-scheme is used again to avoid name clashes
                        applied_cscheme[index] = true;

                        // Is a new goal pushed to "goals"-list?
                        let mut number_new_goals = 0;

                        // The constraint_scheme has some preconditions which must be checked
                        if !current_con.implican.is_empty() {
                            // Push all constraints which implies the current implied constraint to list of goals which must be proved
                            goals.extend(current_con.implican.iter().filter_map(|sub_goal| {
                                let mut sub_goal = sub_goal.clone();

                                // Substitute inferred types
                                sub_goal.substitute(&inferred_types);
                                sub_goal.substitute(&constr_map);

                                // If this goal is self-supporting, remove it
                                // This is the case iff the new goal is in backtrack-list included
                                // "goal == sub_goal" also indicate that there is a self-supporting-constraint
                                // If this is the case, this do not remove self-supporting-constraint in this iteration,
                                // but in the next iteration when this goal is on backtracking-stack
                                match backtracks.iter().find(|bt| bt.current_goal == sub_goal) {
                                    Some(_) => None,
                                    None => {
                                        number_new_goals = number_new_goals + 1;
                                        Some(sub_goal)
                                    }
                                }
                            }));
                        }

                        // if there are new goals pushed on goals-list, create a new backtracking-entry
                        if number_new_goals != 0 {
                            // Save current status to be able to restore it later
                            backtracks.push(Backtrack {
                                current_goal: goal.clone(),
                                current_number_of_goals: goals.len() - number_new_goals,
                                current_index: index,
                                implicit_ident_cons: implicit_ident_cons.clone(),
                                inferred_types: inferred_types.clone(),
                            });
                        }
                        // else this goal is proved by a fact and the last backtracking entries can maybe be removed
                        else {
                            while !backtracks.is_empty()
                                && goals.len() <= backtracks.last().unwrap().current_number_of_goals
                            {
                                backtracks.pop();
                            }
                        }

                        // Add substitution to inferred types
                        if !constr_map.is_empty() {
                            inferred_types.composition(constr_map);
                            constr_map = ConstrainMap::new();
                        }

                        *implicit_ident_cons = implicit_ident_cons_new;
                        index = 0;
                        break;
                    }
                    // Else implied from "current_con" and current goal can not be unified
                    // Try the next constraint_scheme in the environment
                    else {
                        index = index + 1;
                    }
                }
            } // End try to prove goal

            // all "implied"-parts of all constraint_schemes in environment were tried to unify
            // with "goal", but nothing works => goal can not be proved
            if index >= self.constraint_schemes.len() {
                // try to backtrack
                if !backtracks.is_empty() {
                    let Backtrack {
                        current_goal,
                        current_number_of_goals,
                        current_index,
                        implicit_ident_cons: b_implicit_ident_cons,
                        inferred_types: b_inferred_types,
                    } = backtracks.pop().unwrap();
                    // Restore the state before trying to prove this unprovable goal
                    goals.truncate(current_number_of_goals);
                    goals.push(current_goal);
                    index = current_index + 1;
                    *implicit_ident_cons = b_implicit_ident_cons;
                    inferred_types = b_inferred_types;
                }
                // no more possibilities for backtracking -> proving the constrain failed
                else {
                    // Restore state of "implicit_ident_cons"
                    *implicit_ident_cons = implicit_ident_cons_clone;

                    return Err(());
                }
            }
        }

        // Successful computation

        // Remove unnecessary constraint from "inferred_types"-substitution
        if !inferred_types.is_empty() {
            let mut c_inferred = constraint.clone();
            c_inferred.substitute(&inferred_types);
            (inferred_types, _) =
                unify::constrain(constraint, &c_inferred).expect("This can not happen");
        }

        Ok(inferred_types)
    }
}
