use log::debug;
use std::cmp;
#[cfg(debug_assertions)]
use std::collections::HashSet;
use std::mem;

use crate::assignment::{Assignment, VarInfo, VarValue};
use crate::clausedb::{ClauseDatabase, ClauseIndex, ClauseType};
#[cfg(debug_assertions)]
use crate::types::Sign;
use crate::types::{Clause, Literal, Model, Var};
use crate::util::LiteralMap;

pub struct Solver {
    clause_database: ClauseDatabase,
    watches: LiteralMap<Vec<ClauseIndex>>,
    assignment: Assignment,
    trail: Vec<Literal>,
    trail_lim: Vec<usize>,
    // Position of propagation queue in trail. Based on MiniSAT implementation.
    queue_head: usize,
}

impl Solver {
    pub fn new() -> Solver {
        Solver {
            clause_database: ClauseDatabase::new(),
            watches: LiteralMap::new(),
            assignment: Assignment::new(),
            trail: Vec::new(),
            trail_lim: Vec::new(),
            queue_head: 0,
        }
    }

    #[cfg(debug_assertions)]
    fn check_watches(&self) {
        let mut watches_expected = LiteralMap::new();
        for _ in 0..self.assignment.num_vars() {
            watches_expected.push(Vec::new(), Vec::new());
        }

        // Get the expected watch lists
        self.clause_database.expected_watches(&mut watches_expected);

        // Compare to see if there is a difference, ignoring ordering of clauses in the watch lists
        for i in 0..self.assignment.num_vars() {
            for &sign in &[Sign::Positive, Sign::Negative] {
                let lit = Literal { sign, var: Var(i) };

                let actual = &self.watches[lit];
                let expected = &watches_expected[lit];

                let actual: HashSet<_> = actual.iter().copied().collect();
                let expected: HashSet<_> = expected.iter().copied().collect();

                let diff: Vec<_> = actual.symmetric_difference(&expected).copied().collect();

                if diff.len() > 0 {
                    panic!("Watch list invariant violation for literal {}: Expected {:?}, Found {:?}, Diff {:?}",
                           lit, expected, actual, diff);
                }
            }
        }

        debug!("Successfully checked watches");
    }

    #[cfg(debug_assertions)]
    fn check_implied(&self) {
        for c in &self.clause_database.clauses {
            if c.is_implied(&self.assignment) {
                panic!("Found implied clause in user clauses");
            }
        }

        for c in &self.clause_database.clauses {
            if c.is_implied(&self.assignment) {
                panic!("Found implied clause in learned clauses");
            }
        }

        debug!("Successfully checked for implied clauses");
    }

    fn num_assigns(&self) -> usize {
        self.trail.len()
    }

    fn record(&mut self, clause: Clause) {
        // Perform unit propagation on the asserting literal
        let asserting_lit = clause.literals[0];
        let clause_idx = self.add_clause_internal(clause, ClauseType::Learned);

        if let Some(clause_idx) = clause_idx {
            debug!("Asserting literal for learned clause: {}", asserting_lit);
            self.assert_literal(asserting_lit, Some(clause_idx));
        }
    }

    fn analyze(&self, mut clause: ClauseIndex) -> (Clause, usize) {
        let mut seen = vec![false; self.assignment.num_vars()];
        let mut output_clause = Vec::new();
        let mut backtrack_level = 0;

        let mut counter = 0;
        let mut conflicting = true;

        let mut trail_rev = self.trail.iter().rev();

        loop {
            let reason = self
                .clause_database
                .get_clause(clause)
                .calc_reason(conflicting);

            for lit in reason {
                if !seen[lit.var.0] {
                    seen[lit.var.0] = true;

                    let var_level = self
                        .assignment
                        .var_level(lit.var)
                        .expect("unassigned literals cannot be part of a reason set");

                    if var_level == self.decision_level() {
                        // Simply count the number of reason literals that are on
                        // this decision level (without duplicates, since we keep
                        // track of whether we've seen variables already in the
                        // `seen` array). We will run into them as we progress along
                        // the trail backwards. By counting them, we can determine
                        // whether we've reached the first UIP.
                        counter += 1;
                    } else {
                        output_clause.push(lit.negate());
                        // We keep track of the decision level we need to
                        // backtrack to in order to make the UIP literal
                        // asserting. This is the highest decision level below
                        // the current decision level.
                        backtrack_level = cmp::max(backtrack_level, var_level);
                    }
                }
            }

            // We look for a literal that we've seen, because that means that it
            // was part of the (transitive) reason set somewhere. Other literals
            // are simply literals that have been set due to unit propagation,
            // but which have nothing to do with the conflict.
            let lit = loop {
                let lit = trail_rev.next().unwrap();
                assert_eq!(
                    self.assignment.var_level(lit.var).unwrap(),
                    self.decision_level()
                );

                if seen[lit.var.0] {
                    break lit;
                }
            };
            counter -= 1;

            if counter == 0 {
                // Found the first UIP!

                // Put the asserting literal at the end, and then swap it so it
                // ends up in position 0 (the unit propagation position)
                let asserting_idx = output_clause.len();
                output_clause.push(lit.negate());
                output_clause.swap(0, asserting_idx);
                break;
            }

            clause = self.assignment.var_reason(lit.var).unwrap();
            conflicting = false;
        }

        (Clause::new_unchecked(output_clause), backtrack_level)
    }

    fn assume(&mut self, lit: Literal) -> bool {
        self.trail_lim.push(self.trail.len());
        debug!("New decision level: {}", self.decision_level());
        self.assert_literal(lit, None)
    }

    fn undo_one(&mut self) {
        let last = self.trail.pop().unwrap();
        self.queue_head -= 1;

        self.assignment.assign(last.var, VarInfo::Unassigned);
    }

    fn cancel(&mut self) {
        let num_undo = self.trail.len() - self.trail_lim.pop().unwrap();

        for _ in 0..num_undo {
            self.undo_one();
        }
    }

    fn cancel_until(&mut self, decision_level: usize) {
        debug!("Backtracking to level {}", decision_level);
        while self.decision_level() > decision_level {
            self.cancel();
        }
    }

    fn decision_level(&self) -> usize {
        self.trail_lim.len()
    }

    // Asserts a literal
    // TODO: Maybe do not use boolean for error reporting
    fn assert_literal(&mut self, lit: Literal, reason: Option<ClauseIndex>) -> bool {
        match self.assignment.literal_value(lit) {
            VarValue::Unassigned => match lit.assignment() {
                (var, value) => {
                    debug!(
                        "Assignment: {} -> {} at level {} ({})",
                        var,
                        value,
                        self.decision_level(),
                        if let Some(idx) = reason {
                            format!("implied by {}", self.clause_database.get_clause(idx))
                        } else {
                            "decision".to_owned()
                        }
                    );
                    self.assignment.assign(
                        var,
                        VarInfo::Assigned {
                            value,
                            reason,
                            level: self.decision_level(),
                        },
                    );
                    self.trail.push(lit);
                    true
                }
            },
            // Conflicting assignment
            VarValue::False => false,
            // Already set
            VarValue::True => true,
        }
    }

    fn propagate(&mut self) -> Option<ClauseIndex> {
        // TODO: Avoid bounds check on self.trail
        while self.queue_head < self.trail.len() {
            let lit = self.trail[self.queue_head];

            // We empty out the watch list as we process it. Clauses are
            // responsible for re-adding themselves to the watch list if
            // necessary.
            let watches = mem::replace(&mut self.watches[lit], Vec::new());

            // TODO: Get rid of bounds checking
            for i in 0..watches.len() {
                let c_idx = watches[i];

                let (new_watch, maybe_prop) = self
                    .clause_database
                    .get_clause_mut(c_idx)
                    .watch_triggered(lit, &self.assignment);

                // Re-add this clause to the given watch list, since we removed
                // it from one.
                self.watches[new_watch].push(c_idx);

                // Perform unit propagation if necessary
                if let Some(prop) = maybe_prop {
                    if !self.assert_literal(prop, Some(c_idx)) {
                        // Copy back the remaining watches, so we ensure that no
                        // watch pointers are lost, even when backtracking/conflict
                        // occurs.
                        self.watches[lit].extend_from_slice(&watches[i + 1..]);

                        // Clear the queue
                        self.queue_head = self.trail.len();
                        debug!("Conflict! {}", self.clause_database.get_clause(c_idx));

                        return Some(c_idx);
                    }
                }
            }

            self.queue_head += 1;
        }

        None
    }

    pub fn new_var(&mut self) -> Var {
        let idx = self.assignment.num_vars();

        self.assignment.new_var();
        self.watches.push(Vec::new(), Vec::new());

        Var(idx)
    }

    pub fn add_clause(&mut self, clause: Clause) {
        self.add_clause_internal(clause, ClauseType::User);
    }

    fn add_clause_internal(
        &mut self,
        clause: Clause,
        clause_type: ClauseType,
    ) -> Option<ClauseIndex> {
        if clause.literals.len() == 0 {
            panic!("attempt to add empty clause");
        } else if clause.literals.len() == 1 {
            // TODO: What about the ROOT LEVEL?
            self.assert_literal(clause.literals[0], None);
            None
        } else {
            let first_watch = clause.literals[0];
            let second_watch = clause.literals[1];

            let idx = self.clause_database.add_clause(clause, clause_type);

            // We watch the negations, because we want to know when literals in our
            // clause become falsified. We don't care when they become true.
            self.watches[first_watch.negate()].push(idx);
            self.watches[second_watch.negate()].push(idx);

            Some(idx)
        }
    }

    fn search(&mut self) -> Option<Model> {
        loop {
            let maybe_conflict = self.propagate();
            if cfg!(debug_assertions) {
                self.check_watches();
            }
            if let Some(conflict) = maybe_conflict {
                // Conflict at root level means the formula is unsatisfiable
                if self.decision_level() == 0 {
                    return None;
                }

                let (learned_clause, backtrack_level) = self.analyze(conflict);
                debug!("New learned clause: {}", learned_clause);
                if cfg!(debug_assertions) {
                    learned_clause.check_valid_learned(
                        self.decision_level(),
                        backtrack_level,
                        &self.assignment,
                    );
                }

                self.cancel_until(backtrack_level);
                self.record(learned_clause);
            } else {
                if cfg!(debug_assertions) {
                    self.check_implied();
                }

                // If all variables are assigned, then we have a satisfying
                // assignment.
                if self.num_assigns() == self.assignment.num_vars() {
                    for v in &self.assignment.values {
                        if let VarInfo::Unassigned = v {
                            panic!("Found unassigned!");
                        }
                    }

                    let model = Some(Model::from_assignment(&self.assignment));
                    self.cancel_until(0);
                    return model;
                } else {
                    // Pick a new variable to assign

                    // For now, simply pick the first unassigned variable. TODO:
                    // Use a more optimized strategy.
                    let mut vars = self.assignment.values.iter().enumerate();
                    let var = loop {
                        let (i, info) = vars.next().unwrap();
                        if let VarInfo::Unassigned = info {
                            break Var(i);
                        }
                    };

                    self.assume(var.into());
                }
            }
        }
    }

    pub fn solve(mut self) -> Option<Model> {
        // TODO: Maybe do unit propagation at the beginning to handle unit
        // clauses which are there from the beginning.
        self.search()
    }
}
