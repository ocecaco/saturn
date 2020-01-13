use std::cmp;
use std::collections::HashSet;
use std::fmt;
use std::mem;
use std::ops::{Index, IndexMut};

use log::debug;

struct LiteralInfo<T> {
    positive: T,
    negative: T,
}

struct LiteralMap<T>(Vec<LiteralInfo<T>>);

impl<T> Index<Literal> for LiteralMap<T> {
    type Output = T;

    fn index(&self, lit: Literal) -> &T {
        match lit.sign {
            Sign::Positive => &self.0[lit.var.0].positive,
            Sign::Negative => &self.0[lit.var.0].negative,
        }
    }
}

impl<T> IndexMut<Literal> for LiteralMap<T> {
    fn index_mut(&mut self, lit: Literal) -> &mut T {
        match lit.sign {
            Sign::Positive => &mut self.0[lit.var.0].positive,
            Sign::Negative => &mut self.0[lit.var.0].negative,
        }
    }
}

impl<T> LiteralMap<T> {
    fn new() -> LiteralMap<T> {
        LiteralMap(Vec::new())
    }

    fn push(&mut self, positive: T, negative: T) {
        self.0.push(LiteralInfo { positive, negative })
    }
}

type VarMap<T> = Vec<T>;

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum ClauseType {
    User,
    Learned,
}

type ClauseIndex = (ClauseType, usize);

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Var(usize);

impl fmt::Display for Var {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

// TODO: Possibly indicate sign by making literal negative/positive
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Literal {
    sign: Sign,
    var: Var,
}

impl fmt::Display for Literal {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.sign {
            Sign::Positive => write!(f, "{}", self.var),
            Sign::Negative => write!(f, "-{}", self.var),
        }
    }
}

impl Literal {
    pub fn negate(&self) -> Literal {
        Literal {
            sign: self.sign.flip(),
            var: self.var,
        }
    }

    fn assignment(&self) -> (Var, bool) {
        (self.var, self.sign.value())
    }
}

impl From<Var> for Literal {
    fn from(var: Var) -> Literal {
        Literal {
            sign: Sign::Positive,
            var,
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Sign {
    Positive,
    Negative,
}

impl Sign {
    fn flip(&self) -> Sign {
        match self {
            Sign::Positive => Sign::Negative,
            Sign::Negative => Sign::Positive,
        }
    }

    fn value(&self) -> bool {
        match self {
            Sign::Positive => true,
            Sign::Negative => false,
        }
    }
}

#[derive(Debug)]
pub struct Clause {
    literals: Vec<Literal>,
}

impl Clause {
    pub fn new(literals: Vec<Literal>) -> Self {
        // TODO: Normalize clause, check for (p v ~p)
        // occurrences, and potentially use the current solver state in
        // incremental implementation
        let mut literals = literals
            .iter()
            .copied()
            .collect::<HashSet<_>>()
            .iter()
            .copied()
            .collect::<Vec<_>>();

        literals.sort();

        Clause { literals }
    }

    fn new_unchecked(literals: Vec<Literal>) -> Self {
        Clause { literals }
    }

    fn calc_reason<'a>(&'a self, conflicting: bool) -> impl Iterator<Item = Literal> + 'a {
        // If this is a conflicting clause, then all of the literals are part of
        // the reason set. Otherwise, the first literal is not, since it is the
        // implied literal of the unit propagation.
        let reason = if conflicting {
            &self.literals[..]
        } else {
            &self.literals[1..]
        };
        reason.iter().copied()
    }

    fn watch_triggered(
        &mut self,
        lit: Literal,
        assignment: &Assignment,
    ) -> (Literal, Option<Literal>) {
        // Ensure that the falsified watched literal is in index 1
        if self.literals[0] == lit.negate() {
            self.literals.swap(0, 1);
        }

        // The other watched literal is already true: the clause is satisfied.
        if assignment.literal_value(self.literals[0]) == VarValue::True {
            return (lit, None);
        }

        // Find new literal to watch
        for (i, &alternative) in self.literals.iter().enumerate().skip(2) {
            if assignment.literal_value(alternative) != VarValue::False {
                // Found one! No need to do unit propagation
                self.literals.swap(1, i);
                return (self.literals[1].negate(), None);
            }
        }

        // If we didn't find a new literal, then this is a unit clause. Perform
        // unit propagation.
        (lit, Some(self.literals[0]))
    }
}

impl fmt::Display for Clause {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "[")?;
        let mut items = self.literals.iter();
        if let Some(x) = items.next() {
            write!(f, "{}", x)?;

            for i in items {
                write!(f, ", {}", i)?;
            }
        }
        write!(f, "]")
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum VarValue {
    True,
    False,
    Unassigned,
}

pub enum VarInfo {
    Assigned {
        value: bool,
        reason: Option<ClauseIndex>,
        level: usize,
    },
    Unassigned,
}

impl VarValue {
    fn negate(&self) -> VarValue {
        match self {
            VarValue::True => VarValue::False,
            VarValue::False => VarValue::True,
            VarValue::Unassigned => VarValue::Unassigned,
        }
    }
}

struct ClauseDatabase {
    clauses: Vec<Clause>,
    learned: Vec<Clause>,
}

impl ClauseDatabase {
    fn new() -> ClauseDatabase {
        ClauseDatabase {
            clauses: Vec::new(),
            learned: Vec::new(),
        }
    }

    fn get_clause(&self, idx: ClauseIndex) -> &Clause {
        match idx {
            (ClauseType::User, idx) => &self.clauses[idx],
            (ClauseType::Learned, idx) => &self.learned[idx],
        }
    }

    fn get_clause_mut(&mut self, idx: ClauseIndex) -> &mut Clause {
        match idx {
            (ClauseType::User, idx) => &mut self.clauses[idx],
            (ClauseType::Learned, idx) => &mut self.learned[idx],
        }
    }

    fn add_clause(&mut self, clause: Clause, clause_type: ClauseType) -> ClauseIndex {
        let db = match clause_type {
            ClauseType::User => &mut self.clauses,
            ClauseType::Learned => &mut self.learned,
        };

        let idx = db.len();
        db.push(clause);
        (clause_type, idx)
    }
}

pub struct Solver {
    clause_database: ClauseDatabase,
    watches: LiteralMap<Vec<ClauseIndex>>,
    // TODO: Potentially replace propagation queue by just the trail, as in the
    // actual MiniSAT implementation
    assignment: Assignment,
    trail: Vec<Literal>,
    trail_lim: Vec<usize>,
    // Position of propagation queue in trail. Based on MiniSAT implementation.
    queue_head: usize,
}

pub struct Assignment {
    values: VarMap<VarInfo>,
}

impl Assignment {
    fn new() -> Assignment {
        Assignment { values: Vec::new() }
    }

    fn new_var(&mut self) {
        self.values.push(VarInfo::Unassigned);
    }

    fn num_vars(&self) -> usize {
        self.values.len()
    }

    fn var_value(&self, var: Var) -> VarValue {
        match self.values[var.0] {
            VarInfo::Assigned { value: true, .. } => VarValue::True,
            VarInfo::Assigned { value: false, .. } => VarValue::False,
            VarInfo::Unassigned => VarValue::Unassigned,
        }
    }

    fn var_level(&self, var: Var) -> Option<usize> {
        match self.values[var.0] {
            VarInfo::Assigned { level, .. } => Some(level),
            VarInfo::Unassigned => None,
        }
    }

    fn var_reason(&self, var: Var) -> Option<ClauseIndex> {
        match self.values[var.0] {
            VarInfo::Assigned { reason, .. } => reason,
            VarInfo::Unassigned => None,
        }
    }

    fn literal_value(&self, lit: Literal) -> VarValue {
        let var_value = self.var_value(lit.var);

        match lit.sign {
            Sign::Positive => var_value,
            Sign::Negative => var_value.negate(),
        }
    }

    fn assign(&mut self, var: Var, info: VarInfo) {
        self.values[var.0] = info;
    }
}

#[derive(Debug)]
pub struct Model(VarMap<bool>);

impl Model {
    fn from_assignment(assignment: &Assignment) -> Self {
        let values = assignment
            .values
            .iter()
            .map(|v| match v {
                VarInfo::Assigned { value: true, .. } => true,
                VarInfo::Assigned { value: false, .. } => false,
                VarInfo::Unassigned => false,
            })
            .collect();
        Model(values)
    }
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

    fn num_assigns(&self) -> usize {
        self.trail.len()
    }

    fn record(&mut self, clause: Clause) {
        // Perform unit propagation on the asserting literal
        let asserting_lit = clause.literals[0];
        let clause_idx = self.add_clause(clause, ClauseType::Learned);

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
        let conflicting = true;

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

    pub fn add_clause(&mut self, clause: Clause, clause_type: ClauseType) -> Option<ClauseIndex> {
        if clause.literals.len() == 0 {
            panic!("attempt to add empty clause");
        } else if clause.literals.len() == 1 {
            // TODO: What about the ROOT LEVEL?
            self.assert_literal(clause.literals[0], None);
            None
        } else {
            // TODO: Set up initial watches, in incremental version this would need
            // to look at the current assignment
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
            if let Some(conflict) = maybe_conflict {
                // Conflict at root level means the formula is unsatisfiable
                if self.decision_level() == 0 {
                    return None;
                }

                let (learned_clause, backtrack_level) = self.analyze(conflict);
                self.cancel_until(backtrack_level);
                debug!("New learned clause: {}", learned_clause);
                self.record(learned_clause);
            } else {
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
