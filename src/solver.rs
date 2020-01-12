use std::collections::{HashSet, VecDeque};
use std::mem;
use std::ops::{Index, IndexMut, Not};

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

#[derive(Debug, Copy, Clone)]
pub enum ClauseType {
    User,
    Learned,
}

type ClauseIndex = (ClauseType, usize);

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Var(usize);

// TODO: Possibly indicate sign by making literal negative/positive
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Literal {
    sign: Sign,
    var: Var,
}

impl Literal {
    fn negate(&self) -> Literal {
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

impl Not for Literal {
    type Output = Literal;

    fn not(self) -> Self::Output {
        Literal {
            sign: self.sign.flip(),
            var: self.var,
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
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
    pub fn new(literals: Vec<Literal>) -> Option<Self> {
        // TODO: Normalize clause, check for (p v ~p)
        // occurrences, and potentially use the current solver state in
        // incremental implementation
        let literals = literals
            .iter()
            .copied()
            .collect::<HashSet<_>>()
            .iter()
            .copied()
            .collect::<Vec<_>>();

        if literals.len() >= 2 {
            Some(Clause { literals })
        } else {
            None
        }
    }

    fn new_unchecked(literals: Vec<Literal>) -> Self {
        Clause { literals }
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
    propagation_queue: VecDeque<Literal>,
    assignment: Assignment,
    trail: Vec<Literal>,
    trail_lim: Vec<usize>,
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
            propagation_queue: VecDeque::new(),
            assignment: Assignment::new(),
            trail: Vec::new(),
            trail_lim: Vec::new(),
        }
    }

    fn assume(&mut self, lit: Literal) -> bool {
        self.trail_lim.push(self.trail.len());
        self.assert_literal(lit, None)
    }

    fn undo_one(&mut self) {
        let last = self.trail.pop().unwrap();

        self.assignment.assign(last.var, VarInfo::Unassigned);
    }

    fn cancel(&mut self) {
        let num_undo = self.trail.len() - self.trail_lim.pop().unwrap();

        for _ in 0..num_undo {
            self.undo_one();
        }
    }

    fn decision_level(&self) -> usize {
        unimplemented!();
    }

    // Asserts a literal
    // TODO: Maybe do not use boolean for error reporting
    fn assert_literal(&mut self, lit: Literal, reason: Option<ClauseIndex>) -> bool {
        match self.assignment.literal_value(lit) {
            VarValue::Unassigned => match lit.assignment() {
                (var, value) => {
                    self.assignment.assign(
                        var,
                        VarInfo::Assigned {
                            value,
                            reason,
                            level: self.decision_level(),
                        },
                    );
                    self.trail.push(lit);
                    self.propagation_queue.push_back(lit);
                    true
                }
            },
            // Conflicting assignment
            VarValue::False => false,
            // Already set
            VarValue::True => true,
        }
    }

    fn handle_clause(&mut self, clause_index: ClauseIndex, lit: Literal) -> bool {
        // This function should always resubscribe to some watched literal, to
        // ensure that the number of watched literals is always equal to 2
        let unit_literal = {
            let clause = self.clause_database.get_clause_mut(clause_index);

            // Ensure that the falsified watched literal is in index 1
            if clause.literals[0] == lit.negate() {
                clause.literals.swap(0, 1);
            }

            // The other watched literal is already true: the clause is satisfied.
            if self.assignment.literal_value(clause.literals[0]) == VarValue::True {
                self.watches[lit].push(clause_index);
                return true;
            }

            // Find new literal to watch
            for (i, &alternative) in clause.literals[2..].iter().enumerate() {
                if self.assignment.literal_value(alternative) != VarValue::False {
                    // Found one!
                    clause.literals.swap(1, i);
                    self.watches[clause.literals[1].negate()].push(clause_index);
                    return true;
                }
            }

            clause.literals[0]
        };

        // If we didn't find a new literal, then this is a unit clause. Perform
        // unit propagation.
        self.watches[lit].push(clause_index);
        return self.assert_literal(unit_literal, Some(clause_index));
    }

    fn propagate(&mut self) -> bool {
        while let Some(lit) = self.propagation_queue.pop_front() {
            // We empty out the watch list as we process it. Clauses are
            // responsible for re-adding themselves to the watch list if
            // necessary.
            let watches = mem::replace(&mut self.watches[lit], Vec::new());

            for &c_idx in &watches {
                if !self.handle_clause(c_idx, lit) {
                    // TODO: Maybe put remaining clauses back into the watch
                    // list, as in MiniSAT? Why do they do that?
                    self.propagation_queue.clear();
                    return false;
                }
            }
        }

        true
    }

    pub fn new_var(&mut self) -> Var {
        let idx = self.assignment.num_vars();

        self.assignment.new_var();
        self.watches.push(Vec::new(), Vec::new());

        Var(idx)
    }

    pub fn add_clause(&mut self, clause: Clause, clause_type: ClauseType) {
        // TODO: Set up initial watches, in incremental version this would need
        // to look at the current assignment
        let first_watch = clause.literals[0];
        let second_watch = clause.literals[1];

        let idx = self.clause_database.add_clause(clause, clause_type);

        // We watch the negations, because we want to know when literals in our
        // clause become falsified. We don't care when they become true.
        self.watches[first_watch.negate()].push(idx);
        self.watches[second_watch.negate()].push(idx);
    }

    pub fn solve(mut self) -> Option<Model> {
        // TODO: Maybe do unit propagation at the beginning to handle unit
        // clauses which are there from the beginning.

        unimplemented!();
    }
}
