use std::collections::HashSet;
use std::fmt;

use crate::assignment::{Assignment, VarInfo};
use crate::clausedb::ClauseIndex;
use crate::util::VarMap;

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Var(pub(crate) usize);

impl fmt::Display for Var {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Literal {
    pub(crate) sign: Sign,
    pub(crate) var: Var,
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

    pub fn assignment(&self) -> (Var, bool) {
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
    fn flip(self) -> Sign {
        match self {
            Sign::Positive => Sign::Negative,
            Sign::Negative => Sign::Positive,
        }
    }

    fn value(self) -> bool {
        match self {
            Sign::Positive => true,
            Sign::Negative => false,
        }
    }
}

#[derive(Debug)]
pub struct Clause {
    pub(crate) literals: Vec<Literal>,
}

impl Clause {
    pub fn new(literals: Vec<Literal>) -> Self {
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

    pub fn new_unchecked(literals: Vec<Literal>) -> Self {
        Clause { literals }
    }

    pub fn calc_reason<'a>(&'a self, conflicting: bool) -> impl Iterator<Item = Literal> + 'a {
        // If this is a conflicting clause, then all of the literals are part of
        // the reason set. Otherwise, the first literal is not, since it is the
        // implied literal of the unit propagation.
        let reason = if conflicting {
            &self.literals[..]
        } else {
            &self.literals[1..]
        };

        // Negated, because the reason for our tail literals being all False
        // (and thus for this clause being implied) is
        // that their negations were True
        reason.iter().copied().map(|lit| lit.negate())
    }

    pub fn is_locked(&self, idx: ClauseIndex, assignment: &Assignment) -> bool {
        assignment.var_reason(self.literals[0].var) == Some(idx)
    }

    pub fn watch_triggered(
        &mut self,
        lit: Literal,
        assignment: &Assignment,
    ) -> (Literal, Option<Literal>) {
        // Ensure that the falsified watched literal is in index 1
        if self.literals[0] == lit.negate() {
            self.literals.swap(0, 1);
        }

        // The other watched literal is already true: the clause is satisfied.
        if assignment.literal_value(self.literals[0]) == Some(true) {
            return (lit, None);
        }

        // Find new literal to watch
        for (i, &alternative) in self.literals.iter().enumerate().skip(2) {
            if assignment.literal_value(alternative) != Some(false) {
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

#[derive(Debug)]
pub struct Model(VarMap<bool>);

impl Model {
    pub fn from_assignment(assignment: &Assignment) -> Self {
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
