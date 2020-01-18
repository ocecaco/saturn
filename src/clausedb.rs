use crate::types::Clause;
use generational_arena::{Arena, Index};

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub(crate) enum ClauseType {
    Problem,
    Learned,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum ClauseIndex {
    Problem(usize),
    Learned(Index),
}

pub(crate) struct ClauseDatabase {
    pub(crate) clauses: Vec<Clause>,
    pub(crate) learned: Arena<Clause>,
}

impl ClauseDatabase {
    pub fn new() -> ClauseDatabase {
        ClauseDatabase {
            clauses: Vec::new(),
            learned: Arena::new(),
        }
    }

    pub fn get_clause(&self, idx: ClauseIndex) -> Option<&Clause> {
        // Panics when it can't find a user clause, but returns None when it
        // can't find a learned clause. This is to support "lazy" removal of
        // learned clauses from watch lists, where watched LEARNED clauses are
        // simply ignored if they no longer exist. Since user clauses should
        // never be removed, they cause a panic when not found.
        match idx {
            ClauseIndex::Problem(idx) => Some(&self.clauses[idx]),
            ClauseIndex::Learned(idx) => self.learned.get(idx),
        }
    }

    pub fn get_clause_mut(&mut self, idx: ClauseIndex) -> Option<&mut Clause> {
        match idx {
            ClauseIndex::Problem(idx) => Some(&mut self.clauses[idx]),
            ClauseIndex::Learned(idx) => self.learned.get_mut(idx),
        }
    }

    pub fn add_clause(&mut self, clause: Clause, clause_type: ClauseType) -> ClauseIndex {
        match clause_type {
            ClauseType::Problem => {
                let idx = self.clauses.len();
                self.clauses.push(clause);
                ClauseIndex::Problem(idx)
            }
            ClauseType::Learned => ClauseIndex::Learned(self.learned.insert(clause)),
        }
    }

    // pub(crate) fn expected_watches(&self, watches: &mut LiteralMap<Vec<ClauseIndex>>) {
    //     for (i, c) in self.clauses.iter().enumerate() {
    //         let idx = ClauseIndex {
    //             ty: ClauseType::Problem,
    //             offset: i,
    //         };

    //         watches[c.literals[0].negate()].push(idx);
    //         watches[c.literals[1].negate()].push(idx);
    //     }

    //     for (i, c) in self.learned.iter().enumerate() {
    //         let idx = ClauseIndex {
    //             ty: ClauseType::Learned,
    //             offset: i,
    //         };

    //         watches[c.literals[0].negate()].push(idx);
    //         watches[c.literals[1].negate()].push(idx);
    //     }
    // }
}
