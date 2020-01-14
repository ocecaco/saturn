use crate::types::Clause;
use crate::util::LiteralMap;

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub(crate) enum ClauseType {
    User,
    Learned,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct ClauseIndex {
    ty: ClauseType,
    offset: usize,
}

pub(crate) struct ClauseDatabase {
    pub(crate) clauses: Vec<Clause>,
    pub(crate) learned: Vec<Clause>,
}

impl ClauseDatabase {
    pub fn new() -> ClauseDatabase {
        ClauseDatabase {
            clauses: Vec::new(),
            learned: Vec::new(),
        }
    }

    pub fn get_clause(&self, idx: ClauseIndex) -> &Clause {
        match idx.ty {
            ClauseType::User => &self.clauses[idx.offset],
            ClauseType::Learned => &self.learned[idx.offset],
        }
    }

    pub fn get_clause_mut(&mut self, idx: ClauseIndex) -> &mut Clause {
        match idx.ty {
            ClauseType::User => &mut self.clauses[idx.offset],
            ClauseType::Learned => &mut self.learned[idx.offset],
        }
    }

    pub fn add_clause(&mut self, clause: Clause, clause_type: ClauseType) -> ClauseIndex {
        let db = match clause_type {
            ClauseType::User => &mut self.clauses,
            ClauseType::Learned => &mut self.learned,
        };

        let idx = db.len();
        db.push(clause);
        ClauseIndex {
            ty: clause_type,
            offset: idx,
        }
    }

    pub(crate) fn expected_watches(&self, watches: &mut LiteralMap<Vec<ClauseIndex>>) {
        for (i, c) in self.clauses.iter().enumerate() {
            let idx = ClauseIndex {
                ty: ClauseType::User,
                offset: i,
            };

            watches[c.literals[0].negate()].push(idx);
            watches[c.literals[1].negate()].push(idx);
        }

        for (i, c) in self.learned.iter().enumerate() {
            let idx = ClauseIndex {
                ty: ClauseType::Learned,
                offset: i,
            };

            watches[c.literals[0].negate()].push(idx);
            watches[c.literals[1].negate()].push(idx);
        }
    }
}
