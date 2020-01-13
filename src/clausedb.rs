use crate::types::Clause;

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub(crate) enum ClauseType {
    User,
    Learned,
}

#[derive(Debug, Copy, Clone)]
pub struct ClauseIndex {
    ty: ClauseType,
    offset: usize,
}

pub(crate) struct ClauseDatabase {
    clauses: Vec<Clause>,
    learned: Vec<Clause>,
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
}
