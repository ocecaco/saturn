use crate::assignment::Assignment;
use crate::types::Clause;
use generational_arena::{Arena, Index};
use log::info;

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

pub struct LearnedClause {
    activity: f64,
    clause: Clause,
}

pub(crate) struct ClauseDatabase {
    pub(crate) clauses: Vec<Clause>,
    pub(crate) learned: Arena<LearnedClause>,
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
            ClauseIndex::Learned(idx) => self.learned.get(idx).map(|e| &e.clause),
        }
    }

    pub fn get_clause_mut(&mut self, idx: ClauseIndex) -> Option<&mut Clause> {
        match idx {
            ClauseIndex::Problem(idx) => Some(&mut self.clauses[idx]),
            ClauseIndex::Learned(idx) => self.learned.get_mut(idx).map(|e| &mut e.clause),
        }
    }

    pub fn add_clause(&mut self, clause: Clause, clause_type: ClauseType) -> ClauseIndex {
        match clause_type {
            ClauseType::Problem => {
                let idx = self.clauses.len();
                self.clauses.push(clause);
                ClauseIndex::Problem(idx)
            }
            ClauseType::Learned => ClauseIndex::Learned(self.learned.insert(LearnedClause {
                activity: 0.0,
                clause,
            })),
        }
    }

    pub fn reduce_db(&mut self, assignment: &Assignment) {
        info!("Reducing clause database");

        let mut activities = self
            .learned
            .iter()
            .map(|(i, elem)| (i, elem.activity))
            .collect::<Vec<_>>();

        // This comparison will panic on NaN values.
        activities.sort_unstable_by(|(_, act1), (_, act2)| act1.partial_cmp(act2).unwrap());

        let halfway_point = activities.len() / 2;

        let (bottom_half, top_half) = activities.split_at(halfway_point);

        // Remove all non-locked clauses below the median of activity
        for &(i, _) in bottom_half {
            let learned_clause = &self.learned[i];

            if !learned_clause
                .clause
                .is_locked(ClauseIndex::Learned(i), assignment)
            {
                self.learned.remove(i);
            }
        }

        // TODO: Calculate sensible threshold value
        let threshold = 0.0;

        // Remove non-locked clauses which are below a certain activity threshold
        for &(i, act) in top_half {
            let learned_clause = &self.learned[i];

            if act < threshold
                && !learned_clause
                    .clause
                    .is_locked(ClauseIndex::Learned(i), assignment)
            {
                self.learned.remove(i);
            }
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
