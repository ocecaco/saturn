use crate::clausedb::ClauseIndex;
use crate::types::{Literal, Sign, Var};
use crate::util::VarMap;

pub enum VarInfo {
    Assigned {
        value: bool,
        reason: Option<ClauseIndex>,
        level: usize,
    },
    Unassigned,
}

pub struct Assignment {
    pub(crate) values: VarMap<VarInfo>,
}

impl Assignment {
    pub fn new() -> Assignment {
        Assignment { values: Vec::new() }
    }

    pub fn new_var(&mut self) {
        self.values.push(VarInfo::Unassigned);
    }

    pub fn num_vars(&self) -> usize {
        self.values.len()
    }

    pub fn var_value(&self, var: Var) -> Option<bool> {
        match self.values[var.0] {
            VarInfo::Assigned { value: v, .. } => Some(v),
            VarInfo::Unassigned => None,
        }
    }

    pub fn var_level(&self, var: Var) -> Option<usize> {
        match self.values[var.0] {
            VarInfo::Assigned { level, .. } => Some(level),
            VarInfo::Unassigned => None,
        }
    }

    pub fn var_reason(&self, var: Var) -> Option<ClauseIndex> {
        match self.values[var.0] {
            VarInfo::Assigned { reason, .. } => reason,
            VarInfo::Unassigned => None,
        }
    }

    pub fn literal_value(&self, lit: Literal) -> Option<bool> {
        let var_value = self.var_value(lit.var);

        match lit.sign {
            Sign::Positive => var_value,
            Sign::Negative => var_value.map(|v| !v),
        }
    }

    pub fn assign(&mut self, var: Var, info: VarInfo) {
        self.values[var.0] = info;
    }
}
