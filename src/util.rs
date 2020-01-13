use std::ops::{Index, IndexMut};

use crate::types::{Literal, Sign};

struct LiteralInfo<T> {
    positive: T,
    negative: T,
}

pub struct LiteralMap<T>(Vec<LiteralInfo<T>>);

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
    pub fn new() -> LiteralMap<T> {
        LiteralMap(Vec::new())
    }

    pub fn push(&mut self, positive: T, negative: T) {
        self.0.push(LiteralInfo { positive, negative })
    }
}

pub type VarMap<T> = Vec<T>;
