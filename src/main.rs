#![allow(dead_code)]
mod solver;

use solver::{Clause, Solver};

fn main() {
    let mut solver = Solver::new();
    let a = solver.new_var().into();
    let b = solver.new_var().into();
    let c = solver.new_var().into();
    let clause1 = Clause::new(vec![a, b, c]).unwrap();
    let clause2 = Clause::new(vec![!a, !b, !c]).unwrap();
    solver.add_clause(clause1);
    solver.add_clause(clause2);

    println!("{:?}", solver.solve().unwrap());
}
