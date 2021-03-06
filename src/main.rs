#![warn(clippy::all)]
mod assignment;
mod clausedb;
mod congruence_closure;
mod solver;
mod types;
mod util;
mod varorder;

type Error = Box<dyn std::error::Error>;
type Result<T> = std::result::Result<T, Error>;

use crate::congruence_closure::{App, AppEq, ConstEq, EqualitySolver, Equation};
use log::debug;
use solver::Solver;
use std::convert::TryInto;
use std::env;
use std::fs::File;
use std::io::{BufRead, BufReader};
use types::{Clause, Literal};

#[allow(clippy::comparison_chain)]
fn load_dimacs(solver: &mut Solver, filename: &str) -> Result<()> {
    let file = File::open(filename)?;
    let reader = BufReader::new(file);
    let mut lines = reader.lines();
    let mut num_vars = None;
    let mut num_clauses = None;

    for line in lines.by_ref() {
        let line = line?;

        let field = line.split_whitespace().collect::<Vec<_>>();

        if field.len() >= 2 && field[..2] == ["p", "cnf"] {
            num_vars = Some(field[2].parse().unwrap());
            num_clauses = Some(field[3].parse().unwrap());
            break;
        }
    }
    let num_vars = num_vars.unwrap();
    let num_clauses = num_clauses.unwrap();

    let mut variables = Vec::with_capacity(num_vars);
    for _ in 0..num_vars {
        variables.push(solver.new_var());
    }

    for _ in 0..num_clauses {
        let line = lines.next().expect("expected more lines")?;

        let mut clause = Vec::new();
        let fields = line.split_whitespace();

        for f in fields {
            let var = f.parse::<i32>().unwrap();

            if var > 0 {
                let idx: usize = (var - 1).try_into().unwrap();
                let lit = variables[idx].into();
                clause.push(lit);
            } else if var < 0 {
                let idx: usize = (-var - 1).try_into().unwrap();
                let lit: Literal = variables[idx].into();
                clause.push(lit.negate());
            } else {
                break;
            }
        }

        solver.add_clause(Clause::new(clause));
    }

    debug!("Finished adding clauses");

    Ok(())
}

#[allow(clippy::many_single_char_names)]
fn test_equality() {
    let mut solver = EqualitySolver::new();

    let a = solver.new_const();
    let b = solver.new_const();
    let c = solver.new_const();
    let d = solver.new_const();
    let x = solver.new_const();
    let y = solver.new_const();
    let z = solver.new_const();
    let w = solver.new_const();
    let f = solver.new_const();
    println!(
        "{:?}",
        solver.merge(Equation::Application(AppEq(App(f, x), a))),
    );
    println!(
        "{:?}",
        solver.merge(Equation::Application(AppEq(App(f, y), b))),
    );

    println!(
        "{:?}",
        solver.merge(Equation::Constants(true, ConstEq(a, c))),
    );

    println!(
        "{:?}",
        solver.merge(Equation::Constants(true, ConstEq(d, b))),
    );

    println!(
        "{:?}",
        solver.merge(Equation::Constants(false, ConstEq(c, d))),
    );
    println!(
        "{:?}",
        solver.merge(Equation::Application(AppEq(App(f, z), x))),
    );
    println!(
        "{:?}",
        solver.merge(Equation::Application(AppEq(App(f, w), y))),
    );
    println!(
        "{:?}",
        solver.merge(Equation::Constants(true, ConstEq(z, w))),
    );
    println!("{:?}", solver.are_congruent(b, c));
    println!("{:?}", solver.explain_conflict(b, c));
    println!("{:?}", solver.explain(true, b, c));
}

fn main() -> Result<()> {
    env_logger::init();

    let args: Vec<_> = env::args().collect();

    let mut solver = Solver::new();

    load_dimacs(&mut solver, &args[1])?;

    println!("{:?}", solver.solve());
    test_equality();

    Ok(())
}
