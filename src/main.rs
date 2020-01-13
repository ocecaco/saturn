mod solver;

type Error = Box<dyn std::error::Error>;
type Result<T> = std::result::Result<T, Error>;

use solver::{Clause, ClauseType, Literal, Solver};
use std::convert::TryInto;
use std::fs::File;
use std::io::{BufRead, BufReader};

fn load_dimacs(solver: &mut Solver, filename: &str) -> Result<()> {
    let file = File::open(filename)?;
    let reader = BufReader::new(file);
    let mut lines = reader.lines();
    let mut num_vars = None;
    let mut num_clauses = None;

    for line in lines.by_ref() {
        let line = line?;

        let field = line.split_whitespace().collect::<Vec<_>>();

        if field[..2] == ["p", "cnf"] {
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

        solver.add_clause(Clause::new(clause).unwrap(), ClauseType::User);
    }

    Ok(())
}

fn main() -> Result<()> {
    let mut solver = Solver::new();

    load_dimacs(&mut solver, "test.dimacs")?;

    println!("{:?}", solver.solve().unwrap());

    Ok(())
}
