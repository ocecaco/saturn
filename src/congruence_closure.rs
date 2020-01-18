#![allow(dead_code)]
use std::collections::hash_map::Entry;
use std::collections::HashMap;
use std::mem;

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
struct Const(usize);

#[derive(Debug, Clone)]
struct Term {
    function: Const,
    args: Vec<Term>,
}

#[derive(Debug, Clone)]
enum Curried {
    Const(Const),
    Apply(Box<Curried>, Box<Curried>),
}

fn currify(t: &Term) -> Curried {
    let mut result = Curried::Const(t.function);

    for t in &t.args {
        result = Curried::Apply(Box::new(result), Box::new(currify(t)));
    }

    result
}

type ConstMap<T> = Vec<T>;

struct ConstSupply {
    representatives: ConstMap<Const>,
    members: ConstMap<Vec<Const>>,
    uses: ConstMap<Vec<AppEq>>,
}

impl ConstSupply {
    fn fresh(&mut self) -> Const {
        let id = self.representatives.len();
        let new_const = Const(id);
        self.representatives.push(new_const);
        self.members.push(vec![new_const]);
        self.uses.push(Vec::new());
        new_const
    }

    fn num_constants(&self) -> usize {
        self.representatives.len()
    }
}

type AppEq = ((Const, Const), Const);
type ConstEq = (Const, Const);

struct EqualitySolver {
    const_supply: ConstSupply,
    app_equations: HashMap<(Const, Const), Const>,
    const_equations: Vec<(Const, Const)>,
}

impl EqualitySolver {
    fn new() -> Self {
        EqualitySolver {
            const_supply: ConstSupply {
                representatives: Vec::new(),
                members: Vec::new(),
                uses: Vec::new(),
            },
            app_equations: HashMap::new(),
            const_equations: Vec::new(),
        }
    }

    fn add_equation(&mut self, t1: &Term, t2: &Term) {
        let c1 = self.flatten(&currify(t1));
        let c2 = self.flatten(&currify(t2));
        self.const_equations.push((c1, c2));
    }

    fn flatten(&mut self, curried: &Curried) -> Const {
        match curried {
            Curried::Const(c) => *c,
            Curried::Apply(t1, t2) => {
                let c1 = self.flatten(t1);
                let c2 = self.flatten(t2);
                self.flatten_app(c1, c2)
            }
        }
    }

    fn flatten_app(&mut self, c1: Const, c2: Const) -> Const {
        match self.app_equations.entry((c1, c2)) {
            Entry::Occupied(e) => *e.get(),
            Entry::Vacant(e) => {
                let c = self.const_supply.fresh();
                let app_eq = ((c1, c2), c);
                self.const_supply.uses[c1.0].push(app_eq);
                self.const_supply.uses[c2.0].push(app_eq);
                e.insert(c);
                c
            }
        }
    }

    fn congruence_closure(&mut self) {
        while let Some((a, b)) = self.const_equations.pop() {
            let a = self.const_supply.representatives[a.0];
            let b = self.const_supply.representatives[b.0];
            // TODO: Order by class size

            if a != b {
                // Move all of the members from the class of a to the class of b
                let a_members = mem::replace(&mut self.const_supply.members[a.0], Vec::new());
                for c in a_members {
                    self.const_supply.representatives[c.0] = b;
                    self.const_supply.members[b.0].push(c);
                }

                let a_uses = mem::replace(&mut self.const_supply.uses[a.0], Vec::new());
                for orig_eq in a_uses {
                    let ((c, d), e) = orig_eq;
                    let c = self.const_supply.representatives[c.0];
                    let d = self.const_supply.representatives[d.0];
                    let e = self.const_supply.representatives[e.0];

                    if let Some(f) = self.app_equations.get(&(c, d)) {
                        let f = self.const_supply.representatives[f.0];

                        if f != e {
                            self.const_equations.push((e, f));
                        }

                        self.app_equations.insert((c, d), e);
                        self.const_supply.uses[b.0].push(orig_eq);
                    }
                }
            }
        }
    }
}
