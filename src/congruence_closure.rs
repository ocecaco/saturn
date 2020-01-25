use std::collections::hash_map::Entry;
use std::collections::HashMap;
use std::mem;

// This implementation is based on "Congruence Closure with Integer Offsets" by
// Robert Nieuwenhuis and Albert Oliveras.

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Const(usize);

#[derive(Debug, Clone)]
pub struct Term {
    function: Const,
    args: Vec<Term>,
}

impl Term {
    pub fn new(function: Const, args: Vec<Term>) -> Self {
        Term { function, args }
    }
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
    proof_parents: ConstMap<Option<(Const, PendingEq)>>,
}

impl ConstSupply {
    fn fresh(&mut self) -> Const {
        let id = self.representatives.len();
        let new_const = Const(id);
        self.representatives.push(new_const);
        self.members.push(vec![new_const]);
        self.uses.push(Vec::new());
        self.proof_parents.push(None);
        new_const
    }

    fn num_constants(&self) -> usize {
        self.representatives.len()
    }
}

#[derive(Debug, Copy, Clone)]
pub struct ConstEq(Const, Const);

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct App(Const, Const);

#[derive(Debug, Copy, Clone)]
pub struct AppEq(App, Const);

#[derive(Debug, Copy, Clone)]
pub enum Equation {
    Constants(ConstEq),
    Application(AppEq),
}

#[derive(Debug, Copy, Clone)]
enum PendingEq {
    Constants(ConstEq),
    Application(AppEq, AppEq),
}

impl PendingEq {
    fn constants(&self) -> (Const, Const) {
        match self {
            PendingEq::Constants(ConstEq(a, b)) => (*a, *b),
            PendingEq::Application(AppEq(_, a), AppEq(_, b)) => (*a, *b),
        }
    }
}

pub struct EqualitySolver {
    const_supply: ConstSupply,
    lookup: HashMap<App, AppEq>,
    pending: Vec<PendingEq>,
}

impl EqualitySolver {
    pub fn new() -> Self {
        EqualitySolver {
            const_supply: ConstSupply {
                representatives: Vec::new(),
                members: Vec::new(),
                uses: Vec::new(),
                proof_parents: Vec::new(),
            },
            lookup: HashMap::new(),
            pending: Vec::new(),
        }
    }

    pub fn new_const(&mut self) -> Const {
        self.const_supply.fresh()
    }

    fn representative(&self, c: Const) -> Const {
        self.const_supply.representatives[c.0]
    }

    fn reparent(&mut self, c: Const, repr: Const) {
        self.const_supply.representatives[c.0] = repr;
        self.const_supply.members[repr.0].push(c);
    }

    fn class_size(&self, c: Const) -> usize {
        let c = self.representative(c);
        self.const_supply.members[c.0].len()
    }

    fn lookup(&self, app: App) -> Option<AppEq> {
        let App(a1, a2) = app;
        let a1 = self.representative(a1);
        let a2 = self.representative(a2);
        self.lookup.get(&App(a1, a2)).copied()
    }

    fn lookup_set(&mut self, app: App, eq: AppEq) {
        let App(a1, a2) = app;
        let a1 = self.representative(a1);
        let a2 = self.representative(a2);
        self.lookup.insert(App(a1, a2), eq);
    }

    fn add_to_uses(&mut self, eq: AppEq) {
        let AppEq(App(a1, a2), _) = eq;
        let a1 = self.representative(a1);
        let a2 = self.representative(a2);
        self.const_supply.uses[a1.0].push(eq);
        self.const_supply.uses[a2.0].push(eq);
    }

    pub fn merge(&mut self, eq: Equation) {
        match eq {
            Equation::Constants(eq) => {
                self.pending.push(PendingEq::Constants(eq));
                self.propagate();
            }
            Equation::Application(eq) => {
                let AppEq(app, _) = eq;
                if let Some(oldeq) = self.lookup(app) {
                    self.pending.push(PendingEq::Application(eq, oldeq));
                    self.propagate();
                } else {
                    self.lookup_set(app, eq);
                    self.add_to_uses(eq);
                }
            }
        }
    }

    fn add_proof_edge(&mut self, reason: PendingEq) {}

    pub fn propagate(&mut self) {
        while let Some(eq) = self.pending.pop() {
            let (a_orig, b_orig) = eq.constants();

            let a = self.representative(a_orig);
            let b = self.representative(b_orig);

            // Do nothing if already equal
            if a == b {
                continue;
            }

            // Keep track of this union for generating
            // explanations.
            self.add_proof_edge(eq);

            // Make sure that the size of a's equivalence class is less than or
            // equal to b, which is necessary to guarantee good time complexity.
            // This is common in union-find data structures.
            let (a, b) = if self.class_size(a) > self.class_size(b) {
                (b, a)
            } else {
                (a, b)
            };

            // Merge a into b's class
            let members_a = mem::replace(&mut self.const_supply.members[a.0], Vec::new());
            for &m in &members_a {
                self.reparent(m, b);
            }

            // Generate new equations according to the lookup table, which are
            // caused by congruences.
            let uses_a = mem::replace(&mut self.const_supply.uses[a.0], Vec::new());
            for &eq in &uses_a {
                let AppEq(app, _) = eq;
                if let Some(lookupeq) = self.lookup(app) {
                    self.pending.push(PendingEq::Application(eq, lookupeq));
                } else {
                    self.lookup_set(app, eq);
                    self.const_supply.uses[b.0].push(eq);
                }
            }
        }
    }
}
