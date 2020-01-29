use std::collections::hash_map::Entry;
use std::collections::{HashMap, HashSet};
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
type ProofForest = ConstMap<Option<(Const, PendingEq)>>;

struct ConstSupply {
    representatives: ConstMap<Const>,
    members: ConstMap<Vec<Const>>,
    uses: ConstMap<Vec<AppEq>>,
    proof_parents: ProofForest,
    // For each representative, the set of other representatives that it is
    // known to be disequal to
    disequalities: ConstMap<HashSet<Const>>,
    disequalities_reason: HashMap<(Const, Const), (Const, Const)>,
}

impl ConstSupply {
    fn fresh(&mut self) -> Const {
        let id = self.representatives.len();
        let new_const = Const(id);
        self.representatives.push(new_const);
        self.members.push(vec![new_const]);
        self.uses.push(Vec::new());
        self.proof_parents.push(None);
        self.disequalities.push(HashSet::new());
        new_const
    }

    fn num_constants(&self) -> usize {
        self.representatives.len()
    }
}

#[derive(Debug, Copy, Clone)]
pub struct ConstEq(pub Const, pub Const);

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct App(pub Const, pub Const);

#[derive(Debug, Copy, Clone)]
pub struct AppEq(pub App, pub Const);

#[derive(Debug, Copy, Clone)]
pub enum Equation {
    Constants(bool, ConstEq),
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

#[must_use]
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum SolverState {
    Consistent,
    Inconsistent(Const, Const),
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
                disequalities: Vec::new(),
                disequalities_reason: HashMap::new(),
            },
            lookup: HashMap::new(),
            pending: Vec::new(),
        }
    }

    pub fn new_const(&mut self) -> Const {
        self.const_supply.fresh()
    }

    pub fn representative(&self, c: Const) -> Const {
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

    fn disequality_reason_set_single(&mut self, a: Const, b: Const, eq: ConstEq) {
        if let Entry::Vacant(o) = self.const_supply.disequalities_reason.entry((a, b)) {
            let ConstEq(c1, c2) = eq;
            o.insert((c1, c2));
        }
    }

    fn disequality_reason_set(&mut self, a: Const, b: Const, eq: ConstEq) {
        self.disequality_reason_set_single(a, b, eq);
        self.disequality_reason_set_single(b, a, eq);
    }

    fn disequality_reason_get(&self, a: Const, b: Const) -> ConstEq {
        let (c1, c2) = self.const_supply.disequalities_reason[&(a, b)];
        ConstEq(c1, c2)
    }

    pub fn merge(&mut self, eq: Equation) -> SolverState {
        match eq {
            Equation::Constants(positive, eq) => {
                if positive {
                    self.pending.push(PendingEq::Constants(eq));
                    self.propagate()
                } else {
                    let ConstEq(a, b) = eq;
                    let a = self.representative(a);
                    let b = self.representative(b);

                    // If we try to introduce a disequality between classes
                    // which are equal, then it's an error.
                    if a != b {
                        self.const_supply.disequalities[a.0].insert(b);
                        self.const_supply.disequalities[b.0].insert(a);
                        self.disequality_reason_set(a, b, eq);
                        SolverState::Consistent
                    } else {
                        SolverState::Inconsistent(a, b)
                    }
                }
            }
            Equation::Application(eq) => {
                let AppEq(app, _) = eq;
                if let Some(oldeq) = self.lookup(app) {
                    self.pending.push(PendingEq::Application(eq, oldeq));
                    self.propagate()
                } else {
                    self.lookup_set(app, eq);
                    self.add_to_uses(eq);
                    SolverState::Consistent
                }
            }
        }
    }

    fn add_proof_edge(&mut self, reason: PendingEq) {
        let (a, b) = reason.constants();

        let (a, b) = if self.class_size(a) > self.class_size(b) {
            (b, a)
        } else {
            (a, b)
        };

        // Reverse the path from a to the root of its tree and add edge from a
        // to b. By doing this, we ensure that we can always find the shortest
        // path between any two nodes in our tree by just taking those edges
        // that go toward their common ancestor.
        let mut previous = b;
        let mut maybe_current = Some((a, reason));
        while let Some((current, previous_reason)) = maybe_current {
            let old_parent = self.const_supply.proof_parents[current.0];
            self.const_supply.proof_parents[current.0] = Some((previous, previous_reason));
            previous = current;
            maybe_current = old_parent;
        }
    }

    fn safe_to_merge(&self, a: Const, b: Const) -> bool {
        for &da in &self.const_supply.disequalities[a.0] {
            if self.representative(da) == b {
                return false;
            }
        }

        true
    }

    fn merge_classes(&mut self, a: Const, b: Const) {
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

        let disequalities_a =
            mem::replace(&mut self.const_supply.disequalities[a.0], HashSet::new());
        for &da in &disequalities_a {
            let da = self.representative(da);
            self.const_supply.disequalities[b.0].insert(da);
            self.const_supply.disequalities[da.0].insert(b);
            let old_reason = self.disequality_reason_get(a, da);
            self.disequality_reason_set(da, b, old_reason);
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

    fn check_diseq(&self, a: Const) -> bool {
        let a = self.representative(a);

        for &da in &self.const_supply.disequalities[a.0] {
            let da = self.representative(da);

            if da == a {
                return false;
            }
        }

        true
    }

    fn propagate(&mut self) -> SolverState {
        while let Some(eq) = self.pending.pop() {
            let (a_orig, b_orig) = eq.constants();

            let a = self.representative(a_orig);
            let b = self.representative(b_orig);

            // Do nothing if already equal
            if a == b {
                continue;
            }

            self.merge_classes(a, b);

            // Keep track of this union for generating
            // explanations.
            self.add_proof_edge(eq);

            if !self.check_diseq(a) {
                return SolverState::Inconsistent(a, b);
            }
        }

        SolverState::Consistent
    }

    pub fn are_congruent(&self, a: Const, b: Const) -> bool {
        let a = self.representative(a);
        let b = self.representative(b);
        a == b
    }

    pub fn explain(&self, positive: bool, a: Const, b: Const) -> Vec<Equation> {
        if positive {
            let mut explanation_generator =
                ExplanationGenerator::new(&self.const_supply.proof_parents);
            explanation_generator.explain(a, b);
            explanation_generator.done()
        } else {
            let ConstEq(c1, c2) =
                self.disequality_reason_get(self.representative(a), self.representative(b));
            let mut explanation_generator =
                ExplanationGenerator::new(&self.const_supply.proof_parents);
            explanation_generator.explain(a, c1);
            explanation_generator.explain(b, c2);
            let mut explanation = explanation_generator.done();
            explanation.push(Equation::Constants(false, ConstEq(c1, c2)));
            explanation
        }
    }

    pub fn explain_conflict(&self, a: Const, b: Const) -> Vec<Equation> {
        let ConstEq(c1, c2) =
            self.disequality_reason_get(self.representative(a), self.representative(b));

        let mut explanation_generator = ExplanationGenerator::new(&self.const_supply.proof_parents);

        explanation_generator.explain(a, b);
        explanation_generator.explain(a, c1);
        explanation_generator.explain(b, c2);
        let mut explanation = explanation_generator.done();
        explanation.push(Equation::Constants(false, ConstEq(c1, c2)));
        explanation
    }
}

pub struct ExplanationGenerator<'a> {
    proof_forest: &'a ProofForest,
    // For each represenatative, the highest node in its class. A node is higher
    // if it is closer to the root of its proof tree in the proof forest. During
    // explanation generation, we can typically jump to the highest node in a
    // class, thereby skipping many edges of the proof tree.
    highest_node: ConstMap<Option<Const>>,
    // Union-find data structure.
    // This only keeps track of elements which are equal
    // due to the PROOF OUTPUT SO FAR (i.e., things might be non-equal which are
    // in fact equal in the original EqualitySolver).
    representatives: ConstMap<Const>,
    // For each representative, the list of its members
    members: ConstMap<Vec<Const>>,
    explanation: Vec<Equation>,
    pending: Vec<(Const, Const)>,
}

impl<'a> ExplanationGenerator<'a> {
    fn new(proof_forest: &'a ProofForest) -> Self {
        let num_constants = proof_forest.len();

        let mut highest_node = Vec::with_capacity(num_constants);
        let mut representatives = Vec::with_capacity(num_constants);
        let mut members = Vec::with_capacity(num_constants);
        // Initially, each node is its own representative, and also the highest
        // node in its own class.
        for i in 0..num_constants {
            let new_const = Const(i);
            highest_node.push(Some(new_const));
            representatives.push(new_const);
            members.push(vec![new_const]);
        }

        ExplanationGenerator {
            proof_forest,
            highest_node,
            representatives,
            members,
            explanation: Vec::new(),
            pending: Vec::new(),
        }
    }

    fn explain(&mut self, c1: Const, c2: Const) {
        self.pending.push((c1, c2));

        while let Some((a, b)) = self.pending.pop() {
            let c = self
                .nearest_common_ancestor(a, b)
                .expect("Nodes in explanation graph should be connected by some path");
            self.explain_along_path(a, c);
            self.explain_along_path(b, c);
        }
    }

    fn done(self) -> Vec<Equation> {
        self.explanation
    }

    fn explain_along_path(&mut self, a: Const, c: Const) {
        let mut a = self.highest_node(a);

        while a != c {
            let (parent, reason) = self.parent(a).expect("we should always find c before running out of parents, since c is an ancestor of a");

            match reason {
                PendingEq::Constants(eq) => self.explanation.push(Equation::Constants(true, eq)),
                PendingEq::Application(eq1, eq2) => {
                    self.explanation.push(Equation::Application(eq1));
                    self.explanation.push(Equation::Application(eq2));

                    // "Recursively" explain why the arguments to this
                    // application were equal, which is what caused the outputs
                    // of the applications to be unified.
                    let AppEq(App(a1, a2), _) = eq1;
                    let AppEq(App(b1, b2), _) = eq2;
                    self.pending.push((a1, b1));
                    self.pending.push((a2, b2));
                }
            }

            self.union_with_parent(a);
            a = self.highest_node(parent);
        }
    }

    fn representative(&self, c: Const) -> Const {
        self.representatives[c.0]
    }

    fn parent(&self, c: Const) -> Option<(Const, PendingEq)> {
        self.proof_forest[c.0]
    }

    fn class_size(&self, c: Const) -> usize {
        let c = self.representative(c);
        self.members[c.0].len()
    }

    fn highest_node(&self, c: Const) -> Const {
        let c = self.representative(c);
        self.highest_node[c.0]
            .expect("Representative should keep track of the highest node in its class")
    }

    fn collect_ancestors(&self, c: Const) -> Vec<Const> {
        let mut ancestors = Vec::new();

        let mut maybe_current = Some(c);
        while let Some(current) = maybe_current {
            ancestors.push(current);
            maybe_current = self.parent(current).map(|x| x.0);
        }

        ancestors
    }

    fn nearest_common_ancestor(&self, c1: Const, c2: Const) -> Option<Const> {
        let ancestors_c1 = self.collect_ancestors(c1);

        let mut ancestors_c2 = vec![false; self.proof_forest.len()];
        for a2 in self.collect_ancestors(c2) {
            ancestors_c2[a2.0] = true;
        }

        for a1 in ancestors_c1 {
            if ancestors_c2[a1.0] {
                return Some(a1);
            }
        }

        return None;
    }

    fn union_classes(&mut self, a: Const, b: Const, highest_node: Const) {
        let a = self.representative(a);
        let b = self.representative(b);

        let (a, b) = if self.class_size(a) > self.class_size(b) {
            (b, a)
        } else {
            (a, b)
        };

        // Move members from a to b
        let members_a = mem::replace(&mut self.members[a.0], Vec::new());
        for &m in &members_a {
            self.representatives[m.0] = b;
            self.members[b.0].push(m);
        }

        self.highest_node[a.0] = None;
        self.highest_node[b.0] = Some(highest_node);
    }

    fn union_with_parent(&mut self, child: Const) {
        let (parent, _) = self
            .parent(child)
            .expect("union_with_parent should only be called on nodes that have parents");
        let highest_of_parent = self.highest_node(parent);

        self.union_classes(child, parent, highest_of_parent);
    }
}
