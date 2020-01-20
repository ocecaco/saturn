use crate::assignment::Assignment;
use crate::types::Var;
use crate::util::VarMap;

pub struct VarOrder {
    activities: VarMap<f64>,
    act_inc: f64,
    act_decay: f64,
}

impl VarOrder {
    pub fn new(act_inc: f64, act_decay: f64) -> Self {
        VarOrder {
            activities: Vec::new(),
            act_inc,
            act_decay,
        }
    }

    pub fn new_var(&mut self) {
        self.activities.push(0.0);
    }

    fn rescale_activities(&mut self) {
        for act in &mut self.activities {
            *act *= 1e-100;
        }

        self.act_inc *= 1e-100;
    }

    pub fn decay_activities(&mut self) {
        self.act_inc /= self.act_decay;
    }

    pub fn bump_activity(&mut self, v: Var) {
        self.activities[v.0] += self.act_inc;

        if self.activities[v.0] > 1e100 {
            self.rescale_activities();
        }
    }

    pub fn pick_next(&self, assignment: &Assignment) -> Var {
        let mut activities = self.activities.iter().enumerate().collect::<Vec<_>>();

        // This comparison will panic on NaNs.
        activities.sort_unstable_by(|(_, act1), (_, act2)| act1.partial_cmp(act2).unwrap());

        // Iterate in reverse order so we go from highest activity to lowest activity
        for &(i, _) in activities.iter().rev() {
            if assignment.var_value(Var(i)).is_none() {
                return Var(i);
            }
        }

        panic!("pick next called with no unassigned variables");
    }
}
