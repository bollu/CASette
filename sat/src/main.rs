use std::collections::HashMap;
use std::collections::HashSet;
#[derive(Clone, Copy, Eq, Hash, PartialEq)]
struct Atom(usize);

#[derive(Clone, Copy, Eq, Hash, PartialEq)]
struct Lit {
    atom : Atom,
    neg : bool,
}
impl Lit {
    fn from_val(atom : Atom, val : bool) -> Lit {
        Lit {
            atom,
            neg : if val { false } else { true }
        }
    }
    fn sat_value(&self) -> bool {
        return true ^ self.neg;
    }
}
#[derive(Clone, Eq, Hash, PartialEq)]
struct Clause(Vec<Lit>);

// TODO: figure out how to overload iterator()
// impl IntoIterator for Clause {
//     type Item = Lit;
//     type IntoIter = Vec<Lit>::Iter;
//     fn into_iter(&self) -> Vec<Lit>::iterator {
//         self.0.iter()
//     }
// }
//
// impl Clause {
//     fn iter(&self) -> Vec<Lit>::iterator {
//         return self.0.iter()
//     }
// }

#[derive(Copy, Clone)]
struct ClauseId(usize);

#[derive(Copy, Clone)]
struct Level(i32);

impl Level {
    fn toplevel() -> Level {
        Level(-1)
    }
    fn is_toplevel(&self) -> bool {
        return self.0 == -1
    }
    fn incr(&self) -> Level {
        return Level(self.0 + 1)
    }
}


#[derive(Clone)]
struct Model(HashMap<Atom, bool>);

impl Model {
    fn new() -> Model {
        Model(HashMap::new())
    }
    fn eval_atom (&self, atom : Atom) -> Option<bool> {
        self.0.get(&atom).copied()
    }
    fn is_atom_assigned(&self, atom : Atom) -> bool {
        self.0.get(&atom).is_some()
    }

    fn eval_lit(&self, lit : Lit) -> Option<bool> {
        self.eval_atom(lit.atom).map (|v| v ^ lit.neg)
    }
    fn is_literal_assigned(&self, lit : &Lit) -> bool {
        self.0.get(&lit.atom).is_some()
    }
    fn assign_atom(&mut self, atom : Atom, val : bool) {
        self.0.insert(atom, val);
    }

    fn assign_lit(&mut self, lit : Lit) {
        self.assign_atom(lit.atom, true ^ lit.neg);
    }

    fn eval_clause(&self, clause : Clause) -> Option<bool> {
        for lit in clause.0.iter() {
            if let Some(v) = self.eval_lit(*lit) {
                if !v {
                    return Some(false);
                }
            } else {
                return None;
            }
        }
        return Some(true);
    }
    // given a clause, return a unit literal
    fn get_unit_from_clause(&self, clause : &Clause) -> Option<Lit> {
        let mut unassigned : Option<Lit> = None;
        for lit in clause.0.iter() {
            // literal is unassigned
            if !self.is_literal_assigned(lit) {
                // there's no other unassigned value.
                if unassigned.is_none() {
                    unassigned = Some(*lit)
                } else {
                    return None;
                }
            }
        }
        return unassigned;
    }
    // given a clause, return a unit literal
    fn unassigned_atom_from_clause(&self, clause : &Clause) -> Option<Atom> {
        for lit in clause.0.iter() {
            // literal is unassigned
            if !self.is_literal_assigned(lit) {
                return Some(lit.atom);
            }
        }
        return None;
    }

    fn unassigned_atom_from_clauses(&self, clauses : &Vec<Clause>) -> Option<Atom> {
        for c in clauses {
            if let Some(atom) = self.unassigned_atom_from_clause(c) {
                return Some(atom);
            }
        }
        return None;
    }

}

#[derive(PartialEq, Eq, Clone)]
enum DecisionKind {
    Bcp,
    Conflict,
    Decision
}

#[derive(Clone)]
struct Decision {
    kind : DecisionKind,
    atom : Atom,
    level : Level,
    clause_id : Option<ClauseId>,
    // TODO: use a persistent data structure to make this cheap.
    model : Model,
    // tried_false : HashSet<Atom>,
}

// Definition 2.3 (state of a clause under an assignment). A clause is satisfied if one or more of its literals are satisfied (see Definition 1.12), con- flicting if all of its literals are assigned but not satisfied, unit if it is not satisfied and all but one of its literals are assigned, and unresolved other- wise.


enum Resolution {
    // resolve on atom
    Branch(Atom, Box<Resolution>, Box<Resolution>),
    Root(ClauseId),
}
// resolution proof
enum DPLLResult {
    Unsat(),
    Sat(Model),
}

// context for DPLL
struct DPLLCtx {
    clauses : Vec<Clause>,
    decision_stack: Vec<Decision>, // decision_stack of decsions / bcp done so far.
    // for each atom, how many times we have assigned to it.
    // if atom is not present, then it's never been assigned to.
    // if atom is present, then it's assigned once(with the given value),
    // or both times.
}

impl DPLLCtx {
    fn new(clauses : Vec<Clause>) -> DPLLCtx {
        DPLLCtx {
            decision_stack : Vec::new(),
            clauses,
        }
    }
    // return true if any variable was assigned, and false if not.
    fn decide(&mut self) -> bool {
        let mut model = self.model();
        let Some(atom) = model.unassigned_atom_from_clauses(&self.clauses) else { return false };

        // let val = self.tried_false().contains(&atom);
        // let mut tried_false = self.tried_false().clone();
        // tried_false.insert(atom);
        model.assign_atom(atom, false);

        self.decision_stack.push(Decision {
            kind : DecisionKind::Decision,
            level : self.level().incr(),
            atom,
            clause_id : None,
            model,
            // tried_false : self.tried_false()
        });
        true
    }

    fn model(&self) -> Model {
        match self.decision_stack.last() {
            Some(dec) => dec.model.clone(),
            None => Model::new()
        }
    }

    fn level(&self) -> Level {
        match self.decision_stack.last() {
            Some(dec) => dec.level,
            None => Level::toplevel()
        }
    }

    // fn tried_false(&self) -> HashSet<Atom> {
    //     match self.decision_stack.last() {
    //         Some(dec) => dec.tried_false.clone(),
    //         None => HashSet::new(),
    //     }
    // }

    // pushes nodes into the decision stack.
    fn bcp(&mut self) {
        let mut changed = true;
        while changed {
            changed = false;
            // get all units
            let cs = self.clauses.clone(); // WTf, this is crazy. How do I avoid this, and make this a move?
            for (i, c) in cs.iter().enumerate() {
                let clause_id = ClauseId(i);
                let Some(lit) = self.model().get_unit_from_clause(c) else {
                    continue;
                };
                // model already has literal.
                match self.model().eval_lit(lit) {
                    Some(v) => {
                        // model disagrees with our value
                        if v != lit.sat_value() {
                            self.decision_stack.push(Decision {
                                atom : lit.atom,
                                level : self.level(),
                                clause_id : Some(clause_id),
                                kind : DecisionKind::Conflict,
                                model : self.model(),
                                // tried_false : self.tried_false(),
                            });
                            return;
                        }
                    }
                    None => {
                        let mut model = self.model();
                        model.assign_lit(lit);
                        self.decision_stack.push(Decision {
                            atom : lit.atom,
                            level : self.level(),
                            clause_id : Some(clause_id),
                            model : self.model(),
                            kind : DecisionKind::Bcp,
                            // tried_false : self.tried_false(),
                        });
                    }
                }
            }
        }
    }

    fn resolve_conflict(&mut self) -> bool {
        while let Some(mut dec) = self.decision_stack.pop() {
            // not a decision
            if dec.kind != DecisionKind::Decision { continue; }
            // model must have value.
            let val = dec.model.eval_atom(dec.atom).unwrap();
            if val {
                // continue unwinding, since we have tried both F, T.
                continue;
            }
            // assign the model T.
            dec.model.assign_atom(dec.atom, true);

        }
        false
    }

    fn dpll(&mut self) -> DPLLResult {
        loop {
            // BCP, keep performing BCP and analyzing the conflict
            // as long as we keep getting conflicts.
            loop {
                self.bcp();
                // we have a conflict, gotta resolve.
                if let Some(Decision { kind : DecisionKind::Conflict, .. }) = self.decision_stack.last() {
                    // backtrack, looking for the previous decision level that we have not tried
                    // both ways. IF none exists, then we are UNSAT, and thus, build a RUP proof.
                    // resolveConflict() from CHAFF
                    // most recent decision "not tried both ways" -_^
                    if ! self.resolve_conflict() { // failed to resolve conflicts
                        return DPLLResult::Unsat();

                    }
                } else {
                    // no conflicts, stop BCP.
                    break;
                }
            }

            // Decide on atom.
            if !self.decide() {
                return DPLLResult::Sat(self.model().clone())
            }

        }
    }
}
fn main() {
    println!("Hello, world!");
}
