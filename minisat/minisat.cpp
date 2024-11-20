// MiniSAT implementation[0]
// http://minisat.se/downloads/MiniSat.pdf
// Key CDCL loop: Solver->analyze(), Solver->record()
#include "minisat.h"
#include <algorithm>
#include <iostream>
#include "dimacs.h"

// Section 3: Overview of SAT solver
// - Assumptions are then canceled by backtracking **until the conflict clause becomes unit**,
//   from which point the unit clause is propagated and the search continues.
//
// Section 3: Propagation
// - Two unbound literals p and q of the clause are therefore selected, and references to the clause
//   are added to !p and !q.
// - As soon as a watched literal becomes true, the constraint is invoked to see if info can be propagated,
//   or to select new unbound literals to be watched.
//
// - On backtracking, no adjustment to the watcher lists needs to be done.
//   MiniSAT supports optional undo lists, storing what constraints need to be updated when a variable becomes
//   unbound by backtracking.
//
//
// Section 3: Learning
// - The conflicting constraint is asked for a set of variable assignments that make it contradictory.
//   For a clause, it would be all literals of the clause.
// - Each of the variable assignments returned must be an assumption of the searc proecedure, or a propagation of some constraint.
// - The propagating constraints are in turn asked for their variable assignments.
// - This is done until some termination condition is fulfilled.
// - A clause prohibiting this assignment is added to the clause DB.
// - This learnt clause must be implied by the original problem constraints.
// - Learnt clauses serve two purposes: First, they drive backtracking, and second, they speed up future conflicts by caching the reason
//   for the conflict.
//  Section 3: SEarch
//  - Starts by selecting an unassigned variable x (decision variable) and assume it to be TRUE.
//  - The consequences are propagated.
//  - All variables assigned as a consequence of `x` are from the same decision level.
//  - All assignments are stored on a stack (the trail).
//  - Trail is divided into decision levels, and is used to undo information for backtracking.
//  - Decision phase will continue until either all variables are assigned (We have a model),
//  - ... or we find a cex (in which case we learn a conflict clause).
//  - We now undo assignments to the conflict clause, until the conflict clause becomes unit.
//  - If we can remove multiple assignments and have the conflict clause stay unit, then we do so
//    until we get to the lowest level (backjumping / non-chronological backtracking) [MS96].
//
//  Section 3: Cosntraint Removal
//  - Problem constraints can be removed at the top-level, and simplifyDB does this.
//  -
//
//
//  4.2 Constraints API
//
//  #### Remove
//  supplant destructor, receiving solver state as a parameter.
//
//  #### Proapgate: called if constraint is foud in the watcher list during propgation ofunit info of p.
//  - Constraint is **removed from** watch list, is required to insert itself into a new or same watcher list.
//  - Any unit information is derivable as a consequence of p should be enqueued.
//  - If successful, TRUE is returned.
//  - If a conflict is detected, FALSE is retuendd.
//
//  #### Simplify
//  - At the top-level, constraint can simplify its representation (return false), or
//  - state that it is satisfied and can be removed (return true).
//  - Constraint must *not* be simplifiable to produce unit information, or to be conflicting.
//    In that case, propagation has not been correctly defined.
//
// #### Undo
//  - During backtracking, called if constraint was added to to the undo list of var(p) in propagate.
//
// #### Calculate Reason
// - Given a literal p and an empty vector.
// - Constraint is the reason for p being true.
// - That is, during propagation, we enqueued p.
// - The received vector is extended to include a set of assignments (represented as literals) implying p.
// - The currnet variable assignments are guaranteed to be identical to that of the moment before the constraint
//   propagated p.
// - The literal p is allowed to be the special bottom_lit, in which case the reason for conflicting should be returned.
//   (WTF).
//
//
//
//
//  Key takeaways
//  -------------
//
//  If we have clause [p, q]
//    - then we watch !p, !q
//    - because when !p = T, we will be propagated, soknow that p = F, so we are then unit and we can propagate q.
//    - Why don't we watch p? unclear!
//    - Why breadth first search succesfully computes dominators in UIP:
//      [MSS94] J. P. Marques-Silva and K. A. Sakallah. Dynamic search-space pruning techniques in path sensitization. In
//

using namespace std;
using var = int;


template<typename T>
void vectorRemoveElem(T elem, vector<T> &vs) {
  auto it = std::find(vs.begin(), vs.end(), elem);
  assert(it != vs.end());
  using std::swap;
  // swap the one to be removed with the last element
  // and remove the item at the end of the container.
  swap(*it, vs.back());
  vs.pop_back();
}

template<typename T>
void vectorSetSize(vector<T> &vs, int size) {
  assert(vs.size() <= size);
  vs.resize(size);
  vs.shrink_to_fit();
}

lit lit::neg() {
  return lit(this->x, !this->pos);
}

lit lit::lbot() { return lit(); }
bool lit::sign() const { return !this->pos; }
int lit::var() const { assert (this->x >= 0); return this->x; }
int lit::index() const { return 2 * this->x + this->pos; }

bool lit::operator == (const lit &other) const {
  return this->x == other.x && this->pos == other.pos;
}

bool lit::operator != (const lit &other) const {
  return !(*this == other);
}

// == lbool ==

lbool::lbool(bool b) {
  if (b) {
    this->val = kind::t;
  } else {
    this->val = kind::f;
  }
}

bool lbool::is_true() const {
  return this->val == kind::t;
}

bool lbool::is_bot() const {
  return this->val == kind::bot;
}

bool lbool::is_false() const {
  return this->val == kind::f;
}


lbool lbool::neg() {
  if (this->val == kind::bot) {
    return lbool();
  } else if (this->val == kind::t) {
    return lbool(true);
  } else {
    assert(this->val == kind::f);
    return lbool(false);
  }
}

bool lbool::operator == (const lbool &other) const {
  return other.val == this->val;
}

lbool lbot() {
  lbool b;
  b.val = lbool::kind::bot;
  return b;
}



bool Clause::Clause_new(Solver *S, vector<lit> &ps, bool learnt, Clause **out) {
  // bollu TODO: assert lits[0] and lits[i] invariant for learnt clauses.
  *out = nullptr;
  // minisat: normalize clause
  // bollu TODO: convert this to vector<bool> with indexing literals.
  std::set<lit> var2sign;
  if (!learnt) {
    vector<lit> pruned_ps;
    for (lit p : ps) {
      if (S->value(p).is_true()) {
        return true;
      }
      // we have p, !p in clause. quit.
      if (var2sign.find(p.neg()) != var2sign.end()) {
        return true;
      };
      if (var2sign.find(p) != var2sign.end()) {
        // duplicate.
        continue;
      }
      // push back this literal.
      pruned_ps.push_back(p);
    }
    ps = pruned_ps;
  }

  // empty clause, return false indicating conflict.
  if (ps.size() == 0) {
    return false;
  } else if (ps.size() == 1) {
    // minisat: unit clause, enqueue propagation.
    return S->enqueue(ps[0]);
  } else {
    // nontrivial clause.
    Clause *c = new Clause;
    // bollu TODO: use std::move.
    c->lits = ps;
    c->learnt = learnt;
    c->activity = 0; //minisat: only relevant for learnt clauses.

    if (learnt) {
      // pick a good second literal to watch, so move sth to lits[1].
      // max_i = index of literal with highest decision level.
      assert(c->lits.size() > 0);
      int max_i = 0; double max_activity = S->activity[c->lits[0].index()];
      for (int i = 1; i < c->lits.size(); ++i) {
        double a = S->activity[c->lits[i].index()];
        if (a >= max_activity) {
          max_i = i;
          max_activity = a;
        }
      }
      // bollu: make the second literal the one with highest activity.
      c->lits[1] = ps[max_i];
      c->lits[max_i] = ps[1];

      S->claBumpActivity(c);
      for(int i = 0; i < ps.size(); ++i) {
        S->varBumpActivity(ps[i].var());
      }
    }
    // bollu: watch for !p, !q, as explained above.
    // when p = F, ie, when !p = T, we know that we may have an opportunity to propagate.
    // minisat: add clause to watcher lists.
    S->watches[c->lits[0].neg().index()].push_back(c);
    S->watches[c->lits[1].neg().index()].push_back(c);
    *out = c;
    return true;
  }
};

bool Clause::locked(Solver *S) {
  assert(this->learnt);
  return S->reason[this->lits[0].var()] == this;
}

void Clause::remove(Solver *S) {
  // fig 7
  // TODO(bollu): why are we not the *negated* watch list?
  vectorRemoveElem((Constr *)(this), S->watches[lits[0].neg().index()]);
  vectorRemoveElem((Constr *)(this), S->watches[lits[1].neg().index()]);
  delete this; // WTF?
}

// invariant: only called at toplevel with empty propagation queue.
bool Clause::simplify(Solver *S) {
  assert(S->propQ.size() == 0);
  assert (S->decisionLevel() == 0);
  int j = 0;
  for(int i = 0; i < this->lits.size(); ++i) {
    if (S->value(i).is_true()) {
      return true;
    } else if (S->value(i).is_bot()) {
      // unassigned literals are coped over.
      // ergo, false literals are not copied. clever.
      lits[j++] = lits[i];
    }
    else {
      assert(S->value(i).is_false());
      // ergo, false literals are not copied. clever.
    }
  }
  vectorSetSize(lits, j);
  return false;
}

bool Clause::propagate(Solver *S, lit p) {
  // bollu: invariant: Clause was on p's watch list, so p contains clause.

  // minisat: make sure the false literal is lits[1]
  //
  // rearrange the list such that we are woken up by lits[1].
  // This maintains the invariant below that lits[0] is the unknown literal
  // whose state we need to determine, now that we have been woken up on lits[1].
  if (lits[0] == p.neg()) {
    // we are now down to a single literal that is being watched,
    // since we know that lits[0] = F, so we will trigger when lits[1] = T.
    lits[0] = lits[1];
    lits[1] = p.neg();
  }
  assert(lits[1] == p.neg());
  // bollu: invariant: lits[0] is the literal we may have to propagate.
  // bollu: lits[0] cannot be false, since we would have been woken up to this.
  assert(S->value(lits[0] != false);

  // minisat: if 0th watch is true, this clause is SAT.
  if (S->value(lits[0]) == true) {
    // bollu:  minisat: re-insert clause into watcher list.
    // bollu:  we know that lits[0] is true, so we are SAT.
    // bollu:  We have been removed from the watcher list (as MiniSAT algo always removes clauses from the watchers list,
    // bollu:  it is their responsilibity to put themselves back),
    // bollu:  so we put ourselves back on it.
    S->watches[p.index()].push_back(this);
    return true;
  }

  // bollu:  Recall: we were woken up on lits[1].
  // bollu:  We cannot have lits[0] == false, because we would have been woken up on this.
  // bollu:  We also established that it is not true, so it must be bot.
  assert(S->value(lits[0]).is_bot());

  // minisat: look for a new literal to watch.
  for(int i = 0; i < lits.size(); ++i) {
    // it is either bottom [unassigned] or true
    if (S->value(lits[i]) != false) {
      // bollu:  swap with lits[i]
      lits[1] = lits[i];
      lits[i] = p.neg(); // pick the first literal whose value is not false, move it to lits[1].
      // we choose this literal to watch.
      S->watches[lits[1].neg().index()].push_back(this);
      return true;
    }
  }
  // bollu: we could find another literal to watch, which means that all other literals were false!
  // Thus, clause is unit under assignment, so we propagate.
  // minisat: Clause is unit under assignment
  S->watches[p.index()].push_back(this);
  // bollu:  enqueue lits[0] to be propagated.
  return S->enqueue(lits[0], this);
}

// minisat:
// invariant: p == bot || p == lits[0]
// if p = bot, then we must calculate reason for conflict.
// if p = lits[0] (i.e., we propagated this literal, and we are asked what made it true).
void Clause::calcReason(Solver *S, lit p, std::vector<lit> *out_reason) {
  assert((p == lit::lbot()) || p == lits[0]);
  assert(out_reason);
  assert(out_reason->size() == 0);
  // bollu: the reason for conflict is the entire clause.
  // bollu: the reason for lits[0] being true is that every other lit was false!
  const int start = p == lit::lbot() ? 0 : 1;
  for(int i = start; i < this->lits.size(); ++i) {
    // invariant: s.value(lits[i]) == false
    assert(S->value(lits[i]) == false);
    (*out_reason).push_back(lits[i].neg());
  }

  if (this->learnt) {
    // bollu: bump activity of clause involved in either direct conflict,
    // or propagation that led to conflict.
    S->claBumpActivity(this);
  }
}


var Solver::newVar() {
  const int index = nVars();
  watches.push_back({});
  watches.push_back({});
  undos.push_back({});
  reason.push_back(nullptr);
  assigns.push_back(lbool());
  level.push_back(-1);
  activity.push_back(0);
  order.newVar(index);
  return index;
}

bool Solver::addClause(vector<lit> literals) {
  // TODO: bollu's code.
  Clause *out = nullptr;
  Clause::Clause_new(this, literals, false,  &out);
  if (!out) {
    return false;
  } else {
    constrs.push_back(out);
    return true;
  }
}

// Fig 9:
// minisat: propagates all enqueued facts. if a conflict arises, then the conflicting clause is returned.
// bollu: propagate and return a conflicting constraint. This is the DPLL UP loop.
Constr *Solver::propagate() {
  while (propQ.size() > 0) {
    lit p = propQ.front(); // p is the fact to propagate
    propQ.pop();
    vector<Constr *> tmp; // new watchers for p.
    vector<Constr *> &pwatches = watches[p.index()];
    std::copy(tmp.end(), pwatches.begin(), pwatches.end());

    for (int i = 0; i < tmp.size(); ++i) {
      // bollu: tmp[i] is **conflicting**.
      // bollu: copy remaining watches and return the constraint.
      if (!tmp[i]->propagate(this, p)) {
        // bollu: push all clauses left over from `pWatches`.
        for(int j = i + 1; j < tmp.size(); ++i) { pwatches.push_back(tmp[j]); }
        // bollu: stop propagation because we detected conflict.
        propQ = std::queue<lit>();
        return tmp[i];
      }
    }
  }
  return nullptr;
}

// Fig 9
// minisat: puts a new fact onto prop Q, as well as immediately updating the variable's
// assignment vector. If a conflict arises, false is returned and the propogatinon queue is cleared.
bool Solver::enqueue(lit p, Constr *from) {
  // model has value for `p`.
  if (!this->value(p).is_bot()) {
    if (this->value(p) == false) {
      // minisat: conflicting enqueued assignment
      return false;
    } else {
      // existing consistent assignment, don't enqueue
      return true;
    }
  } else {
    // enqueue a UP.
    assigns [p.var()] = lbool(!p.sign());
    level [p.var()] = this->decisionLevel();
    reason [p.var()] = from;
    trail.push_back(p);
    propQ.push(p);
    return true;
  }
}

// minisat: analyze a conflict and produce a reason clause.
// preconditions:
//   (1) out_learnt is assumed to be cleared.
//   (2) current decision level must be greater than root level.
// bollu: Key CDCL loop here!
// TODO(bollu): why does this ensure that *out_learnt is a unit clause? AFAICT, after backtracking, it isn't a unit clause at all!
// TODO(bollu): is it because we effectively only backtrack upto "one decision"?
void Solver::analyze(Constr *confl, vector<lit> *out_learnt, int *out_btlevel) {
  assert(out_learnt);
  assert(out_learnt->size() == 0);
  assert(decisionLevel() > 0);

  vector<bool> seen(nVars(), false);
  // minisat: int counter = 0;
  int counter_nof_unit_propagations_to_p = 0; // number of unit propagations that led to p being assigned.
  // bollu:  TODO: what the heck is bottom lit?
  // bollu:  Recall the API For calcReason(), the bottom literal indicates that we want to analyze the conflict itself.
  lit p = lit::lbot();
  out_learnt->push_back(lit::lbot()); // minisat: leave room for asserting literal.
  *out_btlevel = 0;

  do {
    vector<lit> p_reason;
    assert(confl != nullptr); // minisat: invariant that confl != null.
    // bollu: calculate reason for conflict. Start by calculating how we got conflict, then implicants for conflict.
    confl->calcReason(this, p, &p_reason);

    // minisat: trace reason for p
    for(lit q : p_reason) {
      if (!seen[q.var()]) {
        seen[q.var()] = true; // bollu: BFS.
        // bollu: this is from current decision level
        if (level[q.var()] == decisionLevel()) {
          // the assignment of `q` came from the same decision level as `p`, so it came from unit proagations!
          // We can definitely undo this variable.
          counter_nof_unit_propagations_to_p++;
        }
        else if (level[q.var()] > 0) {
          // bollu: this is from a previos decision level, so add it in.
          // But do not add stuff from the current decision level -_^

          // minisat: exclude variables from decision level 0.
          // we know that (q0 /\ q1 /\... qn) led to False.
          // We negate this clause, and add it as a conflict clause that we learn,
          // which gives us (!q0 \/ !q1 \/ !q2 ... \/ !qn), so we negate the qs.
          out_learnt->push_back(q.neg());
          *out_btlevel = std::max<int>(*out_btlevel, level[q.var()]);
        }
      }
    }

    // minisat: select next lieral to look at.
    do {
      assert (this->trail.size() > 0);
      p = this->trail.back();
      confl = reason[p.var()];
      undoOne();
    } while(!seen[p.var()]);
    counter_nof_unit_propagations_to_p--;
  } while (counter_nof_unit_propagations_to_p > 0); // backtrack all the unit propagations that led to p.

  // bollu: we add a clause whose lits[0] is from the out_btlevel.
  assert(level[p.var()] == *out_btlevel);
  // TODO(bollu): why is this a unit clause? that's pretty unclear to me!
  // TODO(bollu): does this really work?
  // hurray, we found a *decision* that led to p!
  // We negate this decision, since this clause will
  (*out_learnt)[0] = p.neg();
}

// minisat: record a clause and drive backtracking.
// precodntion: clause[0] contains the asserting literal.
// precodnition: clause must not be empty.
void Solver::record(vector<lit> clause) {
  assert(clause.size() > 0);
  Clause *c = nullptr; // minisat: will be set to created clause, or nullptr if c is unit.
  Clause::Clause_new(this, clause, true, &c);
  // bollu(TODO): do we know that clause[1]...clause[n] are false? I really don't see why this is the case!
  enqueue(clause[0], c);
  if (c != nullptr) {
    learnts.push_back(c);
  }
}

// Fig 12
// minisat: unbinds the last variable on the trail.
void Solver::undoOne() {
  assert (trail.size() > 0);
  lit p = trail.back();
  var x = p.var();
  assigns[x] = lbot();
  reason[x] = nullptr;
  level[x] = -1;
  order.undo(x);
  trail.pop_back();

  // TODO(bollu): why does each variable have a LIST of undos?
  while(undos[x].size() > 0) {
    undos[x].back()->undo(this, p);
    undos[x].pop_back();
  }
}

// Fig 12
// minisat: return false if immediate conflict.
bool Solver::assume(lit p) {
  trail_lim.push_back(trail.size());
  return enqueue(p);
}

// Fig 12
// minisat: revert state to before push_back().
void Solver::cancel() {
  assert (trail_lim.size() > 0);
  int c = trail.size() - trail_lim.back();
  // bollu: repeated undo vars on the trail.
  for (; c != 0; c--) {
    undoOne();
  }
  trail_lim.pop_back();
}

// Fig 12
// minisat: pop several levels of assmptions.
// after retruning, we will have decisionLevel() <= level,
// and hopefully, decisionLevel() == level.
void Solver::cancelUntil(int level) {
  while(decisionLevel() > level) {
    cancel();
  }
}

// Fig 13
// minisat: Search method. Assumes and propagates until a conflict is found,
// from which a conflict clause is learnt and backtracking performed
// until search can continue.
// Precondition: root_level == decisionLevel()
lbool Solver::search(int nof_conflicts, int nof_learnts, SearchParams params) {
  assert(root_level == decisionLevel());
  int conflictC = 0;
  var_decay = 1.0 / params.var_decay;
  cla_decay = 1.0 / params.cla_decay;
  model.clear();

  while (true) {
    Constr *confl = this->propagate();
    if (confl != nullptr) {
      // minisat: CONFLICT
      conflictC++;
      Vec<lit> learnt_clause;
      int backtrack_level = -1;
      if (decisionLevel() == root_level) {
        return false;
      }
      this->analyze(confl, &learnt_clause, &backtrack_level);
      this->cancelUntil(max(backtrack_level, root_level));
      this->record(learnt_clause); // bollu: this enqueues learnt_clause[0], which it assumes to be unit! why?
      decayActivities();

    } else {
      // minisat: no conflict
      if (decisionLevel() == 0) {
        // minisat: simplify the set of problem clauses
        simplifyDB();
        if (learnts.size() - nAssigns() >= nof_learnts) {
          // minisat: reduce the number of learnt clauses
          reduceDB();
        }
      }

      if (nAssigns() == nVars()) {
        // minisat: model found
        model.reserve(nVars());
        for(int i = 0; i < nVars(); ++i) {
          assert(!value(i).is_bot()); // bollu
          model[i] = value(i).is_true();
        }
        cancelUntil(root_level); // bollu: undo till root level
        return lbool(true);
      }
      else if (conflictC >= nof_conflicts) {
        cancelUntil(root_level); // bollu: undo till root level
        return lbool();
      } else {
        // minisat: new variable decision.
        lit p = lit(order.select(), false); // minisat: may have heuristic for polarity
                                            // bollu TODO: why can't this return false?
        const bool out = assume(p); // minisat: cannot return false.
        assert(!out);

      }
    }
  }
}


// fig 14
void Solver::varBumpActivity(var x) {
  activity[x] += var_inc;
  if (activity[x] > DOUBLE_REPR_LIMIT) {
    varRescaleActivity();
  }
  order.update(x);
}

// fig 14
void Solver::claBumpActivity(Clause *c) {
  c->activity += cla_inc;
  if (c->activity > DOUBLE_REPR_LIMIT) {
    claRescaleActivity();
  }
  // TODO: analogue of order.update(x)?
}

// fig 14
void Solver::varDecayActivity() {
  var_inc *= var_decay;
}

// fig 14
void Solver::claDecayActivity() {
  cla_inc *= cla_decay;
}


// fig 14
void Solver::varRescaleActivity() {
  for(int i = 0; i < nVars(); ++i) {
    activity[i] /= DOUBLE_REPR_LIMIT;
  }
  var_inc /= DOUBLE_REPR_LIMIT;
}

// fig 14
void Solver::claRescaleActivity() {
  for(int i = 0; i < learnts.size(); ++i) {
    activity[i] /= DOUBLE_REPR_LIMIT;
  }
  cla_inc /= DOUBLE_REPR_LIMIT;
}


// fig 14
void Solver::decayActivities() {
  varDecayActivity();
  claDecayActivity();
}

// fig 15
// remove half of the learnt clauses, but not (some) locked clauses.
// Clauses below a certain lower bound of activity are also removed.
void Solver::reduceDB() {
  int i = 0; // i: iterator over clauses
  int j = 0; // j: iterator over learnts that overwrites data.
  const double lim = cla_inc / learnts.size();
  for(; i < learnts.size() / 2; ++i) {
    if (!learnts[i]->locked(this)) {
      learnts[i]->remove(this);
    } else {
      learnts[j++] = learnts[i];
    }
  }
  for (; i < learnts.size(); ++i) {
    if (!learnts[i]->locked(this) && learnts[i]->activity < lim) {
      learnts[i]->remove(this);
    } else {
      learnts[j++] = learnts[i];
    }
  }
  vectorSetSize(learnts, j);
}

// fig 15:
// top-level simplify of constraint database.
// will remove any satisfied constraint, and simplify remaining constraints
// under current (partial) assignment.
// If top-level conflict is found, return false.
// pre-condition: decision level must be zero.
// post-condition: propgation queue is empty
bool Solver::simplifyDB() {
  if (propagate() != nullptr) { return false; }
  assert(propQ.size() == 0);

  {
    int j = 0;
    for(int i = 0; i < learnts.size(); ++i) {
      // TODO: check if this is okay.
      if (learnts[i]->simplify(this)) {
        learnts[i]->remove(this);
      } else {
        learnts[j++] = learnts[i];
      }
    }
  }

  {
    int j = 0;
    for(int i = 0; i < constrs.size(); ++i) {
      // TODO: check if this is okay.
      if (constrs[i]->simplify(this)) {
        constrs[i]->remove(this);
      } else {
        constrs[j++] = constrs[i];
      }
    }
  }
  return true;
}

// Fib 16
// Main solve method.
// pre-conditions: if assumptions are used, simplifyDB() must be called.
bool Solver::solve(std::vector<lit> assumptions) {
  if (assumptions.size() > 0) {
    std::cout << "using assumptions. Have you called simplifyDB()?\n";
  }

  SearchParams params(0.95, 0.999);
  double nof_conflicts = 100;
  double nof_learnts = nConstraints()/3;
  lbool status;

  // push incremental assumptions.
  for(int i = 0; i < assumptions.size(); ++i) {
    if (!assume(assumptions[i]) || propagate() != nullptr) {
      cancelUntil(0);
      return false;
    }
  }

  // set current root level.
  root_level = decisionLevel();
  while (status.is_bot()) {
    status = search(nof_conflicts, nof_learnts, params);
    nof_conflicts *= 1.5;
    nof_learnts *= 1.5;
  }
  cancelUntil(0);
  return status == true;
}

void VarOrder::newVar(var x) {
  std::push_heap(this->heap.begin(), this->heap.end(), [this](var x, var y) {
      // need to return if x < y, and the actual impl is a min-heap
      return (this->activity[x] > this->activity[y]);
    });
}

void VarOrder::update(var x) {
  // bollu(TODO): what is the expected semantics of update/undo? totally opaque to me...
  this->newVar(x); // bollu(TODO): check if this does the right thing.
}


void VarOrder::updateAll() {
  std::make_heap(this->heap.begin(), this->heap.end(), [this](var x, var y) {
      // need to return if x < y, and the actual impl is a min-heap
      return (this->activity[x] > this->activity[y]);
    });
}

void VarOrder::undo(var x) {
  this->activity[x] = -1;
}

var VarOrder::select() {
  assert(heap.size() > 0);
  return *heap.begin();
}

int main() {
  return 0;
}

