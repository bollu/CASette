// MiniSAT implementation[0]
// http://minisat.se/downloads/MiniSat.pdf
// Key CDCL loop: Solver->analyze()
#include "minisat.h"
#include <algorithm>

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
      // pick a second literal to watch.
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
      // false literals are not copied. clever.
      lits[j++] = lits[i];
    }
  }
  vectorSetSize(lits, j);
  return false;
}

bool Clause::propagate(Solver *S, lit p) {
  // bollu: invariant: p is part of the constraint??

  // minisat: make sure the false literal is lits[1]
  if (lits[0] == p.neg()) {
    // bollu: if lits[0] takes value F, then switch it to lits[1].
    // TODO: where is this invariant used?
    // switch to watching not(p)?
    lits[0] = lits[1];
    lits[1] = p.neg();
  }

  // minisat: if 0th watch is true, this clause is SAT.
  if (S->value(lits[0]) == true) {
    // re-insert clause into watcher list.
    S->watches[p.index()].push_back(this);
    return true;
  }

  // minisat: look for a new literal to watch.
  for(int i = 0; i < lits.size(); ++i) {
    // it is either bottom [unassigned] or true
    if (S->value(lits[i]) != false) {
      lits[1] = lits[i];
      lits[i] = p.neg(); // WTF?
      S->watches[lits[1].neg().index()].push_back(this); // WTF?
      return true;
    }
  }
  // minisat: Clause is unit under assignment
  S->watches[p.index()].push_back(this);
  // enqueue lits[0] to be propagated.
  return S->enqueue(lits[0], this);
}

// minisat:
// invariant: p == bot || p == lits[0]
void Clause::calcReason(Solver *S, lit p, std::vector<lit> *out_reason) {
  assert((p == lit::lbot()) || p == lits[0]);
  assert(out_reason);
  assert(out_reason->size() == 0);
  const int start = p == lit::lbot() ? 0 : 1;
  for(int i = start; i < this->lits.size(); ++i) {
    // invarians: s.value(lits[i]) == false
    assert(S->value(lits[i]) == false);
    (*out_reason).push_back(lits[i].neg());
  }
  if (learnt) {
    // bollu: bump activity of clause involved in conflict.
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
  order.newVar();
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

bool Solver::solve(vector<lit> assumptions) {
  assert(false && "unimplemented");
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
void Solver::analyze(Constr *confl, vector<lit> *out_learnt, int *out_btlevel) {
  assert(out_learnt);
  assert(out_learnt->size() == 0);
  assert(decisionLevel() > 0);

  vector<bool> seen(nVars(), false);
  int counter = 0;
  // bollu TODO: what the heck is bottom lit?
  lit p = lit::lbot();
  vector<lit> p_reason;
  out_learnt->push_back(lit::lbot()); // minisat: leave room for asserting literal.
  *out_btlevel = 0;

  do {
    p_reason.clear();
    assert(confl != nullptr); // minisat: invariant that confl != null.
    confl->calcReason(this, p, &p_reason);

    // minisat: trace reason for p
    for(int j = 0; j < p_reason.size(); ++j) {
      lit q = p_reason[j];
      if (!seen[q.var()]) {
        seen[q.var()] = true;
        // bollu: this is from current decision level
        if (level[q.var()] == decisionLevel()) {
          counter++;
        }
        else if (level[q.var()] > 0) {
          // minisat: exclude variables from decision level 0.
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
    counter--;
  } while (counter > 0);

  // TODO(bollu): does this really work?
  (*out_learnt)[0] = p.neg();
}

// minisat: record a clause and drive backtracking.
// precodntion: clause[0] contains the asserting literal.
// precodnition: clause must not be empty.
void Solver::record(vector<lit> clause) {
  assert(clause.size() > 0);
  Clause *c = nullptr; // minisat: will be set to created clause, or nullptr if c is unit.
  Clause::Clause_new(this, clause, true, &c);
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

int main() {
  return 0;
}

