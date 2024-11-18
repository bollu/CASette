// MiniSAT implementation[0]
// http://minisat.se/downloads/MiniSat.pdf
// Fig 7
// Key CDCL loop: Solver->analyze()
using namespace std;
#include <vector>
#include <queue>
#include <set>
using var = int;

struct Solver;

struct SearchParams {
  double cla_decay;
  double var_decay;
};

struct lit {
  var x;
  bool pos;
  lit (var x, bool pos) : x(x), pos(pos) {
  lit neg() {
    return lit(this->x, !this->pos);
  }
  // WTF is this?
  static lit lbot() {
    x = -1;
    pos = false;
  }
  // it is SIGNED iff it is \overline{x}.
  bool sign() { return !this->pos; }
  int var() { this->var; }
  int index() { return 2 * this->var + this->pos; }

  bool operator == (const lit &other) {
    this->x == other.x && this->pos == other.pos;
  }

  bool operator != (const lit &other) {
    return !(*this == other);
  }
};

struct lbool {
  enum class kind {
    bot = -1
    t = 1,
    f = 0,
  } val;

  explicit lbool() {
    this->val = bot;
  }
  lbool(bool b) {
    if (b) {
      this->val = t;
    } else {
      this->val = f;
    }
  }

  bool is_true() const {
    this->val == t;
  }

  bool is_bot() const {
    this->val == bot;
  }

  bool is_false() const {
    this->val == f;
  }


  lbool neg() {
    if (this->val == bot) {
      return lbool()
    } else if (this->val == t) {
      return lbool(true);
    } else {
      assert(this->val == f);
      return lbool(false);
    }
  }

  bool operator == (const lbool &other) {
    return other.val == this->val;
  }
};

lbool lbot() {
  lbool b;
  b.val = bot;
  return b;
}


// constraints
struct Constr {
  virtual void remove(Solver *S) = 0;
  // return `false` if constraint is conflicting, true otherwise.
  virtual void propagate(Solver *S, lit p) = 0;
  // return `true` is constaint is satisfied.
  virtual bool simplify() { return false; }
  virtual void undo(Solver *S, lit p) {};
  virtual void calcReason(Solver *S, lit p, vector<lit> *outReason) = 0;
};
// figure 7 + 8
struct Clause : public Constr {
  bool learnt;
  float activity;
  vector<lit> lits;

  // implementation in figure 8.
  // minisat: constructor for clauses.
  // return false if toplevel conflict is detected.
  // out_clause maybe set to NULL if the new clause is already satisfied under the current asignment.
  // Post-condition: `ps` is cleared.
  // For learnt clauses, all literals will be false except `lits[0]` [bollu: (x0 \/ !x1 \/ !x2 \/ ... !xn) (i.e. (!(x1 /\ x2 /\ ... /\ xn) => x0))]
  //   this is by design of the analyze() method.
  // For propagation to work, the second watch must be put on the literal that will be first unbound by backtracking.
  // [Note that none of the learnt-clause specific things need to be done for a user defined constraint type).
  static bool Clause_new(Solver *S, vector<lit> &ps, bool learnt, Clause **out) {
    // bollu TODO: assert lits[0] and lits[i] invariant for learnt clauses.
    *out = nullptr;
    // minisat: normalize clause
    // bollu TODO: convert this to vector<bool> with indexing literals.
    std::set<lit> var2sign;
    if (!learnt) {
      vector<lit> pruned_ps;
      for (lit p : ps) {
        if (S->value(p) == true) {
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
      S.enqueue(ps[0]);
    } else {
      // nontrivial clause.
      Clause c = new Clause;
      // bollu TODO: use std::move.
      c.lits = ps;
      c.learnt = learnt;
      c.activity = 0; //minisat: only relevant for learnt clauses.

      if (learnt) {
        // pick a second literal to watch.
        // max_i = index of literal with highest decision level.
        int max_i = 0; double max_activity = s->activity[c.lits[0]];
        for (int i = 1; i < c.lits.size(); ++i) {
          double a = s->activity[c.lits[i]];
          if (a >= max_activity) {
            max_i = i;
            max_activity = a;
          }
        }
        // bollu: make the second literal the one with highest activity.
        c.lits[1] = ps[max_i];
        c.lits[max_i] = ps[1];

        S->claBumpActivity(c);
        for(int i = 0; i < ps.size(); ++i) {
          S->varBumpActivity(ps[i]);
        }
      }
      // minisat: add clause to watcher lists.
      S.watches[c.lits[0].neg().index()].push(c);
      S.watches[c.lits[1].neg().index()].push(c);
      *out_clause = c;
      return true;
    }
  };

  bool locked(Solver *S) {
    assert(this->learnt);
    return S->reason[this->lits[0].var()] == this;
  }

  void remove(Solver *S) {
    // fig 7
    removeElem(this, S.watches[lits[0].neg().index()])
    removeElem(this, S.watches[lits[1].neg().index()]);
    delete this; // WTF?
  }

  // invariant: only called at toplevel with empty propagation queue.
  bool simplify(Solver *S) {
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
    // TODO: do we need this?
    lits.shrink(lits.size() - j);
    return false;
  }

  bool propagate(Solver *S, lit p) {
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
      S->watches[p.index()].push(this);
      return true;
    }

    // minisat: look for a new literal to watch.
    for(int i = 0; i < lits->size(); ++i) {
      // it is either bottom [unassigned] or true
      if (S->value(lits[i]) != false) {
        lits[1] = lits[i];
        lits[i] = p.neg(); // WTF?
        S->watches[lits[1].neg().index()].push(this); // WTF?
        return true;
      }
    }
    // minisat: Clause is unit under assignment
    S->watches(p.index()).push(this);
    // enqueue lits[0] to be propagated.
    return S->enqueue(lits[0], this);
  }

};


struct VarOrder {
  VarOder(vector<lbool> &ref_to_assigns, vector<double> &ref_to_activity) :
    assigns(ref_to_assigns),
    activity(ref_to_activity) {}
  void newVar() ;
  void update(var x);
  void updateAll();
  void undo(var x);
  // select a new unassigned var.
  var select();
  vector<bool> &assigns;
  vector<bool> &activity;

};
struct Solver {
  Solver() : VarOrder(assigns, activity) {}
  var newVar() {
    int index = nVars();
    watches.push({});
    watches.push({});
    undos.push({});
    reason.push(nullptr);
    assigns.push(lbool());
    level.push(-1);
    activity.push(0);
    order.newVar();
  }
  bool addClause(vector<lit> literals);
  bool simplifyDB();
  bool solve(vector<lit> assumptions);
  vector<bool> model;

  int nVars() { return this->assigns.size(); }
  int nAssigns() { return this->trail.size(); }
  int nConstraints() { return this->constrs.size(); }
  int nLearnts() { return this->learnts.size(); }
  lbool value(var x) { return this->assigns[x]; }
  lbool value(lit p) { return p.sign() ? !value(p.var) : value(p.var); }
  int decisionLevel() { return this->trail_lim.size(); }

  // Fig 9:
  // minisat: propagates all enqueued facts. if a conflict arises, then the conflicting clause is returned.
  // bollu: propagate and return a conflicting constraint. This is the DPLL UP loop.
  Constr *propagate() {
    while (propQ.size() > 0) {
      lit p = propQ.deque(); // p is the fact to propagate
      vector<Constr *> tmp; // new watchers for p.
      vector<Constr *> &pwatches = watches[p.index()];
      std::copy(tmp.end(), pwatches.begin(), pwatches.end());

      for (int i = 0; i < tmp.size(); ++i) {
        // bollu: tmp[i] is **conflicting**.
        // bollu: copy remaining watches and return the constraint.
        if (!tmp[i]->propagate(this, p)) {
          // bollu: push all clauses left over from `pWatches`.
          for(int j = i + 1; j < tmp.size(); ++i) { pWatches.push(tmp[j]); }
          // bollu: stop propagation because we detected conflict.
          propQ.clear();
          return tmp[i]
        }
      }
    }
    return nullptr;
  }

  // Fig 9
  // minisat: puts a new fact onto prop Q, as well as immediately updating the variable's
  // assignment vector. If a conflict arises, false is returned and the propogatinon queue is cleared.
  bool enqueue(lit p, Constr *from = nullptr) {
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
      level [p.var()] = this->decisionLevel;
      reason [p.var()] = from;
      trail.push(p);
      propQ.insert(p);
    }
  }

  // minisat: analyze a conflict and produce a reason clause.
  // preconditions:
  //   (1) out_learnt is assumed to be cleared.
  //   (2) current decision level must be greater than root level.
  // bollu: Key CDCL loop here!
  void analyze(Constr *confl, vector<lit> *out_learnt, int *out_btlevel) {
    assert(out_learnt);
    assert(out_learnt.size() == 0);
    assert(decisionLevel() > 0);

    vector<bool> seen(nVars(), false);
    int counter = 0;
    // bollu TODO: what the heck is bottom lit?
    lit p = lit::lbot();
    vector<lit> p_reason;
    out_learnt.push(lit::lbot()); // minisat: leave room for asserting literal.

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
            out_learnt.push(q.neg());
            out_btlevel = max(out_btlevel, level[q.var()];
          }
        }
      }

      // minisat: select next lieral to look at.
      do {
        assert (this->trail.size() > 0);
        p = this->trail.last();
        confl = reason[p.var()];
        undoOne();
      } while(!seen[p.var()]);
      counter--;
    } while (counter > 0);
    *out_learnt[0] = p.neg();
  }

  // minisat: record a clause and drive backtracking.
  // precodntion: clause[0] contains the asserting literal.
  // precodnition: clause must not be empty.
  void record(vector<lit> clause) {
    assert(clause.size() > 0);
    Clause *c = nullptr; // minisat: will be set to created clause, or nullptr if c is unit.
    Clause::Clause_new(this, clause, true, &c);
    enqueue(clause[0], c);
    if (c != nullptr) {
      learnts.push(c);
    }
  }

  // Fig 12
  // minisat: unbinds the last variable on the trail.
  void undoOne() {
    assert (trail.size() > 0);
    lit p = trail.last();
    var x = p.var();
    assigns[x] = lbot();
    reason[x] = nullptr;
    level[x] = -1;
    order.undo(x);
    trail.pop_back();

    while(undos[x].size() > 0) {
      undos[x].last().undo(this, p);
      undos[x].pop_back();
    }
  }

  // Fig 12
  // minisat: return false if immediate conflict.
  bool assume(lit p) {
    trail_lim.push(trail.size());
    return enqueue(p);
  }

  // Fig 12
  // minisat: revert state to before push().
  void cancel() {
    assert (trail_lim.size() > 0);
    int c = trail.size() - trail_lim.last();
    // bollu: repeated undo vars on the trail.
    for (; c != 0; c--) {
      undoOne();
    }
    trail_lim.pop();
  }

  // Fig 12
  // minisat: pop several levels of assmptions.
  // after retruning, we will have decisionLevel() <= level,
  // and hopefully, decisionLevel() == level.
  void cancelUntil(int level) {
    while(decisionLevel() > level) {
      cancel();
    }
  }

  // Fig 13
  // minisat: Search method. Assumes and propagates until a conflict is found,
  // from which a conflict clause is learnt and backtracking performed
  // until search can continue.
  // Precondition: root_level == decisionLevel()
  lbool search(int nof_conflicts, int nof_learnts, SearchParams params) {
    int conflictC = 0;
    var_decay = 1.0 / params.var_decay;
    cla_decay = 1.0 / params.cla_decay;
    model.clear();

    while (true) {
      Constr *confl = this->propagate();
      if (confl != nullptr) {
      } else {
      }
    }
  }

  private:
  vector<Constr> constrs;
  vector<Clause> learnts;
  double cla_inc;
  double cla_decay;

  vector<double> activity;
  double var_inc;
  double var_decay;
  VarOrder order;
  vector<vector<Constr*>> watches;
  vector<vector<Constr*>> undos;
  queue<lit> propQ;
  vector<lbool> assigns;
  vector<lit> trail;
  vector<int> trail_lim; // separate decision levels in trail.
  vector<Constr *> reason; // for each variable, constraint that implied its value.
  vector<int> level;
  int root_level; // separate incremental & search assumptions.\\
};

int main() {
  return 0;
}

