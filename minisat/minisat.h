// MiniSAT implementation[0]
// http://minisat.se/downloads/MiniSat.pdf
// Key CDCL loop: Solver->analyze()
#pragma once
#include <vector>
#include <queue>
#include <set>
#include <map>
#include <assert.h>
#include <algorithm>
#include <functional>
#include <iostream>
#include <string_view>


using var = int;


struct Solver;

struct SearchParams {
  double cla_decay;
  double var_decay;
  SearchParams(double cla_decay, double var_decay) : 
    cla_decay(cla_decay), var_decay(var_decay) {};
};

struct lit {
  var x;
  bool pos;
  explicit lit() : x(-1), pos(true) {}

  lit (var x, bool pos) : x(x), pos(pos) {}
  lit (const lit &other) : x(other.x), pos(other.pos) {}
  lit neg();
  static lit lbot();
  // it is SIGNED iff it is \overline{x}.
  bool sign() const;
  int var() const;
  int index() const;

  bool operator == (const lit &other) const;
  bool operator != (const lit &other) const;
  bool operator <(const lit &other) const { return this->index() < other.index(); }
};

struct lbool {
  enum class kind {
    bot = -1,
    t = 1,
    f = 0,
  } val;
  explicit lbool() { this->val = kind::bot; }
  explicit lbool(bool b);
  bool is_true() const;
  bool is_bot() const;
  bool is_false() const;
  lbool neg();
  bool operator == (const lbool &other) const;
  bool operator == (const bool &other) const { return *this == lbool(other); }
  bool operator != (const bool &other) const { return !(*this == other); }
};

lbool lbot();


// constraints
struct Constr {
  virtual ~Constr() {}
  virtual void remove(Solver *S) = 0;
  // return `false` if constraint is conflicting, true otherwise.
  virtual bool propagate(Solver *S, lit p) = 0;
  // return `true` is constaint is satisfied.
  virtual bool simplify(Solver *S) { return false; }
  virtual void undo(Solver *S, lit p) {};
  virtual void calcReason(Solver *S, lit p, std::vector<lit> *outReason) = 0;
};


struct Clause : public Constr {
  bool learnt;
  float activity;
  std::vector<lit> lits;

  static bool Clause_new(Solver *S, std::vector<lit> &ps, bool learnt, Clause **out);
  bool locked(Solver *S);
  void remove(Solver *S);
  bool simplify(Solver *S);
  bool propagate(Solver *S, lit p);
  void calcReason(Solver *S, lit p, std::vector<lit> *outReason);
};

struct VarOrder {
  VarOrder(std::vector<lbool> &assigns, std::vector<double> &activity) :
    assigns(assigns), activity(activity) {}
  void newVar(var x) ;
  void update(var x);
  void updateAll();
  void undo(var x);
  var select();
  std::vector<lbool> &assigns;
  std::vector<double> &activity;
  std::vector<var> heap;
};

struct Solver {
  Solver() : order(assigns, activity) {}

  var newVar();
  // minisat, pg 2:
  // variables are introduced with newVar();
  // from these variables, clauses are built and added with addClause().
  // trivial conflicts, like { [x], [!x] } being added is detected by addClause().
  // from this point on, the solver state is undefined, and should be used further.
  // If no such trivial clause is detected, solve() is called with the empty list of assumptions.
  // solve() returns `false` if the problem is UNSAT, and `true` is SAT, in which case the model can be
  // read from `model`.
  // simplifyDB() can be called before calling solve() to simplify the set of problem constraints
  //   (aka constraint database).
  // In ths impl, simplifyDB() will first propagate all unit information, and then delete all satisfied clauses.
  //
  // One can solve more interesting problems with unit assumptions.
  //   When passing a non-empty list of assumptions to the solver,
  //   the solver temporarily assumes the literals to be true.
  //   After finding unsat or model, the assumptions are undone,
  //   and the solver is returned to a usable state.
  //
  // For this to work, calling simplifyDB() before solve() is no longer optional.
  // It is the mechanism for detecting conflicts that are independent of the assumptions --
  // referred to as a *top level conflict* from now on -- which puts the solver in an undefined state.
  //
  // Apparently, the ability to pass unit assumptions is more powerful than it may first appear.
  // See [ES03]: temporal induction by incremental SAT solving.
  //
  // [CS03]: New techniques that improve MACE style finite model finding.
  bool addClause(std::vector<lit> literals);
  bool solve(std::vector<lit> assumptions);
  std::vector<bool> model;


  int nVars() { return this->assigns.size(); }
  int nAssigns() { return this->trail.size(); }
  int nConstraints() { return this->constrs.size(); }
  int nLearnts() { return this->learnts.size(); }
  lbool value(var x) { return this->assigns[x]; }
  lbool value(lit p) { return p.sign() ? value(p.var()).neg() : value(p.var()); }
  int decisionLevel() { return this->trail_lim.size(); }

  Constr *propagate();
  bool enqueue(lit p, Constr *from = nullptr);
  void analyze(Constr *confl, std::vector<lit> *out_learnt, int *out_btlevel);
  void record(std::vector<lit> clause);
  void undoOne();
  bool assume(lit p);
  void cancel();
  void cancelUntil(int level);
  lbool search(int nof_conflicts, int nof_learnts, SearchParams params);
  constexpr static const double DOUBLE_REPR_LIMIT = 1e100;

  void varBumpActivity(var x);
  void claBumpActivity(Clause *c);
  void varDecayActivity();
  void claDecayActivity();
  void varRescaleActivity();
  void claRescaleActivity();
  void decayActivities();
  void reduceDB();
  bool simplifyDB();

// private:
  std::vector<Constr *> constrs;
  std::vector<Clause *> learnts;
  double cla_inc;
  double cla_decay;

  std::vector<double> activity;
  double var_inc;
  double var_decay;
  VarOrder order;
  std::vector<std::vector<Constr*>> watches;
  // why does each variable have an undo?
  std::vector<std::vector<Constr*>> undos;
  std::queue<lit> propQ;
  std::vector<lbool> assigns;
  std::vector<lit> trail;
  std::vector<int> trail_lim; // separate decision levels in trail.
  std::vector<Constr *> reason; // for each variable, constraint that implied its value.
  std::vector<int> level;
  int root_level; // separate incremental & search assumptions.
};
