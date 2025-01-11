#include <iostream>
#include <numbers>
#include <sstream>
#include <variant>
#include <vector>
#include"z3++.h"

using namespace z3;

void visit(std::vector<bool>& visited, expr const & e) {
  if (visited.size() <= e.id()) {
    visited.resize(e.id()+1, false);
  }
  if (visited[e.id()]) {
    return;
  }
  visited[e.id()] = true;

  if (e.is_app()) {
    unsigned num = e.num_args();
    for (unsigned i = 0; i < num; i++) {
      visit(visited, e.arg(i));
    }
    // do something
    // Example: print the visited expression
    func_decl f = e.decl();
    std::cout << "application of " << f.name() << ": " << e << "\n";
  }
  else if (e.is_quantifier()) {
    visit(visited, e.body());
    // do something
  }
  else { 
    assert(e.is_var());
    // do something
  }
}

/**
  \brief Test ite-term (if-then-else terms).
  */
void ite_example() {
  std::cout << "if-then-else example\n";
  context c;

  expr f    = c.bool_val(false);
  expr one  = c.int_val(1);
  expr zero = c.int_val(0);
  expr ite  = to_expr(c, Z3_mk_ite(c, f, one, zero));

  std::cout << "term: " << ite << "\n";
}

/**
  \brief Demonstrate how to evaluate expressions in a model.
  */
void eval_example1() {
  std::cout << "eval example 1\n";
  context c;
  expr x = c.int_const("x");
  expr y = c.int_const("y");
  solver s(c);

  /* assert x < y */
  s.add(x < y);
  /* assert x > 2 */
  s.add(x > 2);

  std::cout << s.check() << "\n";

  model m = s.get_model();
  std::cout << "Model:\n" << m << "\n";
  std::cout << "x+y = " << m.eval(x+y) << "\n";
}

/**
  \brief Simple function that tries to prove the given conjecture using the following steps:
  1- create a solver
  2- assert the negation of the conjecture
  3- checks if the result is unsat.
  */
void prove(expr conjecture) {
  context & c = conjecture.ctx();
  solver s(c);
  s.add(!conjecture);
  std::cout << "conjecture:\n" << conjecture << "\n";
  if (s.check() == unsat) {
    std::cout << "proved" << "\n";
  }
  else {
    std::cout << "failed to prove" << "\n";
    std::cout << "counterexample:\n" << s.get_model() << "\n";
  }
}

/**
  \brief Simple bit-vector example. This example disproves that x - 10 <= 0 IFF x <= 10 for (32-bit) machine integers
  */
void bitvector_example1() {
  std::cout << "bitvector example 1\n";
  context c;
  expr x = c.bv_const("x", 32);

  // using signed <=
  prove((x - 10 <= 0) == (x <= 10));

  // using unsigned <=
  prove(ule(x - 10, 0) == ule(x, 10));

  expr y = c.bv_const("y", 32);
  prove(implies(concat(x, y) == concat(y, x), x == y));
}


/**
  Demonstration of how Z3 can be used to prove validity of
  De Morgan's Duality Law: {e not(x and y) <-> (not x) or ( not y) }
  */
void demorgan() {
  std::cout << "de-Morgan example\n";

  context c;

  expr x = c.bool_const("x");
  expr y = c.bool_const("y");
  expr conjecture = (!(x && y)) == (!x || !y);

  solver s(c);
  // adding the negation of the conjecture as a constraint.
  s.add(!conjecture);
  std::cout << s << "\n";
  std::cout << s.to_smt2() << "\n";
  switch (s.check()) {
    case unsat:   std::cout << "de-Morgan is valid\n"; break;
    case sat:     std::cout << "de-Morgan is not valid\n"; break;
    case unknown: std::cout << "unknown\n"; break;
  }
}

/**
  \brief Find a model for <tt>x >= 1 and y < x + 3</tt>.
  */
void find_model_example1() {
  std::cout << "find_model_example1\n";
  context c;
  expr x = c.int_const("x");
  expr y = c.int_const("y");
  solver s(c);

  s.add(x >= 1);
  s.add(y < x + 3);
  std::cout << s.check() << "\n";

  model m = s.get_model();
  std::cout << m << "\n";
  // traversing the model
  for (unsigned i = 0; i < m.size(); i++) {
    func_decl v = m[i];
    // this problem contains only constants
    assert(v.arity() == 0); 
    std::cout << v.name() << " = " << m.get_const_interp(v) << "\n";
  }
  // we can evaluate expressions in the model.
  std::cout << "x + y + 1 = " << m.eval(x + y + 1) << "\n";
}

void tst_visit() {
  std::cout << "visit example\n";
  context c;

  // only one of the occurrences of x*x is visited 
  // because they are the same subterms
  expr x = c.int_const("x");
  expr y = c.int_const("y");
  expr z = c.int_const("z");
  expr f = x*x + x*x - y*y >= 0;
  std::vector<bool> visited;
  visit(visited, f);
}

/**
  \brief Small example using quantifiers.
  */
void quantifier_example() {
  std::cout << "quantifier example\n";
  context c;

  expr x = c.int_const("x");
  expr y = c.int_const("y");
  sort I = c.int_sort();
  func_decl f = function("f", I, I, I);

  solver s(c);

  // making sure model based quantifier instantiation is enabled.
  params p(c);
  p.set("mbqi", true);
  s.set(p);

  s.add(forall(x, y, f(x, y) >= 0));
  expr a = c.int_const("a");
  s.add(f(a, a) < a);
  std::cout << s << "\n";
  std::cout << s.check() << "\n";
  std::cout << s.get_model() << "\n";
  s.add(a < 0);
  std::cout << s.check() << "\n";
}

/**
  \brief Several contexts can be used simultaneously.
  */
void two_contexts_example1() {
  std::cout << "two contexts example 1\n";
  context c1, c2;

  expr x = c1.int_const("x");
  expr n = x + 1;
  // We cannot mix expressions from different contexts, but we can copy
  // an expression from one context to another.
  // The following statement copies the expression n from c1 to c2.
  expr n1 = to_expr(c2, Z3_translate(c1, n, c2));
  std::cout << n1 << "\n";
}

struct Config {
  int w = 5;
  Config() = default;
};

struct Problem {
  expr_vector exists_vars;
  expr_vector forall_vars;
  expr phi; // problem
  Problem(context & c) : phi(c), exists_vars(c), forall_vars(c) {};
};

std::ostream &operator << (std::ostream &o, const Problem &p) {
  o << "'";
  if (p.exists_vars.size() > 0) {
    o << "∃ ";
    for (expr x : p.exists_vars) {
      o << x << " ";
    }
  }

  if (p.forall_vars.size() > 0) {
    o << "∀ ";
    for (expr x : p.forall_vars) {
      o << x << " ";
    }
  }

  o << p.phi;
  o << "'";

  return o;
}

expr_vector get_model_assignments(model m, expr_vector xs) {
  expr_vector as(xs.ctx());
  for (expr x : xs) {
    as.push_back(m.eval(x, /*model_completion=*/true));
  }
  return as;
}


std::ostream &print_assignments(std::ostream &o, expr_vector xs, expr_vector as) {
  assert(xs.size() == as.size());
  for (int i = 0; i < xs.size(); ++i) {
    o << "  * M['" << xs[i] << "'] = '" << as[i] << "'\n";
  }
  return o;
}

std::optional<expr_vector> exists_forall_solver(Config config, context &c, Problem p) {
  // these are constaints that must be obeyed by the exists values.
  expr exists_constraints = c.bool_val(true);
  expr_vector exists_as(c); // assignments for existential variables.
  std::cerr << "==== Solving " << p << "==== \n";
  int i = 0;
  while(true) {
    i++;
    std::cerr << "\n## Iteration " << i << "## \n";
    solver se(c); // exists solver.
    se.add(exists_constraints);
    std::cerr << "+ ∃ Solving with constraints '" << exists_constraints << "'\n";
    se.check();
    check_result se_result = se.check();
    if (se_result) {
      model m = se.get_model();
      exists_as = get_model_assignments(m, p.exists_vars);
      std::cerr << "+ ∃ assignment: \n";
      print_assignments(std::cerr, p.exists_vars, exists_as);
    } else {
      // no exists solution found.
      std::cerr << "- ∃ ERROR: unable to solve for constraints: " << exists_constraints;
      return {};
    }

    solver sa(c); // forall solver.
    // great, we've found constants, let's now try to solve the forall problem.
    expr phi_exists_subst(p.phi);
    phi_exists_subst = phi_exists_subst.substitute(p.exists_vars, exists_as);
    std::cerr << "+ ∀ Solving for TAUTO '" << phi_exists_subst  << "'\n";
    // TAUTO (forall ys, phi[as](ys)) <-> UNSAT (exists ys, ! phi[as](ys))
    sa.add(!phi_exists_subst);
    check_result sa_result = sa.check();
    if (sa_result) {
      // oops, we found a counter-example model!
      model m = sa.get_model();
      std::cerr << "- ∀ Found Counterexample model:\n";
      // found the values of the forall values that creates the contradiction.
      // since the original formula is 'exists xs, forall ys, phi(xs, ys)', 
      // and we found a counter-example for 'forall ys, phi(xs := exists_as, ys)',
      // we can generalize, and rule out all 'xs' where  'ys := forall_as'.
      // So we add a constraint of the form 'phi(xs, ys := forall_as)'.
      expr_vector forall_as =  get_model_assignments(m, p.forall_vars);
      print_assignments(std::cerr, p.exists_vars, exists_as);
      print_assignments(std::cerr, p.forall_vars, forall_as);
      expr new_c = expr(p.phi).substitute(p.forall_vars, forall_as);
      std::cerr << "+ ∀ Extended ∃ constraints with '" << new_c << "'\n";
      exists_constraints = exists_constraints && new_c;
    } else {
      std::cerr << "+ ∃ ∀ Solved. Model:\n";
      print_assignments(std::cerr, p.exists_vars, exists_as);
      return exists_as;
    }
  }
}   

Problem problem_add_id(Config config, context &c) {
  Problem ret(c);
  expr x = c.bv_const("x", config.w);
  expr cst = c.bv_const("cst", config.w);
  // exists cst, forall w, x + cst = x
  ret.exists_vars.push_back(cst);
  ret.forall_vars.push_back(x);
  ret.phi = x + cst == x; 
  return ret;
}

Problem problem_left_shift_right_shift(Config config, context &ctx) {
  // https://blog.regehr.org/archives/1636
  Problem ret(ctx);
  expr x = ctx.bv_const("x", config.w);
  expr cst = ctx.bv_const("cst", config.w);
  // exists cst, forall w, x + cst = x
  ret.exists_vars.push_back(cst);
  ret.forall_vars.push_back(x);
  expr c1 = ctx.bv_val(1, config.w);
  ret.phi = z3::lshr(z3::shl(x, c1), c1) == (x & cst);
  return ret;
}

int main() {
  Config config;
  context ctx;
  std::vector<Problem> ps = { 
    problem_add_id(config, ctx),
    problem_left_shift_right_shift(config, ctx),
  };
  for (Problem p : ps) {
    exists_forall_solver(config, ctx, p);
  }
  return 0;
}

