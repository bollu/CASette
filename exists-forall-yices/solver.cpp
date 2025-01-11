#include <iostream>
#include <numbers>
#include <sstream>
#include <variant>
#include <vector>
#include"z3++.h"

using namespace z3;

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

