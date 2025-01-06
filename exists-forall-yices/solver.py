#!/usr/bin/env python3
from z3 import *

# x = Int('x')
# y = Int('y')
# solve(x > 2, y < 10, x + 2*y == 7)

# Section 2: SMT based EF solving.
# ∃ x, A y, phi(x, y)
# e solver generates candidates.
# f solver tries to find counterexamples to phi(a, y)
def ef_solver(xs, ys, phi, e_solver, f_solver, g_solver):
    # cs: Set of potential candidates for ai.
    cs = BoolVal(True) # grab initial constraints on x from phi
    while True:
        ai = e_solver(xs, cs)
        if ai is None:
            # all candidates for ai have been ruled out, so
            # bail out, as no solution exists.
            return None
        # check if 'phi(ai, y)' is UNSAT. If it is, then we have succeeded.
        # otherwise, we have found a counterexample bi.
        bi = f_solver(xs, ys, ai, phi)
        if bi is None:
            return ai
        else:
            g = gs_solver(xs, ys, ai, phi, bi)
            cs = And(cs, Not(g))
            # Create a new G, such that:
            #  (1) G(ai) = True, so ai is removed from the set of candidates.
            #  (2) G(x0) => !(∀ y, phi(x0, y)). So, G(x0) is true
            #    implies that x0 cannot be a solution to the exists-forall problem.

            # generalize from bi
            #G(x) := x = Ai

def g_solver_naive(xs, ys, ai, phi, bi):
    # rule out all cases where we assign the 'x' to the 'a'.
    formula = BoolVal(True)
    for (x, a) in itertools.zip(xs, ai):
        formula = And(formula, x != a)
    return formula

def g_solver_subst(xs, ys, ai, phi, bi):
    # recall that we found a counter-example, where phi(ai, bi) is false.
    # so, we rule out all models for G(xs) := !(phi(xs, bs)).
    # This needs a bit more meditation.
    # We have a 'guard', that tells us which models we should rule out.
    # We rule out all those models phi(xs,) such that phi(xs, bs) is unsat.
    # So in this way, we kill the "forall" space, which is much larger.
    # But surely this can kill solutions that otherwise exist?
    # 
    # 
    # 
    #     |  *   *
    # bi  |      *
    #     |  *   *
    #     |  *   *
    #     +--*---*----
    #        ai  aj
    #  Indeed, clearly, (ai, bi) is a counterexample, but if we rule out the (bi),
    #  then we miss the hashed  (aj)?
    #  Oh fuck, we don't! We allow it! 
    #  Ok, this is brilliant. What we actually decide to do is to throw a "ray" along the bi direction,
    #  such that for any case `ai'` we try next, we probe it with the $bi$ ray. This rules out `ai`,
    #  and also any other example like `ai`. 
    #  On the other hand, this is complete, since it never rules out any good candidate like aj.

    # exists x, forall y, <something>
    formula = phi
    for (y, b) in itertools.zip(xs, bi):
        formula = substitute(y, b)
    formula = Not(formula) # we don't want a xi such that this is true.
    return formula


def g_solver_model_guided(xs, ys, F, M):
    # M is a model for ∃ xs, ∀ ys, F.
    # we will create a formula G such that G(xs) => !∀ys, F(xs, ys).

    # We do this in two steps
    # First, we create an implicant B of F, based on the model M.
    # Next, we eliminate Y variables from B, by taking advantage of the model M.

    # The implicant B is a conjunction of arithmetic literals that implies F and
    # such that B is true in M.
    # Imp+(l) := l
    # Imp+(f1 \/ f2) = Imp+(f1) if M(f1) else Imp+(f2) # <- MODEL BASED.
    # Imp+(f1 /\ f2) = Imp+(f1) /\ Imp+(f2)
    # Imp+(!f) = Imp-(f)

    # Imp-(t = 0) := t >= 0 if M[t] > 0 else !(t >= 0) # <- MODEL BASED.
    # Imp-(f1 /\ f2)

    # We can construct a G such that G => !(∀ y1, .. yn, B).
    #   This suffices because B implies F.

    # We will use *virtual substitution*. We compute *elimination sets*.
    # For a formula $\phi$ and a variable $y$ that is free in $\phi$,
    # an eliminiation set is a finite set $V$ of terms such that 
    # (∃ y : φ) = \/_{t ∈ V} φ[y := t]
    # https://publikationen.sulb.uni-saarland.de/bitstream/20.500.11880/26735/1/mkosta_dissertation.pdf
    # Q. How to do virtual term substitution for BV theory? has this even been studied? 
    #   Does Reghr think this is even necessary?
    pass

def g_solver_model_guided(xs, ys, ai, phi, bi):
    # Model guided generalization, can be seen as a form of QE, where we are eliminating
    # ∀y, in a way that is guided by the counter-example model (ai, bi).
    # Not that for us, in the case of bitvectors, we will need to guide the model differently / carefully.
    pass

def solve(xs, ys, phi):
    def e_solver (xs, cs):
        # find a model for the formula phi(xs, ys) and cs.
        s = Solver()
        s.add(cs)
        if s.check() == sat:
            m = s.model()
            return [m[x] for x in xs]
        else:
            return None

    def f_solver(xs, ys, ai, phi):
        # find a model for the formula phi(ai, ys).
        s = Solver()
        s.add(substitute(phi, ai))
        if s.check() == sat:
            m = s.model()
            return [m[y] for y in ys]
        else:
            return None
    return ef_solver(xs, ys, phi, e_solver, f_solver, g_solver_subst)


