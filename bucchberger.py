#!/usr/bin/env -vS pytest -v  
# Bucchberger algorithm for computing grobner basis.
import math
from division import *
from hypothesis import given, example, settings
from hypothesis.strategies import text, composite, integers, lists
from typing import List


def lcm_expvec(m: ExpVec, n: ExpVec):
    out = ExpVec.zero()
    for i in range(NVARS):
         out[i] = max(m.exp[i], n.exp[i])
    return out

def lcm_monomial(m: Mono, n: Mono):
    return Mono(coeff=math.lcm(m.coeff, n.coeff), exp=lcm_expvec(m, n))

def bucchberger(ps: List[Poly]):
    changed = True
    while changed:
        ss = set()
        for p in ps:
            for q in ps:
                lcm = lcm_monomial(p.leading(), q.leading())
                S = lcm * p / p.leading() - lcm * q / q.leading()
                if S == Mono.zero(): continue
                # is already represented
                represented = False
                for r in ps:
                    if division(S, [r]) == Poly.zero():
                        represented = True
                        break
                if not represented:
                    ss.insert(S)

        # add to ideal generators
        ps.append(list(ss))
        changed = len(ss) > 0
    return ps

@given(ideal=lists(polynomials(), min_size=1))
def test_bucchberger(ideal):
    ideal2 = bucchberger(ideal)

                

if __name__ == "__main__":
    pass
