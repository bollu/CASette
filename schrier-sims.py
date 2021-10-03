#!/usr/bin/env python3
# run tests with:
# $ pytest --hypothesis-show-statistics
from fractions import Fraction
from hypothesis import given, example, settings
from typing import List, Dict, Set
from hypothesis.strategies import text, composite, integers, lists



class Permutation:
    def __init__(self, mapping: Dict[int, int]):
        assert Permutation.find_non_bijection_witness(mapping) is None
        self.mapping = mapping

    @classmethod
    def find_non_bijection_witness(self, mapping):
        # if bijetion, return none. otherwise return x1, x2 in mapping such that mapping[x1] == mapping[x2]
        # check injective, surjective is by definition
        inverse_images = {}
        for (x, y) in mapping.items():
            if y in inverse_images:
                return x, inverse_images[y]
            else:
                inverse_images[y] = x
        return None

    def sn(self): # find largest number in domain/codomain
        n = 0
        for(x, y) in self.mapping.items():
            n = max(n, x, y)
        return n

    def __call__(self, i):
        if i in self.mapping:
            return self.mapping[i]
        return i

    @classmethod
    def identity(self):
        return Permutation({})

    def inverse(self):
        inverse = {}
        for (x, y) in self.mapping.items():
            inverse[y] = x
        return Permutation(inverse)


    # (g.compose_left_of(h))(x) = g(h(x))
    def compose_left_of(g, h):
        domain = set()
        domain = domain.union(h.mapping.keys())
        domain = domain.union(g.mapping.keys())

        mapping = { x : g(h(x)) for x in domain}
        return Permutation(mapping)


    def __eq__(self, other):
        N = max(self.sn(), other.sn())
        for i in range(N):
            if self(i) != other(i): return False
        return True

    # (g * h)(x) = g(h(x))
    def __mul__(self, other): 
        return self.compose_left_of(other)

    def is_identity(self):
        for k in self.mapping:
            if self.mapping[k] != k: return False
        return True

    def __repr__(self):
        out = ""
        cycs = self.cycles()
        for cyc in cycs:
            out +=  "("
            first = True
            for x in cyc:
                if not first: out += " "
                first = False
                out += str(x)
            out +=  ")"
        return out

    __str__ = __repr__

    def cycles(self) -> Set[List[int]]:
        cycles = []
        seen = set()
        for x in range(self.sn()):
            if x in seen: continue
            cycle = [x]
            seen.add(x)

            xpow = self(x)
            while xpow != x:
                cycle.append(xpow)
                seen.add(xpow)
                xpow = self(xpow)
            cycles.append(cycle)
        return cycles



# Rubick's cube perspective: https://www.jaapsch.net/puzzles/schreier.htm


# https://math.stackexchange.com/questions/1662723/can-someone-explain-how-the-schreier-sims-algorithms-works-on-a-permutation-grou

# https://mathstrek.blog/2018/06/12/schreier-sims-algorithm/

# A: subset of Sn
# G := <A>: subgroup generated by A
# Sn acts on [n] := { 1...n }

# pick a random element k ∈ [n], consider its orbit under G. We know that Size(O[k]) = Size(G|) / Size(Stab[k])
# start by setting O[k] := {k}, expand by allowing elements of A to act on O[k]
# If we can can recursively find Size(Stab[k]), we are done [or so it seems? Stab[k] lives in 2^G, not 2^[n] ]
# We need representatives for left cosets of G.


# compute how to reach [1..n] rom k ∈ [n] using as
# maps a number `c` to the permutation that links its parent `p` to `c`. So we have:
# schrier_vector[c].inverse()[c] = p
# This gives us the orbit. For if an element k ∈ n is not reachable, it will be listed as None.
def schrier_vector(as_: List[Permutation], n: int, k: int) -> List[Permutation]:
    vs = [None for _ in range(n)]

    vs[k] = Permutation.identity()
    changed = True
    while changed:
        changed = False
        for i in range(n):
            if vs[i] is None: continue
            for a in as_:
                if vs[a(i)] is None:
                    changed = True
                    vs[a(i)] = a

                ainv = a.inverse()
                if vs[ainv(i)] is None:
                    changed = True
                    vs[ainv(i)] = ainv
    return vs



# Find smallest index i such that p(i) != i.
# That is, for all small < i, p(small) = small, and p(i) != i
def least_nonfixed(p: Permutation, n:int) -> int:
    assert not p.is_identity()
    for i in range(n):
        # loop invariant: ∀ small < i, p(small) = small)
        if p(i) == i: continue
        # can't have p(i) < i because we are dealing with permutations, and for all
        # indeces small < i, we have pinv(small) = small, since p(small) = small is loop invariant.
        assert p(i) > i 
        return (i, p(i))
    raise RuntimeError("didn't find non-fixed value though not identity")

# return as_ to size n(n-1)/2;
def sims_filter(as_: List[Permutation], n:int):
    table = [[None for j in range(n)] for i in range(n)]

    for a in as_:
        while not a.is_identity():
            (i, j) = least_nonfixed(p)
            if table[i][j] is None:
                table[i][j] = a
                break
            else:
                # should this not be a = a * table[i][j].inverse()
                a = a.inverse() * table[i][j] # strikes me as weird.
                # see that anew(i) = i, since
                # - aprev(i) = j ; aprev_inv(j) = i
                # - table[i][j](i) = j
                # - thus (aprev_inv * table[i][j])(i) = aprev_inv(j) = i
                # so we have that least_nonfixed(anew) > least_nonfixed(a)
    s = set()
    for i in range(n):
        for j in range(i+1, n):
            s.insert(table[i][j])
    return s

@composite
def permutations(draw, n: int):
    # raw random
    # Fishes Yates: https://en.wikipedia.org/wiki/Fisher%E2%80%93Yates_shuffle
    xs = { i : i for i in range(n) }

    i = n-1 # from (n-1), down to zero.
    while i >= 0:
        j = draw(integers(0, i)) # j ∈ [0, i]
        temp = xs[i]; xs[i] = xs[j]; xs[j] = temp; # swap
        i -= 1
    return Permutation(xs)


@given(p=permutations(n=5))
def test_permutation_group_inverse(p: Permutation):
    assert (p * p.inverse()).is_identity()
    assert (p.inverse() * p).is_identity()

@given(p=permutations(n=5), q=permutations(n=5), r=permutations(n=5))
def test_permutation_group_assoc(p: Permutation, q: Permutation, r: Permutation):
    assert (p * (q * r)) == ((p * q) * r)

@given(p=permutations(n=5))
def test_permutation_group_id(p: Permutation):
    assert (p * p.identity()) == p
    assert p == p * p.identity()


def main():
    pass

if __name__ == "__main__":
    main()
