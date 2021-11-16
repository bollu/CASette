#!/usr/bin/env python3
# run tests with:
# $ pytest --hypothesis-show-statistics
from fractions import Fraction
from hypothesis import given, example, settings
from hypothesis.strategies import text, composite, integers, lists


NVARS = 3
NAMES = "pqr"
class ExpVec:
    def __init__(self, exp):
        self.exp = exp
    def __add__(self, other):
        out = [0 for _ in range(NVARS)]
        for i in range(NVARS):
            out[i] = self.exp[i] + other.exp[i]
        return ExpVec(out)
    def __sub__(self, other):
        out = [0 for _ in range(NVARS)]
        for i in range(NVARS):
            out[i] = self.exp[i] - other.exp[i]
        return ExpVec(out)

    def nonneg(self):
        for i in range(NVARS):
            if self.exp[i] < 0: return False
        return True

    def __hash__(self):
        return hash(tuple(self.exp))

    def __eq__(self, other):
        return self.exp == other.exp

    def __lt__(self, other):
        if self == other: return False
        for i in range(NVARS):
            if self.exp[i] == other.exp[i]: continue
            return self.exp[i] < other.exp[i]

    @classmethod
    def zero(self):
        return ExpVec([0 for _ in range(NVARS)])

    def is_zero(self):
        return self == ExpVec.zero()

    def __getitem__(self, ix):
        return self.exp[ix]

    def __setitem__(self, ix, val):
        self.exp[ix] = val

    def __repr__(self):
        out = "("
        printed = False
        for i in range(NVARS):
            if self.exp[i] == 0: continue
            if printed: out += " "
            printed = True
            out += NAMES[i] + "^" + str(self.exp[i])
        out += ")"
        return out

    
class Mono:
    def __init__(self, coeff: int, exp: ExpVec):
        assert isinstance(coeff, int)
        assert isinstance(exp, ExpVec)
        self.coeff = coeff
        if self.coeff == 0:
            self.exp = ExpVec.zero()
        else:
            self.exp = exp
    
    def nonneg(self):
        return self.exp.nonneg()

    @classmethod
    def constant(cls, const):
        return Mono(const, ExpVec.zero())

    @classmethod
    def zero(cls):
        return Mono(0, ExpVec.zero())

    def __mul__(self, other):
        if isinstance (other, int):
            return Mono(self.coeff *other, self.exp)
        elif isinstance(other, Mono):
            return Mono(self.coeff * other.coeff, self.exp + other.exp)
        elif isinstance(other, Poly):
            return Poly(self) * other
        else:
            raise RuntimeError(f"unknown arguments to Mono multiplication: {self} and {other}")


    def __eq__(self, other):
        if isinstance(other, int):
            return self == Mono.constant(other)
        isinstance(other, Mono)
        return self.coeff == other.coeff and self.exp == other.exp

    # divide other by self
    def divide(self, other):
        assert isinstance(self, Mono)
        assert isinstance(other, Mono)
        d = other.coeff // self.coeff
        r = other.coeff % self.coeff
        exp = other.exp - self.exp
        return (Mono(d, exp), (r, exp))

    def __add__(self, other):
        assert isinstance(self, Mono)
        assert isinstance(other, Mono)
        return Poly([self, other])

    def __sub__(self, other):
        assert isinstance(self, Mono)
        assert isinstance(other, Mono)
        return Poly([self, -1*other])

    def __lt__(self, other):
        assert isinstance(self, Mono)
        assert isinstance(other, Mono)
        return (self.exp, self.coeff) < (other.exp, other.coeff)

    __rmul__ = __mul__

    def __repr__(self):
        return f"{self.coeff}{self.exp}"

    # leading term of a monomial is itself
    def leading(self):
        return self

p = Mono(1, ExpVec([1, 0, 0]))
q = Mono(1, ExpVec([0, 1, 0]))
r = Mono(1, ExpVec([0, 0, 1]))

class Poly:
    def __init__(self, v):
        if isinstance(v, list):
            self.terms = v
        elif isinstance(v, int):
            self.terms = [Mono(v, ExpVec.zero())] 
        elif isinstance(v, Mono):
            self.terms = [v]
        else:
            raise RuntimeError(f"unknown Poly init {self}")
        self.normalize()

    @classmethod
    def zero(cls):
        return Poly([])

    def normalize(self):
        exp2coeff = {}
        for term in self.terms:
            if term.exp in exp2coeff:
                exp2coeff[term.exp] = exp2coeff[term.exp] + term.coeff
            else:
                exp2coeff[term.exp] = term.coeff
        normalized = []
        for (exp, coeff) in exp2coeff.items():
            if coeff == 0: continue
            normalized.append(Mono(coeff, exp))
        self.terms = normalized
        self.terms.sort()

    def __add__(self, other):
        if isinstance(other, Poly):
            return Poly(self.terms + other.terms)
        elif isinstance(other, Mono):
            return self + Poly(other)
        elif isinstance(other, int):
            return self + Poly(other)

    def __eq__(self, other):
        if isinstance(other, Poly):
            if len(self.terms) != len(other.terms): return False
            for i in range(len(self.terms)):
                if self.terms[i] != other.terms[i]: return False
            return True
        elif isinstance(other, Mono):
            return self == Poly(other)
        elif isinstance(other, int):
            return self == Poly(other)
        else:
            raise RuntimeError("unknown equality {self} and {other}")
    def __sub__(self, other):
        return self + (-1) * other

    def __mul__(self, other):
        if isinstance(other, int):
            return Poly([t * other for t in self.terms])
        elif isinstance(other, Mono):
            return self * Poly([other])
        elif isinstance(other, Poly):
            out = [s * t for s in self.terms for t in other.terms]
            return Poly(out)
        else:
            raise RuntimeError(f"unknown multiplication {self} and {other}")


    __rmul__ = __mul__

    def leading(self):
        if len(self.terms) == 0: return Mono.zero()
        else: return self.terms[-1]

    def __repr__(self):
        out = "("
        for i in range(len(self.terms)):
            if i > 0: out += " + "
            out += str(self.terms[i])
        out += ")"
        return out


def does_mono_divide_poly(mono_divisor, p):
    assert isinstance(mono_divisor, Mono)
    assert isinstance(p, Poly)
    for term in p.terms:
        (div, rem) = mono_divisor.divide(term)
        if div == Mono.zero(): return False
        if not div.nonneg(): return False
    return True

# p = qs * ks + r. Returns (ks, r)
def division(p, qs):
    assert len(qs) > 0
    if isinstance(p, Mono):
        p = Poly(p)
    for i in range(len(qs)):
        if isinstance(qs[i], Mono):
            qs[i] = Poly(qs[i])

    assert isinstance(p, Poly)
    ks = [Poly.zero() for _ in qs]
    r = Poly.zero()
    while p != 0:
        divided = False
        for i in range(len(qs)):
            if qs[i].leading() == Mono.zero(): continue
            if does_mono_divide_poly(qs[i].leading(), p):
                div, rem = qs[i].leading().divide(p.leading())
                assert div != Mono.zero()
                p = p - div * qs[i]
                ks[i] += div
                divided = True
                
                if p == 0: break
        if not divided:
            r = r + p.leading()
            p = p - p.leading()
    return (ks, r)

def check_division(top, bots):
    # top: numerator, bots: denominators
    (ks, r) = division(top, bots)
    cert = r # certificate
    for i in range(len(bots)):
        cert = cert + ks[i] * bots[i]
    print(f"\n---\n{top} / {bots}\n= {ks} * {bots} + {r}\n=cert: {cert}")
    assert cert == top

@composite
def expvecs_nonneg(draw):
    elements=integers(0, 4)
    xs = draw(lists(elements, min_size=NVARS, max_size=NVARS))
    return ExpVec(xs)

@composite
def monomials(draw):
    exp = draw(expvecs_nonneg())
    coeff = draw(integers(-10, 10))
    return Mono(coeff, exp)

@composite
def polynomials(draw):
    nterms = draw(integers(0, 5))
    out = Poly.zero()
    for i in range(nterms):
        out = out + draw(monomials())
    return out


# @example(2*p + 4*p*p*q + 8*p*p*p*r, [2*p, q, r])
@given(top=polynomials(), bots=lists(polynomials(), min_size=1))
def test_division_certificate(top, bots):
    (ks, r) = division(top, bots)
    cert = r # certificate
    for i in range(len(bots)):
        cert = cert + ks[i] * bots[i]
    assert cert == top

if __name__ == "__main__":
    check_division(p + q + r, [2*p, q])
    check_division(6*p, [2*p])
    check_division(6*p, [3*p])
    check_division(6*p, [4*p])
    check_division(6*p, [7*p])
    check_division(2*p + 4*p*p*q + 8*p*p*p*r, [2*p, q, r])

