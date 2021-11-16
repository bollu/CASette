#!/usr/bin/env python3
# https://www.youtube.com/watch?v=BHezLvEH1DU
# https://math.berkeley.edu/~kmill/notes/todd_coxeter.html
# http://pi.math.cornell.edu/~kbrown/6310/toddcox.pdf

# Coxeter diagram
# * - * - * - * - ... - * (n-1) points
# we have x^2 = 1 for each point x
# we have  (xy)^3 = 1 if x - y [connected]
# we have (x y) = 1 if x y  [discnnected]

# Are there other relations other than these?
# there's a map  from G -> Sn -> 1 if G obeys the above relations.
# we want to show that the kernel is 1.
# it's enough to show that |G| <= |Sn|. We already know that the map is onto by the exactness of [G -> Sn -> 1]

# We consider the case for n = 4
# Consider G: a - b - c - d. Consider H = a - b - c. We know by induction that |H| <= |S4| = 24
# If we can show that |G|/|H| <= 5, then |G| <= 120 and we are done.

# We construct the permutation representation of G  on the cosets of H by brute force.


# 1 : point fixed by H. a, b, c ∈ H all fix `1`.
# what does `d` do? It must take it to another point `2`.
# so the diagram becomes 1 -d-> 2.
# what does a,b,c do to 2?
# we know that bd = db, or dbd^{-1} = b. So b(2) = dbd^{-1}(2) = db(1) = d(1) = 2.
# similarly, ad = da 


idents = [] # vertices seen to far
neighbors = [] # neighbouts of vertex i
to_visit = 0



def find(c):
    c2 = idents[c]
    if c == c2:
        return c
    else:
        c2 = find(c2)
        idents[c] = c2
        return c2


def unify(c1, c2):
    c1 = find(c1)
    c2 = find(c2)
    if c1 == c2:
        return
    c1, c2 = min(c1, c2), max(c1, c2)
    idents[c2] = c1
    for d in range(2*nggens):
        n1 = neighbors[c1][d]
        n2 = neighbors[c2][d]
        if n1 == None:
            neighbors[c1][d] = n2
        elif n2 != None:
            unify(n1, n2)



def new():
    c = len(idents)
    idents.append(c)
    neighbors.append((2*nggens)*[None])
    return c


def follow(c, d):
    c = find(c)
    ns = neighbors[c]
    if ns[d] == None:
        ns[d] = new()
    return find(ns[d])

def followp(c, ds):
    c = find(c)
    for d in reversed(ds):
        c = follow(c, d)
    return c

def cycle(perm):
    parts = []
    for i in range(len(perm)):
        part = [str(i+1)]
        k = perm[i]
        while k != i:
            if k < i: break
            part.append(str(k+1))
            k = perm[k]
        else:
            parts.append(" ".join(part))
    return "("+")(".join(parts)+")"


def parse_word(w: str) -> list[int]:
    w = w.lower()
    out = []
    i = 0
    while i < len(w):
        assert w[i] >= 'a' and w[i] <= 'z'
        letter = 2 * (ord(w[i]) - ord('a'))
        i += 1
        if i < len(w) and w[i] == '\'':
            letter += 1 # use inverse
            i += 1
        out.append(letter)
    return out

def print_word(w: list[int]) -> str:
    out = ""
    out += chr(ord('a') + w[i])
    if w[i] % 2 == 1: out += '\''
    return out

nggens = 2
grels = [
    parse_word("a'a"),
    parse_word("b'b"),
    parse_word("aaa"),
    parse_word("bb"),
    parse_word("abab")
    # (1, 0), # a^-1a
    # (3, 2), # b^-1b
    # (0, 0, 0), #a^3
    # (2, 2), # b^2
    # (0, 2, 0, 2) # abab
]
hgens = [
    parse_word("b")
]


if __name__ == "__main__":
    start = new()
    for hgen in hgens:
        unify(followp(start, hgen), start)

    while to_visit < len(idents):
        c = find(to_visit)
        if c == to_visit:
            for rel in grels:
                unify(followp(c, rel), c)
        to_visit += 1

    # find equivalence class representattives
    cosets = [c for i, c in enumerate(idents) if i == c]

    # see what coset one gets
    perms = [[cosets.index(follow(c, 2*d)) for i, c in enumerate(cosets)]
         for d in range(nggens)]

    for d in range(nggens):
        print("g%d ="%d, cycle(perms[d]))

# There is a difference between enumerating cosets of <g> under subgroup <g^7=e, g^3=e>, and
# enumerating cosets of <g | g ^7 = e> under subgroup < g^3 = e>
