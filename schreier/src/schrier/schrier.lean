import group_theory.subgroup.basic
import group_theory.coset
import group_theory.sylow
import group_theory.perm.basic
import group_theory.perm.fin
import group_theory.group_action.basic
import group_theory.group_action.defs
import algebra.group.defs

open list  fin function subgroup

variables {G : Type*} [group G]
-- symmetric group on n letters
@[simp]
def S (n: nat) := (equiv.perm (fin n))

instance  (n: nat) : group (S n) :=
{ mul := λ f g, equiv.trans g f,
  one := equiv.refl _,
  inv := equiv.symm,
  mul_assoc := λ f g h, (equiv.trans_assoc _ _ _).symm,
  one_mul := equiv.trans_refl,
  mul_one := equiv.refl_trans,
  mul_left_inv := equiv.self_trans_symm }



-- subset of Sn
variables {H: ∀ (N: nat), set (S N)}


instance (N: nat): has_scalar (S N) (fin N)  := 
{ smul :=  λ s n, (equiv.to_fun s) n }


instance (N: nat): mul_action (S N) (fin N) :=  {
  smul := λ s n, (equiv.to_fun s) n,
  one_smul :=  begin
     intros,
     unfold has_scalar.smul,
     simp,
  end,
  mul_smul := begin
    intros,
    unfold has_scalar.smul,
    unfold has_mul.mul,
    simp,
    unfold mul_one_class.mul,
    unfold monoid.mul,
    unfold div_inv_monoid.mul,
    unfold group.mul,
    unfold equiv.trans,
    simp,
  end
}

theorem fin.upcast {n N: nat} (LEQ: n ≤ N) (f: fin n): fin N := begin
  constructor,
  swap,  
  exact f.val,
  have fbound : (f.val < n), begin
    exact f.prop
  end,
  linarith
end


-- -- | H stabilizes the interval `[0..n] ⊂ [0..N]` iff H is a subset of the stabilizer of
-- each `i ∈ [0..n]`.
def interval_stab (n N: nat) (LEQ: n ≤ N) (K: set (S N))
  : Prop := ∀ (i: fin n), K ≤  (mul_action.stabilizer (S N) (fin.upcast LEQ i))


-- | A chain of stabilizers is an ascending sequence of subsets of Sn, where Ks(i)
-- | stabilizes the interval [0..i]
def chain_of_stabs (N: nat) (Ks: fin N → (set (S N))) : Prop := 
  (∀ (i: fin N), interval_stab i N (le_of_lt i.prop) (Ks i)) /\
  (∀ (i: fin N) (j: fin N) (LT: i < j), Ks i ≤ Ks j)

def generators (N: nat) (gs: finset (S N)) (H: subgroup (S N)) : Prop := 
    closure (coe gs) = H


-- | records how to reach `k` from `i`.
def schrier_vector (N: nat)
  (H: subgroup (S N))
  (k: fin N)
  (vec: fin N → option H): Prop
  := ∀ (i: fin N), ∃ (p: H), some p = vec i → p • i = k 

/-
# compute how to reach [1..n] rom k ∈ [n] using as
# maps a number `c` to the permutation that links its parent `p` to `c`. So we have:
# schrier_vector[c].inverse()[c] = p
# This gives us the orbit. For if an element k ∈ n is not reachable, it will be listed as None.
def schrier_vector(as_: List[Permutation], k: int, n:int) -> List[Permutation]:
    assert k < n
    vs = [None for _ in range(n)]
    vs[k] = Permutation.identity()
    changed = True
    while changed:
        changed = False
        for i in range(n):
            if vs[i] is None: continue
            for a in as_:
                if vs[a(i)] is None: changed = True; vs[a(i)] = a
                ainv = a.inverse()
                if vs[ainv(i)] is None: changed = True; vs[ainv(i)] = ainv
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
            (i, j) = least_nonfixed(a, n)
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
            if table[i][j] is None: continue
            s.add(table[i][j])
    return s


# given generators, generate the full group
def generate_from_generators(ps: List[Permutation]):
    H = set(); H.add(Permutation.identity())
    while True:
        Hnew = set()
        for h in H:
            for p in ps:
                hnew = h * p
                if hnew in H: continue
                Hnew.add(hnew);

        if not Hnew: return H
        else: H = H.union(Hnew)
    return H


# returns a map of elements in the orbit of k to the permutation that sends them there.
# see that there are coset representatives by the orbit stabilizer theorem.
def stabilizer_coset_representatives_slow(gs: Set[Permutation], k: int, n:int) -> Dict[int, Permutation]:
    gs = set(gs)
    gs.add(Permutation.identity())
    orb2rep = {}
    orb2rep = { k : Permutation.identity() }

    while True:
        new_orb2rep = {}
        # terrible, O(n^2). use some kind of tree search!
        for g in gs:
            # rep es coset representative for orb ∈ Orbit(k)
            for (orb, rep) in orb2rep.items(): 
                repnew = g * rep; orbnew = repnew(k)
                if orbnew in orb2rep: continue # have already seen
                new_orb2rep[orbnew] = repnew
        # no update
        if not new_orb2rep: return orb2rep
        orb2rep.update(new_orb2rep)


# we have a group G = <gs>
# We have k ∈ S, and we need to find hs ⊂ G such that <hs> = Stab(k).
# We have partitioned G into cosets of Stab(k) via (o[0] Stab(k), ..., o[n] Stab(k)).
#   These are called os[:] since they are Cosets of the Stabilizer,
#   which are in bijection with *O*rbits. [Orbit stabilizer]
# Key idea: we have a sort of "splitting"
#   find coset             return coset repr.
# G ----------> G/Stab(k) -------------------> G
# Call the composite map defect: G -> G, since it measures how far an element is from
# living in Stab(k). See that defect(h) = e iff h ∈ Stab(k).

# Now consider: remove_defect (h: G) : G := defect(h).inverse() * h
# `remove_defect` 'inverts' the defect. It allows `h` to act, sending k to some element of Orb(k).
#  it then undoes the defect [by defect(h).inverse()], moving it back to `k`. So we have
#  k --h----------> l ∈Orb(k) --defect(h).inverse()---> k
#  k --defect(h)--> l ∈Orb(k) --defect(h).inverse()---> k
#
# Thus, for all g ∈ G, we have remove_defect(g) ∈ Stab(k).
#
# It is now plausible that: <gs> = G => < gs.map(remove_defect) > = Stab(k)
# since  remove_defect forces elements to stabilize k,
# and we apply this treatment to all of G(by modifying the generator). 
# 
# However, the weird part is that THAT's NOT ENOUGH.
# Rather, we need the generators to be: < (gs * os).map(remove_defect) >
# For whatever reason, we must take all pairs of gs, os!
def generators_of_stabilizer(gs: List[Permutation], k: int, n: int):
    purified = set()

    # Create coset representatives
    orb2rep = stabilizer_coset_representatives_slow(gs, k, n)

    # candidates = [g * rep for g in gs for rep in orb2rep.values()]
    candidates = gs


    for h in candidates:
            o = h(k) # find where h sends k | o ∈ Orb(k)
            orep = orb2rep[o] # find coset representative corresponding to o
            # orep is hdefect, since it tells us which coset h lies in.
            # h = orep * h_k_stab
            # h_k_stab := h * orep.inverse()
            h_k_stab = orep.inverse() * h
            purified.add(h_k_stab)
    return purified


def schrier_decomposition(gs: List[Permutation], n: int, use_sims_filter:bool = True) -> Dict[int, Permutation]:
    Ggens = {-1: gs} # Gss[i]: List[int] = generators of G[i]. so G[0] = < gs > = < Ggens[0] > and so on.
    gs_prev = gs
    # Ggens[k] is a subgroup of <gs> which stabilizes [0..k] pointwise
    #   [so h(0) = 0, h(1) = 1, ... h(k) = k]
    for k in range(n+1): # [0, n]
        gs_new = generators_of_stabilizer(gs_prev, k, n)
        if use_sims_filter: gs_new = sims_filter(gs_new, n) # performance
        Ggens[k] = gs_new
        gs_prev = gs_new
    return Ggens


def compute_order(gs: List[Permutation], n: int):
    schrier = schrier_decomposition(gs, n)
    # let's compute |schrier[i]|/|schrier[i+1]|.
    # Recall that schrier[i] ~= Stab(schrier[i-1], i)
    # Recall that schrier[i+1] ~= Stab(schrier[i], i+1)
    # Recall that |schrier[i+1]|/|Stab(schrier[i], i+1)| ~= Orb(schrier[i+1],i+1) 
    total_size = 1
    for i in range(-1, len(schrier)):
        if i == n-1: break
        hs = schrier[i]
        # intuition: G0 has G1=Stab(G0, 1). Size of |G0|/|Stab(G0, 1)| ~= Orb(G0, 1).
        # so Gi should act on (i+1)
        vs = schrier_vector(hs, k=i+1, n=n)
        orb_size = sum([1 for v in vs if v is not None])
        print(f"orb size of {hs} is {orb_size}")
        total_size *= orb_size
    return total_size


-/