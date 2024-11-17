#!/usr/bin/env python3
import pytest
from dataclasses import field, dataclass
from random import random, randint, seed
from rand_gen import randbool
from typing import Dict, Set, List, Option
from truth_table import TruthTable, enumerate_truth_tables

class BDD:
    """
    A data structure for representing truth tables in 'if normal form',
    with moreover, the guarantees that:
        + variables are tested in the same order each time, and
        + no redundant tests are performed (i.e. tests where the left and right cases the same values).
    """
    pass

@dataclass(frozen=True)
class BDDNode(BDD):
    var : int
    lo : BDD
    hi : BDD

    def largest_var(self): 
        return max(var, lo.largest_var(), hi.largest_var())

    def eval(self, assignment : int) -> bool:
        if assignment & (1 << var):
            return self.hi.eval(assignment)
        else:
            return self.lo.eval(assignment)

@dataclass(frozen=True)
class BDDVal(BDD):
    val : bool

    def largest_var(self):
        return 0

    def eval(self, assignment : int) -> bool:
        return val

@dataclass
class BDDCtx:
    canon_node : dict[(int, BDD, BDD), BDD] = field(default_factory=dict)
    num_vars : int = 0
    t : BDD = BDDVal(True)
    f : BDD = BDDVal(False)

    def const(self, b):
        return self.t if b else self.f

    def false(self):
        return self.f

    def true(self):
        return self.t

    def node(self, var : int, lo : BDD, hi : BDD):
        self.num_vars = max(var, self.num_vars)
        if (var, lo, hi) in self.canon_node:
            return self.canon_node[(var, lo, hi)]
        node = BDDNode(var, lo, hi)
        self.canon_node[(var, lo, hi)] = node
        return node
    
    def _assignment(self, nvars : int, a : int, val : bool, x : int) -> BDD:
        assert x >= -1
        if x == -1:
            return self.false()
        
        bit = a & (1 << x)
        if bit:
            return node(x, self.false(), self._assignment(nvars, a, x-1))
        else:
            return node(x, self._assignment(nvars, a, x-1), self.false())

    def assignment(self, nvars : int, a : int, val : bool) -> BDD:
        """build a BDD that is true for the assignment 'a' and false otherwise"""
        self._assignment(n, a, val, nvars-1)
    
    def _apply(self, op : bool -> bool -> bool, lhs : BDD, rhs : BDD, cache : Dict[(BDD, BDD), BDD]) -> BDD:
        """
        Computes a new truth_table,
        such that out[a] = op(lhs[a], rhs[a]),
        when we view the BDD as a truth table that maps variable assignments to boolean values.


        Key idea of the implementation:
        See that we can think of the BDD
        as telling us the sequence of assignments we need to inspect, before we get to a concrete value.

        So, we inspect the assignment, variable by variable, but use the structure of the BDDs
        to "skip" looking at variables that do not need to be looked at.
        * If both BDDS are values:
            + We evaluate, and return the value.
        * If the left BDD is a value, then it has already "settled". Now, let the right node be a Node.
            + We build another Node, since the right BDD has not settled on a value yet.
            + We recurse, and call 'apply' to build the BDDs for the lo and hi subtrees.
        * Mutatis mutandis for the case of (value, variable).
        * If both sides are nodes:
           + We case split on their variables.
           + If lhs.var == rhs.var, then they scrutinize the same variable.
             - This means that the 'lo' of both will inspect the same variable,
                and so, we should apply the operation to the 'lo' of both branches.
             -  similarly, this means that the 'hi' of both will inspect the same variable, and so,
                we should apply the operation to the 'hi' of both branches.
           + If lhs.var < rhs.var,
             - This means that the RHS has more variables to inspect than the LHS.
             - So, we consider both cases of the RHS, and ask to merge with the LHS in both cases.
             - In this case, we are "short circuiting" the otherwise 'unused' nodes that we would have from the occurrence of the variable in the LHS.
             - In some sense, this is an optzn available to us because we are working with ROBDDs.
        """
        assert isinstance(lhs, BDD)
        assert isinstance(rhs, BDD)
        if isinstance(lhs, BDDVal) and isinstance(rhs, BDDVal):
            out = self.const(op(lhs.val, rhs.val))
        
        elif isinstance(lhs, BDDNode) and isinstance(rhs, BDDNode):
            if lhs.var == rhs.var:
                out = self.node(lhs.var, self._apply(op, lhs.lo, rhs.lo, cache), self._apply(op, lhs.hi, rhs.hi, cache))
            elif lhs.var < rhs.var:
                # LHS is "deeper" in the final tree than the RHS. So we ask to merge the children of RHS with the lhs.
                out = self.node(rhs.var, self._apply(op, lhs, rhs.lo, cache), self._apply(op, lhs, rhs.hi, cache))
            else:
                assert lhs.var > rhs.var
                # RHS is "deeper", so we case split on the LHS first.
                out = self.node(lhs.var, self._apply(op, lhs.lo, rhs, cache), self._apply(op, lhs.hi, rhs, cache))

        elif isinstance(lhs, BDDVal) and isinstance(RHS, BDDNode):
            out = self.node(rhs.var, self._apply(op, lhs, rhs.lo, cache), self._apply(op, lhs, rhs.hi, cache))
        
        elif isinstance(lhs, BDDNode) and isinstance(rhs, BDDVal):
            out = self.node(lhs.var, self._apply(op, lhs.lo, rhs, cache), self._apply(op, lhs.hi, rhs, cache))
        
        else:
            raise RuntimeError(f"unreachable case in _apply. lhs: {lhs}, rhs: {rhs}")
        
        assert out is not None
        cache[(lhs, rhs)] = out
        return out
    
    def _restrict(self, bdd : BDD, x : int, v : bool, cache : Dict[BDD, BDD]) : (BDD, bool)
        """
        Restricts a bdd's variable to a value, and returns if the restriction was made.
        """
        if bdd in cache:
            return cache[bdd]

        if isinstance(bdd, BDDVal):
            out = bdd
            cache[bdd] = out 
            return (out, False)
        
        if isinstance(bdd, BDDNode):
            # BDD may contain 'x'
            if bdd.var <= x:
                if bdd.var == x:
                    # Restrict the BDD, so return whatever we get by following the hi(lo) branch as appropriate.
                    out = bdd.hi if v else bdd.lo 
                    # TODO: do we need to call restrict on out()?
                    # Mu intuition says no, but the CMI lecture notes by madhavan say yes?
                    cache[bdd] = out 
                    return (out, True)
                else:
                    # the variable might still appear, so let's recurse.
                    (lo, lo_changed) = self._restrict(bdd.lo, x, v, cache)
                    (hi, hi_changed) = self._restrict(bdd.hi, x, v, cache)
                    out = self.node(bdd.var, lo, hi, (lo_changed or hi_changed))
                    cache[bdd] = out 
                    return (out, lo_changed or hi_changed)

            else:
                out = bdd
                cache[bdd] = out 
                return (out, False)

    def restrict(self, var : int, val : bool) -> (BDD, bool):
        """
        partially apply BDD with 'var = val', and return if this changed the BDD.
        """
        self._restrict(var, val, dict())
    

    def bdd_or(self, lhs : BDD, rhs : BDD) -> BDD:
        """compute pointwse bitwise OR of truth tables"""
        return self.apply(lambda x y : x or y, lhs, rhs)

    def bdd_and(self, lhs : BDD, rhs : BDD) -> BDD:
        """compute pointwise bitwise AND of truth tables"""
        return self.apply(lambda x y : x and y, lhs, rhs)
    
    def exists(self, bdd : BDD, x : int) -> (BDD, bool):
        """
        quantifier eliminate the variable 'x'
        exists v, bdd[x := v] = T iff (bdd [x := F] \/ bdd[x := T])
        """
        (false_bdd, false_changed) = restrict(bdd, x, False)
        (true_bdd, true_changed) = restrict(bdd, x, True)
        return (self.bdd_or(false_bdd, true_bdd), false_changed or true_changed)
        return 

    def _substitute(self, bdd : BDD, x : int, val : BDD, cache : Dict[BDD, BDD]) -> (BDD, bool):
        """
        Compute bdd [x := val]. That is, we substitute the expression 'val'
        for the variable 'x' in the BDD's 'ite normal form'.

        Return the new BDD, and whether the BDD was changed by this substitution.
        """

        if bdd in cache:
            return (cache[bdd], False)

        if isinstance(val, BDDVal):
            # We have fixed enough variables that we see the raw value, so we
            # perform the restriction, which is the best implementation
            # w could have had.
            (out, is_changed) = self.restrict(bdd, x, val.val)
            cache[bdd] = out 
            return (out, is_changed)
        
        assert isinstance(val, BDDNode) # no luck, val is still a node.
        
        if isinstance(bdd, BDDVal):
            out = bdd
            cache[bdd] = out
            return (out, False)

        assert isinstance(bdd, BDDNode)

        # can't get x anymore
        if bdd.var < x:
            out = bdd 
            cache[bdd] = out 
            return (out, False)
        elif bdd.var == x
            # we are substituting 'x' with the value 'val'.
            pass 
        else:
            # we must merge 'val' with 'bdd'.
            if bdd.var == val.var:
                (lo, lo_changed) = self._substitute(bdd.lo, x, val.lo, cache)
                (hi, hi_changed) = self._substitute(bdd.hi, x, val.hi, cache)
                out = self.node(bdd.var, lo, hi)
                cache[bdd] = out 
                return (out, lo_changed or hi_changed)

            elif bdd.var < val.var:
            else:

                
        
        assert isinstance(val, BDDNode)




    def substitute(self, bdd : BDD, x : int, val : BDD) -> (BDD, bool):
        """
        Compute bdd [x := val]. That is, we substitute the expression 'val'
        for the variable 'x' in the BDD's 'ite normal form'.

        Return the new BDD, and whether the BDD was changed by this substitution.
        """





# that if a node is not the terminal 0, it has at least one path leading 
def bdd_any_sat(bdd : BDD) : Option[int]
    """
    Return any satisfying assignment, if available.
    This depends on the key invariant of a ROBDD
    """


def assert_bdd_ordered(bdd : BDD, nvars : int) -> bool:
    assert isinstance(bdd, BDD)
    print(bdd)
    if isinstance(bdd, BDDVal):
        return True
    assert isinstance(bdd, BDDNode)
    assert bdd.var < nvars
    assert_bdd_ordered(bdd.lo, bdd.var)
    assert_bdd_ordered(bdd.hi, bdd.var)


def truth_table_of_bdd(bdd : BDD, nvars : int) -> TruthTable:
    """build a truth table from a BDD"""
    tt = TruthTable(nvars)
    for a in range(0, 1 << nvars):
        tt.set_val(a, bdd.eval(a))

def assert_bdd_reduced (bdd : BDD, nvars : int, tts : Dict[TruthTable, BDD]) :
    """Check that the BDD is reduced: That is, for every node, it creates a unique truth table"""
    tt = None
    if isinstance(bdd, BDDVal):
        if bdd.val:
            tt = TruthTable.true(nvars)
        else:
            tt = TruthTable.false(nvars)

    else:
        assert(isinstance(bdd, BDDNode))
    tts_lo = assert_bdd_reduced(bdd.lo, nvars, tts).true_assignments
    tts_hi = assert_bdd_reduced(bdd.hi, nvars, tts).true_assignments
    tts_hi = set(map(lambda x : x | (1 << bdd.var), tts_hi))
    tt = TruthTable(n, tts_lo.union(tts_hi))
    
    assert tt is not None
    # if we have the truth table, then it must be us!
    # otherwise, throw an error.
    if tt in tts:
        assert tts[tdd] == bdd
    else:
        tts[tt] = bdd
    return tts


def bdd_of_truth_table(tt : TruthTable, ctx : BDDCtx) -> BDD:
    """build a BDD from a truth table"""
    # start with the false bdd
    bdd = ctx.false()
    # for every true assignment, add the assignment into the BDD.
    for a in tt.true_assignments:
        bdd = ctx.bdd_or(bdd, ctx.assignment(tt.nvars, a))
    return bdd


def test_bdd_faithful(nvars : int):
    """
    Test that the BBDs faithfully represent the truth tables
    """
    for tt in enumerate_truth_tables(nvars):
        ctx = BDDCtx()
        bdd = bdd_of_truth_table(tt, ctx)
        assert_bdd_ordered(bdd, nvars)
        tt2 = truth_table_of_bdd(bdd)
        assert tt == tt2 
        
def test_bdds_unique(nvars : int):
    # enumerate all truth tables, build BDDs, and check that we get unique bbds each time.
    bdds = []
    for tt in enumerate_truth_tables(nvars):
        ctx = BDDCtx()
        bdd = bdd_of_truth_table(tt, ctx)
        assert_bdd_ordered(bdd, nvars)
        bdds.append(bdd)
    # reduce the set of BDDs by removing duplicates
    bdds = list(set(bdds))
    # check that the number of BDDs is correct
    assert len(bdds) == 2 ** (2 ** nvars)

@pytest.fixture(autouse=True)
def nvars(): return 4
