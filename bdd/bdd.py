#!/usr/bin/env python3
from typing import *
from dataclasses import *

class BDD:
    pass

@dataclass(frozen=True)
class BDDNode(BDD):
    var : int
    lo : BDD
    hi : BDD

@dataclass(frozen=True)
class BDDVal(BDD):
    val : bool

@dataclass
class BDDCtx:
    canon_node : dict[(int, BDD, BDD), BDD] = {}
    num_vars : int = 0
    t : BDD = BDDVal(True)
    f : BDD = BDDVal(False)

    def const(self, b):
        return self.t if b else self.f

    def node(self, var : int, lo : BDD, hi : BDD):
        self.num_vars = max(var, self.num_vars)
        if (var, lo, hi) in self.canon_node:
            return self.canon_node[(var, lo, hi)]
        node = BDDNode(var, lo, hi)
        self.canon_node[(var, lo, hi)] = node
        return node

class AIG:
    pass

@dataclass(frozen=True)
class AIGVal(AIG):
    val : bool


@dataclass(frozen = True)
class AIGVar(AIG):
    x : int

@dataclass(frozen=True)
class AIGNode(AIG):
    linv : bool
    rinv : bool
    l : AIGNode
    r : AIGNode


def eval_const_aig(l : (bool, bool), r : (bool, bool)) -> bool:
    return (l[0] ^ l[1]) & (r[0] ^ r[1])

def eval_unit_aig(l : bool, r : bool) -> bool:  
    # x &&& x  = T
    # x &&& !x = F
    # !x &&& x = F
    # !x &&& !x = T
    return l == r

@dataclass
class AIGCtx:
    canon_node: dict[(bool, AIGNode, AIGNode), AIGNode] = {}
    canon_var : dict[int, AIGNode] = {}

    t : AIGVal = AIGVal(true)
    f : AIGVal  = AIGVal(false)

    def __init__(self):
        self.canon_node = {}

    def const(self, b):
        return self.t if b else self.f

    def var(self, x):
        if x in self.canon_var:
            return self.canon_var[x]
        o = AIGVar(x)
        self.canon_var[x] = o
        return o

    def _mkNode(self : bool, l : (AIGNode, bool), r : (AIGNode, bool)):
        if l[0] == r[0]:
            return self.const(eval_unit_aig(l[1], r[1]))
        # constant fold.
        if isinstance(l[0], AIGVal) and isinstance(r[0], AIGVal):
            return self.const(eval_const_aig((l[0].val, l[1]), (r[0].val, r[1])))

        if (neg, l, r) in self.canon_node:
            return self.canon_node[(neg, l, r)]
        node = AIGNode(neg, l, r)
        self.canon_node[(neg, l, r)] = node 
        return node 

    def mkAnd(self, l : AIGNode, r : AIGNode):
        return self._mkNode((l, False), (r, False))
        
    def mkNot(self, n : AIGNode):
        return self._mkNode((self.t, False), (self.x, True))

    def mkOr(self, l : AIGNode, r : AIGNode):
        # !(A && B) = !a || !b
        return self.mkNot(self._mkNode((l, True), (r, True)))

    def mkXor(self, l : AIGNode, r : AIGNode):
        return self.mkOr(mkAnd(l, mkNot(r)), mkAnd(mkNot(l)), r)

    def subst(self, aig : AIGNode, x : int, val: AIGNode) -> AIG:
        if isinstance(aig, AIGVal):
            return aig
        if isinstance(aig, AIGVar):
            if aig.var == x:
                return val 
            else:
                return aig 
        assert isinstance(aig, AIGNode)
        return self._mkNode((subst(aig.l, x, val), aig.linv), (subst(aig.r, x, val), aig.rinv))

def aig_to_bdd_aux(aig : AIG, bdd_ctx : BDDCtx, x : int) -> BDD: 
    """build a BDD from an and-inverter graph"""
    if x > bdd_ctx.num_vars:
        return bdd_ctx.f

def aig_to_bdd(aig : AIG, aig_ctx : AIGCtx, bdd_ctx : BDDCtx) -> BDD: 
    """build a BDD from an and-inverter graph"""

# TODO: Tseytin transformation
