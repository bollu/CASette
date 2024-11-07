#!/usr/bin/env python3
import pytest
from dataclasses import field, dataclass
from random import random, randint, seed
import rand_gen
from typing import Set, Dict, List

@dataclass
class TruthTable:
    n : int
    true_assignments : set[int]

    def __init__(self, n : int, true_assignments : Set[int] = set()):
        self.n = n
        for val in true_assignments:
            self.set_val(val)

    def set_val(self, a : int, val : bool = True):
        """
        set the value for the truth table for assignment 'a'
        we index into the bitvector with an integer, interpreted as a bitvector.
        """
        assert a >= 0
        assert a < 2**self.n
        if val:
            self.true_assignments.add(a)
        else:
            self.true_assignments.discard(a)

    def get_val(self, xs : int):
        return xs in self.true_assignments

    @classmethod
    def true(n : int):
        """truth table denoting constant true."""
        return TruthTable(n, set(range(0, 2 ** n)))

    @classmethod
    def false(nvars : int):
        """truth table denoting constant false."""
        return TruthTable(n, set())


def enumerate_truth_tables(n : int) -> List[TruthTable]:
    """enumerate all truth tables of size n"""
    for true_xs in rand_gen.all_subsets(list(range(2 ** n))):
        yield TruthTable(n, true_xs)


