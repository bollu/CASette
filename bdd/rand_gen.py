#!/usr/bin/env python3
import pytest
from dataclasses import field, dataclass
from random import random, randint, seed
from typing import Any, List
import itertools


# === TESTING ===

@pytest.fixture(autouse=True)
def set_random_seed():
    seed(42)

def randbool() -> bool:
    return randint(0, 1) == 1


def all_subsets(xs : List[Any]):
    for i in range(len(xs) + 1):
        for subset in itertools.combinations(xs, i):
            yield set(subset)


def enumerate_assignments(nvars : int) -> List[int]:
    return range(0, 1 << nvars)

