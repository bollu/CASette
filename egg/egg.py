# https://bernsteinbear.com/blog/whats-in-an-egraph/
from __future__ import annotations
from dataclasses import dataclass
import itertools
from typing import Optional

every_op = []

@dataclass
class Expr:
    forwarded: Optional[Expr] = dataclasses.field(
        default=None,
        init=False,
        compare=False,
        hash=False,
    )

    def __post_init__(self) -> None:
        global every_op
        every_op.append(self)

    def find(self) -> Expr:
        """Return the representative of the set containing `self`."""
        expr = self
        while expr is not None:
            next = expr.forwarded
            if next is None:
                return expr
            expr = next
        return expr

    def make_equal_to(self, other) -> None:
        """Union the set containing `self` with the set containing `other`."""
        found = self.find()
        if found is not other:
            found.forwarded = other

@dataclass
class Const(Expr):
    value: int

@dataclass
class Var(Expr):
    name: str

@dataclass
class BinaryOp(Expr):
    left: Expr
    right: Expr

@dataclass
class Add(BinaryOp):
    pass

@dataclass
class Mul(BinaryOp):
    pass

@dataclass
class Div(BinaryOp):
    pass

@dataclass
class LeftShift(BinaryOp):
    pass


def is_const(op: Expr, value: int) -> bool:
    return isinstance(op, Const) and op.value == value

def optimize_one(op: Expr) -> None:
    if isinstance(op, BinaryOp):
        left = op.left.find()
        right = op.right.find()
        if isinstance(op, Add):
            if isinstance(left, Const) and isinstance(right, Const):
                op.make_equal_to(Const(left.value + right.value))
            elif is_const(left, 0):
                op.make_equal_to(right)
            elif is_const(right, 0):
                op.make_equal_to(left)
        elif isinstance(op, Mul):
            if is_const(left, 1):
                op.make_equal_to(right)
            elif is_const(right, 1):
                op.make_equal_to(left)
            elif is_const(right, 2):
                op.make_equal_to(Add(left, left))
                op.make_equal_to(LeftShift(left, Const(1)))

def optimize(ops: list[Expr]):
    for op in ops:
        optimize_one(op.find())

def eg1():
  ops = [
      a := Const(1),
      b := Const(2),
      c := Add(a, b),
  ]
  print("BEFORE:")
  for op in ops:
      print(f"v{op.id} =", op.find())
  optimize(ops)
  print("AFTER:")
  for op in ops:
      print(f"v{op.id} =", op.find())
eg1()
  

def discover_eclasses(ops: list[Expr]) -> dict[Expr, set[Expr]]:
    eclasses: dict[Expr, set[Expr]] = {}
    for op in ops:
        found = op.find()
        if found not in eclasses:
            # Key by the representative
            eclasses[found] = set()
        eclasses[found].add(op)
        if op is not found:
            # Alias the entries so that looking up non-representatives also
            # finds equivalent operations
            eclasses[op] = eclasses[found]
    return eclasses

def eg2():
  print("ECLASSES:")
  eclasses = discover_eclasses(every_op.copy())
  for op in ops:
      print(f"v{op.id} =", eclasses[op])
eg2()


def eg3():
  ops = [
      a := Var("a"),
      b := Const(2),
      c := Mul(a, b),
      d := Div(c, b),
  ]

def optimize_match(op: Expr, eclasses: dict[Expr, set[Expr]]):
    # Find cases of the form (a * b) / b and rewrite to a
    for e0 in eclasses[op]:
        if isinstance(e0, Div):
            div_left = e0.left
            div_right = e0.right
            for e1 in eclasses[div_left]:
                if isinstance(e1, Mul):
                    mul_left = e1.left
                    mul_right = e1.right
                    if mul_right == div_right:
                        op.make_equal_to(mul_left)
                        return

# https://github.com/bytecodealliance/rfcs/blob/main/accepted/cranelift-egraph.md
def extract(program: list[Expr], eclasses: dict[Expr, set[Expr]]) -> list[Expr]:
    best_cost = float("inf")
    best_program = program
    for trial_program in itertools.product(*[eclasses[op] for op in program]):
        cost = whole_program_cost(trial_program)
        if cost < best_cost:
            best_cost = cost
            best_program = trial_program.copy()
    return best_program

# aegraphs: https://cfallin.org/pubs/egraphs2023_aegraphs_slides.pdf
