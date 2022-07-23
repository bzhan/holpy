"""State of computation"""

from typing import Tuple
from integral.expr import Expr, Eq, Var, Const
from integral import expr


class StateItem:
    """Items in a state of computation"""
    pass

class StateRule:
    """A rule that modifies state of computation"""
    pass

class FuncDef(StateItem):
    """Introduce a new function definition."""
    def __init__(self, eq: Expr):
        if not (eq.is_equals() and eq.lhs.is_fun()):
            raise AssertionError("FuncDef: left side should be a function")

        self.eq = eq
        self.symb = self.eq.lhs.func_name
        self.args = self.eq.lhs.args
        self.body = self.eq.rhs

        if any(not arg.is_var() for arg in self.args) or len(self.args) != len(set(self.args)):
            raise AssertionError("FuncDef: arguments should be distinct variables")

    def __str__(self):
        return str(self.eq)


class Identity(StateItem):
    """Proved identity."""
    def __init__(self, eq: Expr):
        if not eq.is_equals():
            raise AssertionError("Identity: expression should be an equality")
        
        self.eq = eq

    def __str__(self):
        return str(self.eq)


def perform_induction(eq: Expr, induct_var: str) -> Tuple[Expr, Expr]:
    if not eq.is_equals():
        raise AssertionError("perform_induction")

    # Base case: m = 0
    eq0 = eq.subst(induct_var, Const(0))
    eq0 = Eq(eq0.lhs.normalize(), eq0.rhs.normalize())

    # Inductive case:
    eqI = eq.subst(induct_var, Var(induct_var) + Const(1))
    eqI = Eq(eqI.lhs.normalize(), eqI.rhs.normalize())
    
    return (eq0, eqI)


class State:
    def __init__(self, goal):
        # Final goal of the computation
        self.goal = goal

        # List of items in the computation
        self.items = []

        # Dictionary mapping function names to their definitions
        self.func_map = dict()


    def add_item(self, item: StateItem):
        """Add an item of computation."""
        self.items.append(item)
        if isinstance(item, FuncDef):
            self.func_map[item.symb] = item
