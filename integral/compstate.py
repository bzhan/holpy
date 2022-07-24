"""State of computation"""

from copy import copy
from typing import Optional, Tuple

from integral.expr import Expr, Eq, Var, Const
from integral import rules
from integral.rules import Rule
from integral.conditions import Conditions
from integral import conditions


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
        res = "Definition\n"
        res += "  %s\n" % self.eq
        return res


class Identity(StateItem):
    """Proved identity."""
    def __init__(self, eq: Expr):
        if not eq.is_equals():
            raise AssertionError("Identity: expression should be an equality")
        
        self.eq = eq

    def __str__(self):
        res = "Identity\n"
        res += "  %s\n" % self.eq
        return res


class CalculationStep(StateItem):
    """A step in the calculation."""
    def __init__(self, rule: Rule, res: Expr):
        self.rule = rule
        self.res = res

    def __str__(self):
        return "%s (%s)" % (self.res, self.rule)


class Calculation(StateItem):
    """Calculation starting from an expression.

    start: starting expression.
    conds: (optional) a list of conditions under which the calculation
        is carried out.

    """
    def __init__(self, start: Expr, *, conds: Optional[Conditions] = None):
        self.start = start
        self.steps = []
        if conds is None:
            conds = Conditions()
        self.conds = conds

    def __str__(self):
        res = "  " + str(self.start) + "\n"
        for step in self.steps:
            res += "= %s\n" % step
        return res

    def add_step(self, step: CalculationStep):
        """Add the given step to the computation."""
        self.steps.append(step)

    @property
    def last_expr(self) -> Expr:
        if self.steps:
            return self.steps[-1].res
        else:
            return self.start

    def perform_rule(self, rule: Rule):
        """Perform the given rule on the current expression."""        
        e = self.last_expr
        new_e = rule.eval(e, conds=self.conds)
        self.add_step(CalculationStep(rule, new_e))


class CalculationProof(StateItem):
    """Proof for an equation by calculation.
    
    The proof consists of calculation of left and right sides.

    """
    def __init__(self, goal: Expr, *, conds: Optional[Conditions] = None):
        if not goal.is_equals():
            raise AssertionError("CalculationProof: goal is not an equality.")

        self.goal = goal
        if conds is None:
            conds = Conditions()
        self.conds = conds

        self.lhs_calc = Calculation(self.goal.lhs, conds=self.conds)
        self.rhs_calc = Calculation(self.goal.rhs, conds=self.conds)

    def __str__(self):
        if self.lhs_calc.last_expr == self.rhs_calc.last_expr:
            res = "Proof by calculation (finished)\n"
        else:
            res = "Proof by calculation\n"
        if self.lhs_calc.steps:
            res += "LHS:\n"
            res += str(self.lhs_calc)
        if self.rhs_calc.steps:
            res += "RHS:\n"
            res += str(self.rhs_calc)
        return res


class InductionProof(StateItem):
    """Proof for an equation by induction on natural numbers.
    
    This breaks the equation goal into two goals, corresponding to the
    base case and inductive case.

    """
    def __init__(self, goal: Expr, induct_var: str, *, conds: Optional[Conditions] = None):
        if not goal.is_equals():
            raise AssertionError("InductionProof: currently only support equation goals.")

        self.goal = goal
        self.induct_var = induct_var
        if conds is None:
            conds = Conditions()
        self.conds = conds

        # Base case: n = 0
        eq0 = goal.subst(induct_var, Const(0))
        eq0 = Eq(eq0.lhs.normalize(), eq0.rhs.normalize())
        self.base_case = CalculationProof(eq0, conds=self.conds)
        
        # Inductive case:
        eqI = goal.subst(induct_var, Var(induct_var) + 1)
        eqI = Eq(eqI.lhs.normalize(), eqI.rhs.normalize())
        induct_conds = copy(self.conds)
        induct_conds.add_condition("IH", self.goal)
        self.induct_case = CalculationProof(eqI, conds=induct_conds)

    def __str__(self):
        res = "Proof by induction on %s\n" % self.induct_var
        res += "Base case: %s\n" % self.base_case.goal
        res += str(self.base_case)
        res += "Induct case: %s\n" % self.induct_case.goal
        res += str(self.induct_case)
        return res


class State:
    """Represents the global state of the proof."""
    def __init__(self, goal: Expr):
        # Final goal of the computation
        self.goal = goal

        # List of items in the computation
        self.items = []

        # Dictionary mapping function names to their definitions
        self.func_map = dict()

    def __str__(self):
        res = "Goal: %s\n" % self.goal
        for item in self.items:
            res += str(item)
        return res

    def add_item(self, item: StateItem):
        """Add an item of computation."""
        self.items.append(item)
        if isinstance(item, FuncDef):
            self.func_map[item.symb] = item
