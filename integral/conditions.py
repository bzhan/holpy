"""Conditions"""

from copy import copy

from integral.expr import Expr
from integral import latex

# A condition is represented by a dictionary mapping condition names to
# boolean expressions

class Conditions:
    def __init__(self, conds=None):
        self.data = dict()
        if conds is not None:
            for i, cond in enumerate(conds):
                self.data['C' + str(i+1)] = cond

    def add_condition(self, name: str, cond: Expr):
        self.data[name] = cond

    def __copy__(self):
        res = Conditions()
        res.data = copy(self.data)
        return res

    def export(self):
        res = list()
        for name, cond in self.data.items():
            res.append({
                "type": "Condition",
                "name": name,
                "cond": str(cond),
                "latex_cond": latex.convert_expr(cond)
            })
        return res


def is_positive(e: Expr, conds: Conditions) -> bool:
    """Return whether conditions imply e is positive."""
    if e.is_const():
        return e.val > 0

    if e.is_power():
        if is_positive(e.args[0], conds):
            return True

    for _, cond in conds.data.items():
        if cond.is_greater() and cond.args[0] == e and cond.args[1].is_const() and cond.args[1].val >= 0:
            return True
        if cond.is_greater_eq() and cond.args[0] == e and cond.args[1].is_const() and cond.args[1].val > 0:
            return True
    return False

def is_negative(e: Expr, conds: Conditions) -> bool:
    """Return whether conditions imply e is negative."""
    if e.is_const():
        return e.val < 0

    for _, cond in conds.data.items():
        if cond.is_less() and cond.args[0] == e and cond.args[1].is_const() and cond.args[1].val <= 0:
            return True
        if cond.is_less_eq() and cond.args[0] == e and cond.args[1].is_const() and cond.args[1].val < 0:
            return True
    return False
