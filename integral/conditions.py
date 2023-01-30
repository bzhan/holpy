"""Conditions"""

from typing import Optional

from integral import expr
from integral.expr import Expr
from integral import latex

class Conditions:
    """A condition is represented by a list of boolean expressions."""
    def __init__(self, conds=None):
        self.data = list()
        if conds is not None:
            self.data.extend(conds)

    def __str__(self):
        return ", ".join(str(cond) for cond in self.data)

    def add_condition(self, cond: Expr):
        assert isinstance(cond, Expr)
        self.data.append(cond)

    def __eq__(self, other):
        return isinstance(other, Conditions) and self.data == other.data

    def export(self):
        res = list()
        for cond in self.data:
            res.append({
                "cond": str(cond),
                "latex_cond": latex.convert_expr(cond)
            })
        return res


def is_positive(e: Expr, conds: Optional[Conditions]) -> bool:
    """Return whether conditions imply e is positive."""
    if conds is None:
        return False

    if e.is_const():
        return e.val > 0

    if e.is_fun() and e.func_name == 'sqrt':
        if is_positive(e.args[0], conds):
            return True
    if e.is_fun() and e.func_name == 'exp':
        return True
    if e == expr.E:
        return True
    if e.is_power():
        if is_positive(e.args[0], conds):
            return True
    if e.is_plus():
        if is_positive(e.args[0], conds) and e.args[1].is_power() and e.args[1].args[1].val % 2 == 0:
            return True
        if is_not_negative(e.args[0], conds) and is_positive(e.args[1], conds):
            return True
    if e.is_integral():
        l, h = e.lower, e.upper
        if is_positive(e.body, conds) and l.is_const() and h.is_inf() or \
                l.is_const() and h.is_const() and l < h:
            return True
    for cond in conds.data:
        if cond.is_greater() and cond.args[0] == e and cond.args[1].is_const() and cond.args[1].val >= 0:
            return True
        if cond.is_greater_eq() and cond.args[0] == e and cond.args[1].is_const() and cond.args[1].val > 0:
            return True
        if e.is_plus():
            if cond.is_greater_eq() and cond.args[0] == e.args[0] and cond.args[1].is_const() and \
                e.args[1].is_const() and cond.args[1].val + e.args[1].val > 0:
                return True

    return False

def is_not_negative(e: Expr, conds: Optional[Conditions]) -> bool:
    if conds is None:
        return False

    if e.is_const():
        return True if e.val >= 0 else False
    elif e.is_plus():
        if all(is_not_negative(arg, conds) for arg in e.args):
            return True
    elif e.is_times():
        # a * a >= 0
        if e.args[0] == e.args[1]:
            return True
    elif e.is_power():
        if e.args[1] == expr.Const(2):
            return True
    else:
        # TODO: many cases are missing
        return False

def is_negative(e: Expr, conds: Optional[Conditions]) -> bool:
    """Return whether conditions imply e is negative."""
    if conds is None:
        return False

    if is_not_negative(e, conds):
        return False
    if e.is_const():
        return e.val < 0

    if e.is_uminus() and is_positive(e.args[0], conds):
        # e = -x
        return True
    if e.is_divides() and is_positive(e.args[0], conds) and is_negative(e.args[1], conds):
        # e = a / b
        return True
    if e.is_power() and is_negative(e.args[0], conds) and e.args[1] == expr.Const(-1):
        # e = b ^ -1
        return True
    if e.is_minus() and e.args[1].is_const() and e.args[1].val > 0:
        # -y^2 - 1
        if e.args[0].is_uminus():
            a = e.args[0].args[0]
            if a.ty == expr.OP and a.op == '^' and a.args[1].is_const and a.args[1].val % 2 == 0:
                return True
    for cond in conds.data:
        if cond.is_less() and cond.args[0] == e and cond.args[1].is_const() and cond.args[1].val <= 0:
            return True
        if cond.is_less_eq() and cond.args[0] == e and cond.args[1].is_const() and cond.args[1].val < 0:
            return True
        if cond.is_greater() and (cond.args[1] - cond.args[0]).normalize() == e.normalize():
            return True
    return False
