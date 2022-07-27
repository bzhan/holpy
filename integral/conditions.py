"""Conditions"""

from copy import copy

from integral import expr
from integral.expr import Expr


# A condition is represented by a dictionary mapping condition names to
# boolean expressions

class Conditions:
    def __init__(self):
        self.data = dict()

    def add_condition(self, name: str, cond: Expr):
        self.data[name] = cond

    def __copy__(self):
        res = Conditions()
        res.data = copy(self.data)
        return res


def is_positive(e: Expr, conds: Conditions) -> bool:
    """Return whether conditions imply e is positive."""
    if e.is_const():
        return e.val > 0

    if e.is_power():
        if is_positive(e.args[0], conds):
            return True
    if e.is_plus():
        if is_positive(e.args[0],conds) and e.args[1].is_power() and e.args[1].args[1].val % 2 == 0:
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
    if e.ty == expr.OP and e.op == '-' and len(e.args) == 1 and is_positive(e.args[0],conds):
        return True
    for _, cond in conds.data.items():
        if cond.is_less() and cond.args[0] == e and cond.args[1].is_const() and cond.args[1].val <= 0:
            return True
        if cond.is_less_eq() and cond.args[0] == e and cond.args[1].is_const() and cond.args[1].val < 0:
            return True
    return False

def contains_const_var(e: Expr, conds: Conditions) -> bool:
    """Return whether conditions imply e contains const var"""
    all_vars = e.get_vars()
    for v in all_vars:
        if v in conds.data.keys():
            t = conds.data[v]
            if t.ty == expr.FUN and t.func_name == 'isConst' and t.args[0].ty == expr.VAR\
                    and t.args[0].name == v:
                return True
    return False
def get_const_vars(e: Expr, conds: Conditions) -> bool:
    '''return get all const vars in e based on conds'''
    all_vars = e.get_vars()
    res = []
    for v in all_vars:
        if v in conds.data.keys():
            t = conds.data[v]
            if t.ty == expr.FUN and t.func_name == 'isConst' and t.args[0].ty == expr.VAR \
                    and t.args[0].name == v:
                res.append(v)
    return res
def is_const(e: Expr, conds: Conditions) -> bool:
    """Return whether conditions imply e is const."""
    if e.is_const():
        return True
    if str(e) in conds.data.keys():
        t = conds.data[str(e)]
        if t.ty == expr.FUN and t.func_name == 'isConst':
            return True
    if not contains_const_var(e, conds) and len(e.get_vars())!=0:
        return False
    return True