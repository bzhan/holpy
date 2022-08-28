"""Conditions"""

from copy import copy

from integral import expr
from integral.expr import Expr
from integral import latex

# A condition is represented by a dictionary mapping condition names to
# boolean expressions

class Conditions:
    def __init__(self, conds=None):
        self.data = dict()
        self.is_assume = dict()
        if conds is not None:
            for i, cond in enumerate(conds):
                self.data['C' + str(i+1)] = cond

    def add_condition(self, name: str, cond: Expr, isAssume:bool = False):
        self.data[name] = cond
        self.is_assume[name] = isAssume

    def __copy__(self):
        res = Conditions()
        res.data = copy(self.data)
        return res

    def __eq__(self, other):
        return isinstance(other, Conditions) and self.data == other.data

    def export(self):
        res = list()
        for name, cond in self.data.items():
            if name in self.is_assume.keys() and not self.is_assume[name]:
                res.append({
                    "type": "Condition",
                    "name": name,
                    "cond": str(cond),
                    "latex_cond": latex.convert_expr(cond)
                })
        return res

    def del_assume(self, cond:Expr):
        # delete assume
        for n, c in self.data.items():
            if c == cond and self.is_assume[n]:
                self.data.pop(n)
                break

def is_positive(e: Expr, conds: Conditions) -> bool:
    """Return whether conditions imply e is positive."""
    if e.is_const():
        return e.val > 0

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

    if e.is_integral():
        l, h = e.lower, e.upper
        if is_positive(e.body, conds) and l.is_const() and h.is_inf() or l.is_const() and h.is_const() and l<h:
            return True
    for _, cond in conds.data.items():
        if cond.is_greater() and cond.args[0] == e and cond.args[1].is_const() and cond.args[1].val >= 0:
            return True
        if cond.is_greater_eq() and cond.args[0] == e and cond.args[1].is_const() and cond.args[1].val > 0:
            return True
        if e.is_plus():
            if cond.is_greater_eq() and cond.args[0] == e.args[0] and cond.args[1].is_const() and \
                e.args[1].is_const() and cond.args[1].val + e.args[1].val > 0:
                return True

    return False

def is_negative(e: Expr, conds: Conditions) -> bool:
    """Return whether conditions imply e is negative."""
    if e.is_const():
        return e.val < 0

    if e.ty == expr.OP and e.op == '-' and len(e.args) == 1 and is_positive(e.args[0],conds):
        return True
    if e.is_minus() and e.args[1].is_const() and e.args[1].val > 0:
        # -y^2 - 1
        if e.args[0].is_uminus():
            a = e.args[0].args[0]
            if a.ty == expr.OP and a.op == '^' and a.args[1].is_const and a.args[1].val % 2 == 0:
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
    for a,b in conds.data.items():
        if b.ty == expr.FUN and b.func_name == 'isConst' and b.args[0] == e:
            return True
    # contain vars but doesn't contain const var implies e is not const
    if not contains_const_var(e, conds) and len(e.get_vars())!=0:
        return False
    return True


def replaceByConds(ex:Expr, conds:Conditions):
    if conds == None:
        return ex
    # replace is_const(C) with C which is a skolem constant
    # repalce is_const(C(a,b)) with C which is a skolem constant that depends on a and b
    for k, v in conds.data.items():
        if v.is_fun() and v.func_name == 'is_const':
            if not isinstance(v.args[0], expr.Var) and not isinstance(v.args[0], expr.Fun):
                raise NotImplementedError
            name = str(v.args[0]) if v.args[0].is_var() else v.args[0].func_name
            dep_vars = [] if v.args[0].is_var() else v.args
            new_c = expr.SkolemConst(name, *dep_vars)
            ex = ex.replace(v.args[0], new_c)
    return ex