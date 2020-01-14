# Author: Bohua Zhan

"""Use sympy's solveset to decide certain real inequalities
on intervals.

"""

import sympy

from data import nat
from data import real
from data import set as hol_set
import integral


class SymPyException(Exception):
    def __init__(self, err):
        self.err = err

    def __str__(self):
        return self.err


def convert(t):
    """Convert term t to SymPy term."""
    if t.is_var():
        if t.T == real.realT:
            return sympy.Symbol(t.name)
        else:
            raise SymPyException("convert: unexpected variable type: %s" % str(t.T))
    elif t == real.pi:
        return sympy.pi
    elif real.is_binary_real(t):
        return real.from_binary_real(t)
    elif real.is_plus(t):
        return convert(t.arg1) + convert(t.arg)
    elif real.is_minus(t):
        return convert(t.arg1) - convert(t.arg)
    elif real.is_times(t):
        return convert(t.arg1) * convert(t.arg)
    elif real.is_divides(t):
        return convert(t.arg1) / convert(t.arg)
    elif real.is_nat_power(t) and nat.is_binary_nat(t.arg):
        return convert(t.arg1) ** nat.from_binary_nat(t.arg)
    elif real.is_real_power(t):
        return convert(t.arg1) ** convert(t.arg)
    elif t.is_comb():
        if t.head.is_const_name('real_closed_interval'):
            return sympy.Interval(convert(t.arg1), convert(t.arg))
        elif t.head == real.sqrt:
            return sympy.sqrt(convert(t.arg))
        elif t.head == real.abs:
            return sympy.Abs(convert(t.arg))
        elif t.head == real.exp:
            return sympy.exp(convert(t.arg))
        elif t.head == real.log:
            return sympy.log(convert(t.arg))
        elif t.head == real.sin:
            return sympy.sin(convert(t.arg))
        elif t.head == real.cos:
            return sympy.cos(convert(t.arg))
        elif t.head == real.tan:
            return sympy.tan(convert(t.arg))
        elif t.head == real.greater_eq:
            return convert(t.arg1) >= convert(t.arg)
        elif t.head == real.greater:
            return convert(t.arg1) > convert(t.arg)
        elif t.head == real.less_eq:
            return convert(t.arg1) <= convert(t.arg)
        elif t.head == real.less:
            return convert(t.arg1) < convert(t.arg)
        else:
            raise NotImplementedError
    else:
        print(str(t))
        raise NotImplementedError


def solve(goal, cond):
    """Attempt to solve goal using sympy's solveset function."""
    assert hol_set.is_mem(cond) and cond.arg1.is_var() and \
        cond.arg.head.is_const_name("real_closed_interval"), "sympy_solve"

    var = convert(cond.arg1)
    interval = convert(cond.arg)
    
    assert goal.is_binop() and goal.head.is_const() and \
        goal.head.name in ('equals', 'greater_eq', 'greater', 'less_eq', 'less'), "sympy_solve"

    if goal.is_equals():
        res = sympy.solveset(convert(goal.arg1) - convert(goal.arg), var, interval)
    else:
        res = sympy.solveset(convert(goal), var, interval)

    return res == interval
