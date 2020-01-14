# Author: Bohua Zhan

"""Use sympy's solveset to decide certain real inequalities
on intervals.

"""

import sympy
from sympy import solveset
from sympy import Symbol, Interval

from data import nat
from data import real


class SymPyException(Exception):
    def __init__(self, err):
        self.err = err

    def __str__(self):
        return self.err


def convert(t):
    """Convert term t to SymPy term."""
    if t.is_var():
        if t.T == real.realT:
            return Symbol(t.name)
        else:
            raise SymPyException("convert: unexpected variable type: %s" % str(t.T))
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
        if t.head == real.sqrt:
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
        else:
            raise NotImplementedError
    else:
        raise NotImplementedError
