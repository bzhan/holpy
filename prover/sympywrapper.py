# Author: Bohua Zhan

"""Use sympy's solveset to decide certain real inequalities
on intervals.

"""

import sympy

from kernel.term import Term
from kernel.thm import Thm
from kernel.macro import global_macros
from data import nat
from data import real
from data import set as hol_set
from logic import auto
from logic import logic
from logic.proofterm import ProofMacro, ProofTermDeriv
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
            raise SymPyException("Unable to convert " + str(t))
    else:
        raise SymPyException("Unable to convert " + str(t))


def solve(goal, cond):
    """Attempt to solve goal using sympy's solveset function."""
    if not (hol_set.is_mem(cond) and cond.arg1.is_var() and 
            cond.arg.head.is_const_name("real_closed_interval")):
        return False

    var = convert(cond.arg1)
    interval = convert(cond.arg)
    
    if logic.is_neg(goal) and goal.arg.is_equals():
        try:
            sympy_goal = convert(goal.arg.arg1) - convert(goal.arg.arg)
        except SymPyException:
            return False

        res = sympy.solveset(sympy_goal, var, interval)
        return res == sympy.EmptySet()

    try:
        sympy_goal = convert(goal)
    except SymPyException:
        return False

    res = sympy.solveset(sympy_goal, var, interval)
    return res == interval

class SymPyMacro(ProofMacro):
    """Macro invoking sympy."""
    def __init__(self):
        self.level = 0  # No expand implemented for sympy.
        self.sig = Term
        self.limit = None

    def can_eval(self, thy, goal, prevs):
        assert len(prevs) == 1, "SymPyMacro: expect exactly one condition"
        return solve(goal, prevs[0].prop)

    def eval(self, thy, goal, prevs):
        assert len(prevs) == 1, "SymPyMacro: expect exactly one condition"
        assert solve(goal, prevs[0].prop), "sympy: not solved."

        return Thm(sum([th.hyps for th in prevs], ()), goal)

    def expand(self, prefix, thy, args, prevs):
        raise NotImplementedError

def apply_sympy(thy, t, pts=None):
    if pts is None:
        pts = []
    return ProofTermDeriv('sympy', thy, args=t, prevs=pts)


use_sympy = False

def sympy_solve(thy, goal, pts):
    if not use_sympy:
        raise NotImplementedError

    macro = SymPyMacro()
    if macro.can_eval(thy, goal, pts):
        return apply_sympy(thy, goal, pts)
    else:
        raise NotImplementedError

auto.add_global_autos(real.greater_eq, sympy_solve)
auto.add_global_autos(real.greater, sympy_solve)
auto.add_global_autos(real.less_eq, sympy_solve)
auto.add_global_autos(real.less, sympy_solve)

auto.add_global_autos_neg(Term.equals(real.realT), sympy.solve)

global_macros.update({
    "sympy": SymPyMacro(),
})
