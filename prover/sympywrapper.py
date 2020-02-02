# Author: Bohua Zhan

"""Use sympy's solveset to decide certain real inequalities
on intervals.

"""

import sympy
from fractions import Fraction

from kernel.type import RealType
from kernel import term
from kernel.term import Term
from kernel.thm import Thm
from kernel.macro import global_macros
from data import nat
from data import real
from data import set as hol_set
from logic import auto
from logic import logic
from logic.logic import TacticException
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
        if t.T == RealType:
            return sympy.Symbol(t.name)
        else:
            raise SymPyException("convert: unexpected variable type: %s" % str(t.T))
    elif t == real.pi:
        return sympy.pi
    elif t.is_number():
        val = t.dest_number()
        if isinstance(val, Fraction):
            return sympy.Number(val.numerator) / sympy.Number(val.denominator)
        else:
            return sympy.Number(val)
    elif t.is_plus():
        return convert(t.arg1) + convert(t.arg)
    elif t.is_minus():
        return convert(t.arg1) - convert(t.arg)
    elif t.is_uminus():
        return -convert(t.arg)
    elif t.is_times():
        return convert(t.arg1) * convert(t.arg)
    elif t.is_divides():
        return convert(t.arg1) / convert(t.arg)
    elif t.is_nat_power() and t.arg.is_number():
        return convert(t.arg1) ** t.arg.dest_number()
    elif t.is_real_power():
        return convert(t.arg1) ** convert(t.arg)
    elif t.is_comb('real_closed_interval', 2):
        return sympy.Interval(convert(t.arg1), convert(t.arg))
    elif t.is_comb('real_open_interval', 2):
        return sympy.Interval.open(convert(t.arg1), convert(t.arg))
    elif t.is_comb('sqrt', 1):
        return sympy.sqrt(convert(t.arg))
    elif t.is_comb('abs', 1):
        return sympy.Abs(convert(t.arg))
    elif t.is_comb('exp', 1):
        return sympy.exp(convert(t.arg))
    elif t.is_comb('log', 1):
        return sympy.log(convert(t.arg))
    elif t.is_comb('sin', 1):
        return sympy.sin(convert(t.arg))
    elif t.is_comb('cos', 1):
        return sympy.cos(convert(t.arg))
    elif t.is_comb('tan', 1):
        return sympy.tan(convert(t.arg))
    elif t.is_comb('cot', 1):
        return sympy.cot(convert(t.arg))
    elif t.is_comb('sec', 1):
        return sympy.sec(convert(t.arg))
    elif t.is_comb('csc', 1):
        return sympy.csc(convert(t.arg))
    elif t.is_greater_eq():
        return convert(t.arg1) >= convert(t.arg)
    elif t.is_greater():
        return convert(t.arg1) > convert(t.arg)
    elif t.is_less_eq():
        return convert(t.arg1) <= convert(t.arg)
    elif t.is_less():
        return convert(t.arg1) < convert(t.arg)
    else:
        raise SymPyException("Unable to convert " + str(t))

def solve_goal(goal):
    """Attempt to solve goal using sympy."""
    if goal.is_not() and goal.arg.is_equals():
        try:
            lhs, rhs = convert(goal.arg.lhs), convert(goal.arg.rhs)
        except SymPyException:
            return False

        return lhs != rhs
    elif goal.is_equals():
        try:
            lhs, rhs = convert(goal.lhs), convert(goal.rhs)
        except SymPyException:
            return False

        return lhs == rhs
    else:
        try:
            sympy_goal = convert(goal)
        except SymPyException:
            return False

        return sympy_goal == True

solveset_cache = dict()

def solveset_wrapper(goal, var, interval):
    if (goal, var, interval) in solveset_cache:
        solveset_cache[(goal, var, interval)]['count'] += 1
        return solveset_cache[(goal, var, interval)]['res']
    else:
        res = sympy.solveset(goal, var, interval)
        solveset_cache[(goal, var, interval)] = {'count': 1, 'res': res}
        return res

def solve_with_interval(goal, cond):
    """Attempt to solve goal using sympy's solveset function."""
    if not (hol_set.is_mem(cond) and cond.arg1.is_var() and 
            (cond.arg.is_comb("real_closed_interval", 2) or
             cond.arg.is_comb("real_open_interval", 2))):
        return False

    var = convert(cond.arg1)
    interval = convert(cond.arg)
    
    if goal.is_not() and goal.arg.is_equals():
        try:
            sympy_goal = convert(goal.arg.arg1) - convert(goal.arg.arg)
        except SymPyException:
            return False

        # print("Sympy solve: ", sympy_goal, " on interval ", interval)
        res = solveset_wrapper(sympy_goal, var, interval)
        # print("Result: ", res)
        return res == sympy.EmptySet

    try:
        sympy_goal = convert(goal)
    except SymPyException:
        return False

    # print("Sympy solve: ", sympy_goal, " on interval ", interval)
    try:
        res = solveset_wrapper(sympy_goal, var, interval)
    except TypeError:  # raised by Sympy
        print("TypeError")
        return False

    # print("Result: ", res)
    return res == interval

class SymPyMacro(ProofMacro):
    """Macro invoking sympy."""
    def __init__(self):
        self.level = 0  # No expand implemented for sympy.
        self.sig = Term
        self.limit = None

    def can_eval(self, goal, prevs):
        if len(prevs) == 0:
            return solve_goal(goal)
        elif len(prevs) == 1:
            return solve_with_interval(goal, prevs[0].prop)
        else:
            return False

    def eval(self, goal, prevs):
        assert self.can_eval(goal, prevs), "sympy: not solved."

        return Thm(sum([th.hyps for th in prevs], ()), goal)

    def expand(self, prefix, args, prevs):
        raise NotImplementedError


def sympy_solve(goal, pts):
    if pts is None:
        pts = []

    macro = SymPyMacro()
    if macro.can_eval(goal, pts):
        th = Thm(sum([th.hyps for th in pts], ()), goal)
        return ProofTermDeriv('sympy', args=goal, prevs=pts, th=th)
    else:
        raise TacticException

auto.add_global_autos(real.greater_eq, sympy_solve)
auto.add_global_autos(real.greater, sympy_solve)
auto.add_global_autos(real.less_eq, sympy_solve)
auto.add_global_autos(real.less, sympy_solve)

auto.add_global_autos_neg(real.equals, sympy_solve)

auto.add_global_autos(nat.greater_eq, sympy_solve)
auto.add_global_autos(nat.greater, sympy_solve)
auto.add_global_autos(nat.less_eq, sympy_solve)
auto.add_global_autos(nat.less, sympy_solve)

auto.add_global_autos_neg(nat.equals, sympy_solve)

global_macros.update({
    "sympy": SymPyMacro(),
})
