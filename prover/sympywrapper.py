# Author: Bohua Zhan

"""Use sympy's solveset to decide certain real inequalities
on intervals.

"""

import sympy
from fractions import Fraction

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
        if t.T == real.realT:
            return sympy.Symbol(t.name)
        else:
            raise SymPyException("convert: unexpected variable type: %s" % str(t.T))
    elif t == real.pi:
        return sympy.pi
    elif nat.is_binary_nat(t):
        return sympy.Number(nat.from_binary_nat(t))
    elif real.is_binary_real(t):
        val = real.from_binary_real(t)
        if isinstance(val, Fraction):
            return sympy.Number(val.numerator) / sympy.Number(val.denominator)
        else:
            return sympy.Number(val)
    elif real.is_plus(t):
        return convert(t.arg1) + convert(t.arg)
    elif real.is_minus(t):
        return convert(t.arg1) - convert(t.arg)
    elif real.is_uminus(t):
        return -convert(t.arg)
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
        elif t.head.is_const_name('real_open_interval'):
            return sympy.Interval.open(convert(t.arg1), convert(t.arg))
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
        elif t.head == real.cot:
            return sympy.cot(convert(t.arg))
        elif t.head == real.sec:
            return sympy.sec(convert(t.arg))
        elif t.head == real.csc:
            return sympy.csc(convert(t.arg))
        elif t.head.is_const_name('greater_eq'):
            return convert(t.arg1) >= convert(t.arg)
        elif t.head.is_const_name('greater'):
            return convert(t.arg1) > convert(t.arg)
        elif t.head.is_const_name('less_eq'):
            return convert(t.arg1) <= convert(t.arg)
        elif t.head.is_const_name('less'):
            return convert(t.arg1) < convert(t.arg)
        else:
            raise SymPyException("Unable to convert " + str(t))
    else:
        raise SymPyException("Unable to convert " + str(t))

def solve_goal(goal):
    """Attempt to solve goal using sympy."""
    if logic.is_neg(goal) and goal.arg.is_equals():
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
            (cond.arg.head.is_const_name("real_closed_interval") or
             cond.arg.head.is_const_name("real_open_interval"))):
        return False

    var = convert(cond.arg1)
    interval = convert(cond.arg)
    
    if logic.is_neg(goal) and goal.arg.is_equals():
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

    def can_eval(self, thy, goal, prevs):
        if len(prevs) == 0:
            return solve_goal(goal)
        elif len(prevs) == 1:
            return solve_with_interval(goal, prevs[0].prop)
        else:
            return False

    def eval(self, thy, goal, prevs):
        assert self.can_eval(thy, goal, prevs), "sympy: not solved."

        return Thm(sum([th.hyps for th in prevs], ()), goal)

    def expand(self, prefix, thy, args, prevs):
        raise NotImplementedError


def sympy_solve(thy, goal, pts):
    if pts is None:
        pts = []

    macro = SymPyMacro()
    if macro.can_eval(thy, goal, pts):
        th = Thm(sum([th.hyps for th in pts], ()), goal)
        return ProofTermDeriv('sympy', thy, args=goal, prevs=pts, th=th)
    else:
        raise TacticException

auto.add_global_autos(real.greater_eq, sympy_solve)
auto.add_global_autos(real.greater, sympy_solve)
auto.add_global_autos(real.less_eq, sympy_solve)
auto.add_global_autos(real.less, sympy_solve)

auto.add_global_autos_neg(Term.equals(real.realT), sympy_solve)

auto.add_global_autos(nat.greater_eq, sympy_solve)
auto.add_global_autos(nat.greater, sympy_solve)
auto.add_global_autos(nat.less_eq, sympy_solve)
auto.add_global_autos(nat.less, sympy_solve)

auto.add_global_autos_neg(Term.equals(nat.natT), sympy_solve)

global_macros.update({
    "sympy": SymPyMacro(),
})
