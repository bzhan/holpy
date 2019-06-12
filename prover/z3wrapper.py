# Author: Bohua Zhan

import importlib

if importlib.util.find_spec("z3"):
    import z3
    z3_loaded = True
else:
    z3_loaded = False

from kernel.type import TFun
from kernel.term import Term, Var, boolT
from kernel.thm import Thm
from kernel.macro import ProofMacro, global_macros
from logic import logic
from data import nat
from syntax import printer


def convert(t):
    """Convert term t to Z3 input."""
    if t.is_var():
        T = t.get_type()
        if T == nat.natT:
            return z3.Int(t.name)
        elif T == TFun(nat.natT, nat.natT):
            return z3.Function(t.name, z3.IntSort(), z3.IntSort())
        elif T == TFun(nat.natT, boolT):
            return z3.Function(t.name, z3.IntSort(), z3.BoolSort())
        elif T == boolT:
            return z3.Bool(t.name)
        else:
            print("convert: unsupported type " + repr(T))
            raise NotImplementedError
    elif t.is_all():
        if t.arg.var_T == nat.natT:
            v = Var(t.arg.var_name, nat.natT)
            z3_v = z3.Int(t.arg.var_name)
            return z3.ForAll([z3_v], convert(t.arg.subst_bound(v)))
        else:
            raise NotImplementedError
    elif t.is_implies():
        return z3.Implies(convert(t.arg1), convert(t.arg))
    elif t.is_equals():
        return convert(t.arg1) == convert(t.arg)
    elif logic.is_conj(t):
        return z3.And(convert(t.arg1), convert(t.arg))
    elif logic.is_disj(t):
        return z3.Or(convert(t.arg1), convert(t.arg))
    elif logic.is_neg(t):
        return z3.Not(convert(t.arg))
    elif nat.is_plus(t):
        return convert(t.arg1) + convert(t.arg)
    elif nat.is_times(t):
        return convert(t.arg1) * convert(t.arg)
    elif nat.is_binary(t):
        return nat.from_binary(t)
    elif t.is_comb():
        return convert(t.fun)(convert(t.arg))
    elif t.is_const():
        if t == logic.true:
            return z3.BoolVal(True)
        elif t == logic.false:
            return z3.BoolVal(False)
        else:
            print("convert: unsupported constant " + repr(t))
            raise NotImplementedError
    else:
        print("convert: unsupported operation " + repr(t))
        raise NotImplementedError

def solve(t):
    """Solve the given goal using Z3."""
    s = z3.Solver()

    # First strip foralls from t.
    while Term.is_all(t):
        t = t.arg.subst_bound(Var(t.arg.var_name, t.arg.var_T))
    s.add(z3.Not(convert(t)))
    return str(s.check()) == 'unsat'

class Z3Macro(ProofMacro):
    """Macro invoking SMT solver Z3."""
    def __init__(self):
        self.level = 0  # No expand implemented for Z3.
        self.sig = Term

    def eval(self, thy, args, prevs):
        if z3_loaded:
            assert solve(args), "Z3: not solved."
        else:
            print("Warning: Z3 is not installed")

        return Thm([], args)

    def expand(self, prefix, thy, args, prevs):
        raise NotImplementedError


global_macros.update({
    "z3": Z3Macro(),
})
