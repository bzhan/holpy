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
from kernel.theory import Method, global_methods
from logic import logic
from data import nat, int
from syntax import pprint, settings


def convert(t):
    """Convert term t to Z3 input."""
    if t.is_var():
        T = t.get_type()
        if T == nat.natT or T == int.intT:
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
    elif int.is_binary_int(t):
        return int.from_binary_int(t)
    elif t.is_implies():
        return z3.Implies(convert(t.arg1), convert(t.arg))
    elif t.is_equals():
        return convert(t.arg1) == convert(t.arg)
    elif logic.is_conj(t):
        return z3.And(convert(t.arg1), convert(t.arg))
    elif logic.is_disj(t):
        return z3.Or(convert(t.arg1), convert(t.arg))
    elif logic.is_if(t):
        b, t1, t2 = t.args
        return z3.If(convert(b), convert(t1), convert(t2))
    elif logic.is_neg(t):
        return z3.Not(convert(t.arg))
    elif nat.is_plus(t):
        return convert(t.arg1) + convert(t.arg)
    elif nat.is_times(t):
        return convert(t.arg1) * convert(t.arg)
    elif nat.is_less_eq(t):
        return convert(t.arg1) <= convert(t.arg)
    elif nat.is_less(t):
        return convert(t.arg1) < convert(t.arg)
    elif nat.is_binary_nat(t):
        return nat.from_binary_nat(t)
    elif int.is_plus(t):
        return convert(t.arg1) + convert(t.arg)
    elif int.is_minus(t):
        return convert(t.arg1) - convert(t.arg)
    elif int.is_uminus(t):
        return -convert(t.arg)
    elif int.is_times(t):
        return convert(t.arg1) * convert(t.arg)
    elif int.is_less_eq(t):
        return convert(t.arg1) <= convert(t.arg)
    elif int.is_less(t):
        return convert(t.arg1) < convert(t.arg)
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
    try:
        s.add(z3.Not(convert(t)))
        return str(s.check()) == 'unsat'
    except NotImplementedError:
        return False

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

class Z3Method(Method):
    """Method invoking SMT solver Z3."""
    def __init__(self):
        self.sig = []

    def search(self, state, id, prevs, data=None):
        if data:
            return [data]

        return [{}]

    @settings.with_settings
    def display_step(self, state, id, data, prevs):
        return pprint.N("Apply Z3")

    def apply(self, state, id, data, prevs):
        assert z3_loaded, "Z3 method: not installed"
        goal = state.get_proof_item(id).th.prop
        assert solve(goal), "Z3 method: not solved"
        state.set_line(id, 'z3', args=goal, prevs=[])


global_macros.update({
    "z3": Z3Macro(),
})

global_methods.update({
    "z3": Z3Method(),
})
