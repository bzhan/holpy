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
from data.real import realT
from data import set as hol_set
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
        elif T == realT:
            return z3.Real(t.name)
        elif T == TFun(realT, realT):
            return z3.Function(t.name, z3.RealSort(), z3.RealSort())
        elif T == TFun(realT, boolT):
            return z3.Function(t.name, z3.RealSort(), z3.BoolSort())
        elif T == hol_set.setT(nat.natT):
            return z3.Function(t.name, z3.IntSort(), z3.BoolSort())
        elif T == hol_set.setT(realT):
            return z3.Function(t.name, z3.RealSort(), z3.BoolSort())
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
    elif t.head.is_const_name('plus'):
        return convert(t.arg1) + convert(t.arg)
    elif t.head.is_const_name('minus'):
        return convert(t.arg1) - convert(t.arg)
    elif t.head.is_const_name('uminus'):
        return -convert(t.arg)
    elif t.head.is_const_name('times'):
        return convert(t.arg1) * convert(t.arg)
    elif t.head.is_const_name('less_eq'):
        return convert(t.arg1) <= convert(t.arg)
    elif t.head.is_const_name('less'):
        return convert(t.arg1) < convert(t.arg)
    elif t.head.is_const_name('greater_eq'):
        return convert(t.arg1) >= convert(t.arg)
    elif t.head.is_const_name('greater'):
        return convert(t.arg1) > convert(t.arg)
    elif t.head.is_const_name('real_divide'):
        return convert(t.arg1) / convert(t.arg)
    elif t.head.is_const_name('zero'):
        return 0
    elif t.head.is_const_name('one'):
        return 1
    elif t.head.is_const_name('of_nat') and nat.is_binary(t.arg):
        return nat.from_binary(t.arg)
    elif t.head.is_const_name('max'):
        a, b = convert(t.arg1), convert(t.arg)
        return z3.If(a >= b, a, b)
    elif t.head.is_const_name('abs'):
        a = convert(t.arg)
        return z3.If(a >= 0, a, -a)
    elif t.head.is_const_name('member'):
        a, S = convert(t.arg1), convert(t.arg)
        return S(a)
    elif t.head.is_const_name('subset'):
        if t.arg1.T.args[0] == nat.natT:
            S, T = convert(t.arg1), convert(t.arg)
            z3_v = z3.Int("_u")
            return z3.ForAll([z3_v], z3.Implies(S(z3_v), T(z3_v)))
        elif t.arg1.T.args[0] == realT:
            S, T = convert(t.arg1), convert(t.arg)
            z3_v = z3.Real("_u")
            return z3.ForAll([z3_v], z3.Implies(S(z3_v), T(z3_v)))
        else:
            print("convert: unsupported constant " + repr(t))
            raise NotImplementedError
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
        # print(convert(t))
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
