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
from logic import conv
from data import nat, int
from data.real import realT
from data import set as hol_set
from syntax import pprint, settings
from prover import fologic


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
        elif t.arg.var_T == realT:
            v = Var(t.arg.var_name, realT)
            z3_v = z3.Real(t.arg.var_name)
            return z3.ForAll([z3_v], convert(t.arg.subst_bound(v)))
        else:
            print("convert: unsupported forall type " + str(t.arg.var_T))
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
    elif t.head.is_const_name('min'):
        a, b = convert(t.arg1), convert(t.arg)
        return z3.If(a <= b, a, b)
    elif t.head.is_const_name('abs'):
        a = convert(t.arg)
        return z3.If(a >= 0, a, -a)
    elif t.head.is_const_name('member'):
        a, S = convert(t.arg1), convert(t.arg)
        return S(a)
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

norm_thms = [
    'member_empty_simp',
    'member_insert',
    'member_collect',
    'member_union_iff',
    'member_inter_iff',
    'set_equal_iff',
    'subset_def'
]

def norm_term(thy, t):
    # Collect list of theorems that can be used.
    th_names = [name for name in norm_thms if thy.has_theorem(name)]
    cvs = [conv.try_conv(conv.rewr_conv(th_name)) for th_name in th_names]
    cvs.append(conv.try_conv(conv.beta_conv()))
    cv = conv.top_conv(conv.every_conv(*cvs))
    return fologic.simplify(cv.eval(thy, t).rhs)

def solve(thy, t):
    """Solve the given goal using Z3."""
    s = z3.Solver()

    # First strip foralls from t.
    t = norm_term(thy, t)
    new_names = logic.get_forall_names(t, svar=False)
    _, As, C = logic.strip_all_implies(t, new_names, svar=False)

    try:
        for A in As:
            # print('A', convert(A))
            s.add(convert(A))
        # print('C', convert(C))
        s.add(z3.Not(convert(C)))
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
            assert solve(thy, args), "Z3: not solved."
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
        assert solve(state.thy, goal), "Z3 method: not solved"
        state.set_line(id, 'z3', args=goal, prevs=[])


global_macros.update({
    "z3": Z3Macro(),
})

global_methods.update({
    "z3": Z3Method(),
})
