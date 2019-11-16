# Author: Bohua Zhan

import importlib

if importlib.util.find_spec("z3"):
    import z3
    z3_loaded = True
else:
    z3_loaded = False

from kernel.type import TFun
from kernel import term
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
from util import name


class Z3Exception(Exception):
    def __init__(self, err):
        self.err = err

    def __str__(self):
        return self.err


def convert_type(T):
    if T.is_tvar():
        return z3.DeclareSort(T.name)
    if T == nat.natT or T == int.intT:
        return z3.IntSort()
    elif T == boolT:
        return z3.BoolSort()
    elif T == realT:
        return z3.RealSort()
    elif T.is_fun():
        domainT = convert_type(T.domain_type())
        rangeT = convert_type(T.range_type())
        if isinstance(domainT, tuple):
            raise Z3Exception("convert: unsupported type " + repr(T))
        if isinstance(rangeT, tuple):
            return tuple([domainT] + rangeT)
        else:
            return (domainT, rangeT)
    elif T.is_type() and T.name == 'set':
        domainT = convert_type(T.args[0])
        if isinstance(domainT, tuple):
            raise Z3Exception("convert: unsupported type " + repr(T))
        return (domainT, convert_type(boolT))
    else:
        raise Z3Exception("convert: unsupported type " + repr(T))

def convert_const(name, T):
    z3_T = convert_type(T)
    if isinstance(z3_T, tuple):
        return z3.Function(name, *z3_T)
    else:
        return z3.Const(name, z3_T)

def convert(t):
    """Convert term t to Z3 input."""
    if t.is_var():
        return convert_const(t.name, t.T)
    elif t.is_all():
        var_names = [v.name for v in term.get_vars(t.arg.body)]
        nm = name.get_variant_name(t.arg.var_name, var_names)
        v = Var(nm, t.arg.var_T)
        z3_v = convert_const(nm, t.arg.var_T)
        return z3.ForAll(z3_v, convert(t.arg.subst_bound(v)))
    elif logic.is_exists(t):
        var_names = [v.name for v in term.get_vars(t.arg.body)]
        nm = name.get_variant_name(t.arg.var_name, var_names)
        v = Var(nm, t.arg.var_T)
        z3_v = convert_const(nm, t.arg.var_T)
        return z3.Exists(z3_v, convert(t.arg.subst_bound(v)))
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
            raise Z3Exception("convert: unsupported constant " + repr(t))
    else:
        raise Z3Exception("convert: unsupported operation " + repr(t))

norm_thms = [
    'member_empty_simp',
    'member_insert',
    'member_univ_simp',
    'member_collect',
    'member_union_iff',
    'member_inter_iff',
    'set_equal_iff',
    'subset_def',
    'diff_def'
]

def norm_term(thy, t):
    # Collect list of theorems that can be used.
    th_names = [name for name in norm_thms if thy.has_theorem(name)]
    cvs = [conv.try_conv(conv.rewr_conv(th_name)) for th_name in th_names]
    cvs.append(conv.try_conv(conv.beta_conv()))
    cv = conv.top_conv(conv.every_conv(*cvs))
    while True:
        rhs = cv.eval(thy, t).rhs
        if rhs == t:
            break
        else:
            t = rhs
    return fologic.simplify(t)

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
    except Z3Exception:
        return False

class Z3Macro(ProofMacro):
    """Macro invoking SMT solver Z3."""
    def __init__(self):
        self.level = 0  # No expand implemented for Z3.
        self.sig = Term

    def eval(self, thy, args, prevs):
        if z3_loaded:
            assms = [prev.prop for prev in prevs]
            assert solve(thy, Term.mk_implies(*(assms + [args]))), "Z3: not solved."
        else:
            print("Warning: Z3 is not installed")

        return Thm(sum([th.hyps for th in prevs], ()), args)

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
        prev_ths = [state.get_proof_item(prev).th for prev in prevs]
        assms = [prev.prop for prev in prev_ths]
        goal = state.get_proof_item(id).th.prop
        assert solve(state.thy, Term.mk_implies(*(assms + [goal]))), "Z3 method: not solved"
        state.set_line(id, 'z3', args=goal, prevs=prevs)


global_macros.update({
    "z3": Z3Macro(),
})

global_methods.update({
    "z3": Z3Method(),
})
