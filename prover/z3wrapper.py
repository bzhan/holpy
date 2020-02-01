# Author: Bohua Zhan

import importlib

if importlib.util.find_spec("z3"):
    import z3
    z3_loaded = True
else:
    z3_loaded = False

from kernel.type import TFun
from kernel import term
from kernel.term import Term, Var, boolT, Implies, true, false
from kernel.thm import Thm
from kernel.macro import ProofMacro, global_macros
from kernel.theory import Method, global_methods
from kernel import theory
from logic import logic
from logic import conv
from logic.proofterm import ProofTermDeriv
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

def convert(t, var_names, assms, to_real):
    """Convert term t to Z3 input."""
    def rec(t):
        if t.is_var():
            z3_t = convert_const(t.name, t.T)
            if t.T == nat.natT and t.name not in assms:
                assms[t.name] = z3_t >= 0
            return z3_t
        elif t.is_all():
            nm = name.get_variant_name(t.arg.var_name, var_names)
            var_names.append(nm)
            v = Var(nm, t.arg.var_T)
            z3_v = convert_const(nm, t.arg.var_T)
            return z3.ForAll(z3_v, rec(t.arg.subst_bound(v)))
        elif logic.is_exists(t):
            nm = name.get_variant_name(t.arg.var_name, var_names)
            var_names.append(nm)
            v = Var(nm, t.arg.var_T)
            z3_v = convert_const(nm, t.arg.var_T)
            return z3.Exists(z3_v, rec(t.arg.subst_bound(v)))
        elif int.is_binary_int(t):
            return int.from_binary_int(t)
        elif t.is_implies():
            return z3.Implies(rec(t.arg1), rec(t.arg))
        elif t.is_equals():
            return rec(t.arg1) == rec(t.arg)
        elif t.is_conj():
            return z3.And(rec(t.arg1), rec(t.arg))
        elif t.is_disj():
            return z3.Or(rec(t.arg1), rec(t.arg))
        elif logic.is_if(t):
            b, t1, t2 = t.args
            return z3.If(rec(b), rec(t1), rec(t2))
        elif t.is_not():
            return z3.Not(rec(t.arg))
        elif t.head.is_const_name('plus'):
            return rec(t.arg1) + rec(t.arg)
        elif t.head.is_const_name('minus'):
            m, n = rec(t.arg1), rec(t.arg)
            if t.arg1.get_type() == nat.natT:
                return z3.If(m >= n, m - n, 0)
            return m - n
        elif t.head.is_const_name('uminus'):
            return -rec(t.arg)
        elif t.head.is_const_name('times'):
            return rec(t.arg1) * rec(t.arg)
        elif t.head.is_const_name('less_eq'):
            return rec(t.arg1) <= rec(t.arg)
        elif t.head.is_const_name('less'):
            return rec(t.arg1) < rec(t.arg)
        elif t.head.is_const_name('greater_eq'):
            return rec(t.arg1) >= rec(t.arg)
        elif t.head.is_const_name('greater'):
            return rec(t.arg1) > rec(t.arg)
        elif t.head.is_const_name('real_divide'):
            return rec(t.arg1) / rec(t.arg)
        elif t.head.is_const_name('zero'):
            return 0
        elif t.head.is_const_name('one'):
            return 1
        elif t.is_comb() and t.head.is_const_name('of_nat'):
            if nat.is_binary(t.arg):
                return nat.from_binary(t.arg)
            elif t.get_type() == realT:
                if t.arg.is_var():
                    if t.arg.name not in to_real:
                        nm = name.get_variant_name("r" + t.arg.name, var_names)
                        var_names.append(nm)
                        to_real[t.arg.name] = nm
                        z3_t = convert_const(nm, realT)
                        assms[nm] = z3_t >= 0
                        return z3_t
                    else:
                        return convert_const(to_real[t.arg.name], realT)
                return z3.ToReal(rec(t.arg))
            else:
                raise Z3Exception("convert: unsupported of_nat " + repr(t))
        elif t.head.is_const_name('max'):
            a, b = rec(t.arg1), rec(t.arg)
            return z3.If(a >= b, a, b)
        elif t.head.is_const_name('min'):
            a, b = rec(t.arg1), rec(t.arg)
            return z3.If(a <= b, a, b)
        elif t.head.is_const_name('abs'):
            a = rec(t.arg)
            return z3.If(a >= 0, a, -a)
        elif t.head.is_const_name('member'):
            a, S = rec(t.arg1), rec(t.arg)
            return S(a)
        elif t.is_comb():
            return rec(t.fun)(rec(t.arg))
        elif t.is_const():
            if t == true:
                return z3.BoolVal(True)
            elif t == false:
                return z3.BoolVal(False)
            else:
                raise Z3Exception("convert: unsupported constant " + repr(t))
        else:
            raise Z3Exception("convert: unsupported operation " + repr(t))

    return rec(t)


norm_thms = [
    'member_empty_simp',
    'member_insert',
    'member_univ_simp',
    'member_collect',
    'member_union_iff',
    'member_inter_iff',
    'set_equal_iff',
    'subset_def',
    'diff_def',
    ('real_zero_def', True),
    ('real_one_def', True),
    ('real_of_nat_add', True),
    ('real_of_nat_mul', True),
    'real_of_nat_minus',
    'real_inverse_divide',
    'real_open_interval_def',
    'real_closed_interval_def',
]

def norm_term(t):
    # Collect list of theorems that can be used.
    cvs = []
    for th_name in norm_thms:
        if isinstance(th_name, str) and theory.thy.has_theorem(th_name):
            cvs.append(conv.try_conv(conv.rewr_conv(th_name)))
        elif theory.thy.has_theorem(th_name[0]):
            cvs.append(conv.try_conv(conv.rewr_conv(th_name[0], sym=True)))
    cvs.append(conv.try_conv(conv.beta_conv()))
    cv = conv.top_conv(conv.every_conv(*cvs))
    while True:
        rhs = cv.eval(t).rhs
        if rhs == t:
            break
        else:
            t = rhs
    return fologic.simplify(t)

def solve(t, debug=False):
    """Solve the given goal using Z3."""
    s = z3.Solver()
    s.set('timeout', 5000)

    # First strip foralls from t.
    t = norm_term(t)
    new_names = logic.get_forall_names(t, svar=False)
    _, As, C = logic.strip_all_implies(t, new_names, svar=False)

    def print_debug(*args):
        if debug:
            print(*args)

    var_names = [v.name for v in term.get_vars(As + [C])]
    assms = dict()
    to_real = dict()
    for A in As:
        try:
            z3_A = convert(A, var_names, assms, to_real)
            print_debug('A', z3_A)
            s.add(z3_A)
        except Z3Exception as e:
            print_debug(e)
    try:
        z3_C = convert(C, var_names, assms, to_real)
        print_debug('C', z3_C)
        s.add(z3.Not(z3_C))
    except Z3Exception as e:
        print_debug(e)

    for nm, A in assms.items():
        print_debug('A', A)
        s.add(A)
    return str(s.check()) == 'unsat'

class Z3Macro(ProofMacro):
    """Macro invoking SMT solver Z3."""
    def __init__(self):
        self.level = 0  # No expand implemented for Z3.
        self.sig = Term
        self.limit = None

    def eval(self, args, prevs):
        if z3_loaded:
            assms = [prev.prop for prev in prevs]
            assert solve(Implies(*(assms + [args]))), "Z3: not solved."
        else:
            print("Warning: Z3 is not installed")

        return Thm(sum([th.hyps for th in prevs], ()), args)

    def expand(self, prefix, args, prevs):
        raise NotImplementedError

def apply_z3(t):
    return ProofTermDeriv('z3', args=t)


class Z3Method(Method):
    """Method invoking SMT solver Z3."""
    def __init__(self):
        self.sig = []
        self.limit = None
        self.no_order = True

    def search(self, state, id, prevs, data=None):
        if data:
            return [data]

        return [{}]

    @settings.with_settings
    def display_step(self, state, data):
        return pprint.N("Apply Z3")

    def apply(self, state, id, data, prevs):
        assert z3_loaded, "Z3 method: not installed"
        prev_ths = [state.get_proof_item(prev).th for prev in prevs]
        assms = [prev.prop for prev in prev_ths]

        cur_item = state.get_proof_item(id)
        assert cur_item.rule == "sorry", "introduction: id is not a gap"
        goal = cur_item.th.prop

        assert solve(Implies(*(assms + [goal]))), "Z3 method: not solved"
        state.set_line(id, 'z3', args=goal, prevs=prevs)


global_macros.update({
    "z3": Z3Macro(),
})

global_methods.update({
    "z3": Z3Method(),
})
