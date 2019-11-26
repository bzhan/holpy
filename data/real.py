# Author: Bohua Zhan

from kernel.type import Type, TFun, boolT
from kernel.term import Term, Const
from kernel.thm import Thm
from kernel.theory import Method, global_methods
from kernel import macro
from data import nat
from logic.proofterm import ProofTermMacro
from syntax import pprint, settings
from server.tactic import MacroTactic
from util import poly


# Basic definitions

realT = Type("real")
zero = Const("zero", realT)
one = Const("one", realT)
of_nat = Const("of_nat", TFun(nat.natT, realT))
plus = Const("plus", TFun(realT, realT, realT))
minus = Const("minus", TFun(realT, realT, realT))
uminus = Const("uminus", TFun(realT, realT))
times = Const("times", TFun(realT, realT, realT))
less_eq = Const("less_eq", TFun(realT, realT, boolT))
less = Const("less", TFun(realT, realT, boolT))
nat_power = Const("power", TFun(realT, nat.natT, realT))

# Transcendental functions

exp = Const("exp", TFun(realT, realT))
sin = Const("sin", TFun(realT, realT))
cos = Const("cos", TFun(realT, realT))


def mk_plus(*args):
    if not args:
        return zero
    elif len(args) == 1:
        return args[0]
    else:
        return plus(mk_plus(*args[:-1]), args[-1])

def mk_times(*args):
    if not args:
        return one
    elif len(args) == 1:
        return args[0]
    else:
        return times(mk_times(*args[:-1]), args[-1])

def is_real(t):
    return t.get_type() == realT

def is_plus(t):
    return t.is_binop() and t.head == plus

def is_minus(t):
    return t.is_binop() and t.head == minus

def is_uminus(t):
    return t.is_comb() and t.fun == uminus

def is_times(t):
    return t.is_binop() and t.head == times

def is_nat_power(t):
    return t.is_binop() and t.head == nat_power

def is_less_eq(t):
    return t.is_binop() and t.head == less_eq

def is_less(t):
    return t.is_binop() and t.head == less

def to_binary_real(n):
    if n == 0:
        return zero
    elif n == 1:
        return one
    else:
        return of_nat(nat.to_binary(n))

def is_binary_real(t):
    if t.is_comb() and t.fun.is_const_name("uminus"):
        return is_binary_real(t.arg)
    else:
        return t == zero or t == one or \
               (t.is_comb() and t.fun.is_const_name("of_nat") and
                nat.is_binary(t.arg) and nat.from_binary(t.arg) >= 2)

def from_binary_real(t):
    assert is_binary_real(t), "from_binary_real"
    if t.is_comb() and t.fun.is_const_name("uminus"):
        return -from_binary_real(t.arg)
    if t == zero:
        return 0
    elif t == one:
        return 1
    else:
        return nat.from_binary(t.arg)

def convert_to_poly(t):
    """Convert a term t to polynomial normal form."""
    if t.is_var():
        return poly.singleton(t)
    elif is_binary_real(t):
        return poly.constant(from_binary_real(t))
    elif is_plus(t):
        t1, t2 = t.args
        return convert_to_poly(t1) + convert_to_poly(t2)
    elif is_minus(t):
        t1, t2 = t.args
        return convert_to_poly(t1) - convert_to_poly(t2)
    elif is_uminus(t):
        return -convert_to_poly(t.arg)
    elif is_times(t):
        t1, t2 = t.args
        return convert_to_poly(t1) * convert_to_poly(t2)
    else:
        return poly.singleton(t)

class real_norm_macro(ProofTermMacro):
    """Attempt to prove goal by normalization."""

    def __init__(self):
        self.level = 0  # proof term not implemented
        self.sig = Term
        self.limit = 'real_neg_0'

    def eval(self, thy, goal, pts):
        assert len(pts) == 0, "real_norm_macro"
        assert self.can_eval(thy, goal), "real_norm_macro"

        return Thm([], goal)

    def can_eval(self, thy, goal):
        assert isinstance(goal, Term), "real_norm_macro"
        if not (goal.is_equals() and goal.lhs.get_type() == realT):
            return False

        t1, t2 = goal.args
        return convert_to_poly(t1) == convert_to_poly(t2)

    def get_proof_term(self, thy, goal, pts):
        raise NotImplementedError


class real_norm_method(Method):
    """Apply real_norm macro."""
    def __init__(self):
        self.sig = []
        self.limit = 'real_neg_0'

    def search(self, state, id, prevs, data=None):
        if data:
            return [data]

        if len(prevs) != 0:
            return []

        cur_th = state.get_proof_item(id).th
        if real_norm_macro().can_eval(state.thy, cur_th.prop):
            return [{}]
        else:
            return []

    @settings.with_settings
    def display_step(self, state, data):
        return pprint.N("real_norm: (solves)")

    def apply(self, state, id, data, prevs):
        assert len(prevs) == 0, "real_norm_method"
        state.apply_tactic(id, MacroTactic('real_norm'))


macro.global_macros.update({
    "real_norm": real_norm_macro()
})

global_methods.update({
    "real_norm": real_norm_method()
})
