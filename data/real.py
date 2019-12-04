# Author: Bohua Zhan

from fractions import Fraction

from kernel.type import Type, TFun, boolT
from kernel.term import Term, Const
from kernel.thm import Thm
from kernel.theory import Method, global_methods
from kernel import macro
from data import nat
from data.set import setT
from logic.conv import Conv
from logic.proofterm import refl, ProofTermMacro, ProofTermDeriv
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
divides = Const("real_divide", TFun(realT, realT, realT))
less_eq = Const("less_eq", TFun(realT, realT, boolT))
less = Const("less", TFun(realT, realT, boolT))
nat_power = Const("power", TFun(realT, nat.natT, realT))

# Transcendental functions

exp = Const("exp", TFun(realT, realT))
sin = Const("sin", TFun(realT, realT))
cos = Const("cos", TFun(realT, realT))

# Intervals

closed_interval = Const("real_closed_interval", TFun(realT, realT, setT(realT)))
open_interval = Const("real_open_interval", TFun(realT, realT, setT(realT)))


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

def is_divides(t):
    return t.is_binop() and t.head == divides

def is_nat_power(t):
    return t.is_binop() and t.head == nat_power

def is_less_eq(t):
    return t.is_binop() and t.head == less_eq

def is_less(t):
    return t.is_binop() and t.head == less

def to_binary_real(n):
    if n < 0:
        return uminus(to_binary_real(-n))

    if isinstance(n, Fraction):
        return divides(to_binary_real(n.numerator), to_binary_real(n.denominator))
        
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
    elif t.is_comb() and t.fun.is_const_name('of_nat'):
        return nat.convert_to_poly(t.arg)
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
    elif is_divides(t):
        num, denom = t.args
        p_denom = convert_to_poly(denom)
        if p_denom.is_nonzero_constant():
            return convert_to_poly(num).scale(Fraction(1, p_denom.get_constant()))
        else:
            return poly.singleton(t)
    elif is_nat_power(t):
        power = nat.convert_to_poly(t.arg)
        if power.is_constant():
            return convert_to_poly(t.arg1) ** power.get_constant()
        else:
            return poly.singleton(t)
    else:
        return poly.singleton(t)

def from_mono(m):
    """Convert a monomial to a term."""
    assert isinstance(m, poly.Monomial), "from_mono: input is not a monomial"
    factors = []
    for base, power in m.factors:
        assert isinstance(base, Term), "from_mono: base is not a Term"
        baseT = base.get_type()
        if baseT != realT:
            base = Const('of_nat', TFun(baseT, realT))(base)
        if power == 1:
            factors.append(base)
        else:
            factors.append(nat_power(base, nat.to_binary_nat(power)))
    if m.coeff != 1:
        factors = [to_binary_real(m.coeff)] + factors
    return mk_times(*factors)

def from_poly(p):
    """Convert a polynomial to a term t."""
    return mk_plus(*(from_mono(m) for m in p.monomials))


class real_ineq_macro(ProofTermMacro):
    """Attempt to prove a <= b, where a and b are real constants."""
    def __init__(self):
        self.level = 0  # proof term not implemented
        self.sig = Term
        self.limit = 'real_neg_0'

    def eval(self, thy, goal, pts):
        assert len(pts) == 0, "real_ineq_macro"
        assert self.can_eval(thy, goal), "real_ineq_macro"

        return Thm([], goal)

    def can_eval(self, thy, goal):
        assert isinstance(goal, Term), "real_ineq_macro"
        if not (is_less_eq(goal) or is_less(goal)) and goal.arg.get_type() == realT:
            return False

        t1, t2 = goal.args
        if not (is_binary_real(t1) and is_binary_real(t2)):
            return False

        r1 = from_binary_real(t1)
        r2 = from_binary_real(t2)
        if is_less_eq(goal):
            return r1 <= r2
        elif is_less(goal):
            return r1 < r2
        else:
            raise NotImplementedError

    def get_proof_term(self, thy, goal, pts):
        raise NotImplementedError

def real_less_eq(thy, t1, t2):
    assert is_binary_real(t1) and is_binary_real(t2) and from_binary_real(t1) <= from_binary_real(t2), \
        "real_less_eq"

    return ProofTermDeriv("real_ineq", thy, less_eq(t1, t2))

def real_less(thy, t1, t2):
    assert is_binary_real(t1) and is_binary_real(t2) and from_binary_real(t1) < from_binary_real(t2), \
        "real_less_eq"

    return ProofTermDeriv("real_less", thy, less(t1, t2))


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


class real_norm_conv(Conv):
    """Conversion for real_norm."""
    def get_proof_term(self, thy, t):
        t2 = from_poly(convert_to_poly(t))
        if t2 == t:
            return refl(t)
        else:
            return ProofTermDeriv('real_norm', thy, Term.mk_equals(t, t2))


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
    "real_ineq": real_ineq_macro(),
    "real_norm": real_norm_macro()
})

global_methods.update({
    "real_norm": real_norm_method()
})
