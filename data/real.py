# Author: Bohua Zhan

from fractions import Fraction
import math
import sympy
from sympy.ntheory.factor_ import factorint
import typing

from kernel.type import TFun, BoolType, RealType
from kernel import term
from kernel.term import Term, Const, Eq, Nat, Real, Sum, Prod, true, false, Var, Exists, And, Implies, Not, false
from kernel.thm import Thm
from kernel.theory import register_macro
from kernel.macro import Macro
from kernel.proofterm import TacticException
from kernel import term_ord
from data import nat, integer, proplogic
from data.set import setT
from logic import logic
from logic import auto
from logic import matcher
from logic.conv import rewr_conv, binop_conv, arg1_conv, arg_conv, try_conv, Conv, ConvException, top_conv
from logic.tactic import MacroTactic
from kernel.proofterm import refl, ProofTerm
from syntax import pprint, settings
from server.method import Method, register_method
from util import poly
import functools

# Basic definitions

zero = Const('zero', RealType)
one = Const('one', RealType)
plus = term.plus(RealType)
minus = term.minus(RealType)
uminus = term.uminus(RealType)
times = term.times(RealType)
divides = term.divides(RealType)
nat_power = term.nat_power(RealType)
real_power = term.real_power(RealType)
of_nat = term.of_nat(RealType)
equals = term.equals(RealType)
less_eq = term.less_eq(RealType)
less = term.less(RealType)
greater_eq = term.greater_eq(RealType)
greater = term.greater(RealType)

inverse = Const("real_inverse", TFun(RealType, RealType))
sqrt = Const("sqrt", TFun(RealType, RealType))
pi = Const("pi", RealType)

# Transcendental functions

log = Const("log", TFun(RealType, RealType))
exp = Const("exp", TFun(RealType, RealType))
sin = Const("sin", TFun(RealType, RealType))
cos = Const("cos", TFun(RealType, RealType))
tan = Const("tan", TFun(RealType, RealType))
cot = Const("cot", TFun(RealType, RealType))
sec = Const("sec", TFun(RealType, RealType))
csc = Const("csc", TFun(RealType, RealType))
hol_abs = Const("abs", TFun(RealType, RealType))
atn = Const("atn", TFun(RealType, RealType))

# Intervals

closed_interval = Const("real_closed_interval", TFun(RealType, RealType, setT(RealType)))
open_interval = Const("real_open_interval", TFun(RealType, RealType, setT(RealType)))
lopen_interval = Const("real_lopen_interval", TFun(RealType, RealType, setT(RealType)))
ropen_interval = Const("real_ropen_interval", TFun(RealType, RealType, setT(RealType)))

def real_eval(t):
    """Evaluate t as a constant. Return an integer or rational number.

    Assume t does not contain non-rational constants.

    """
    def rec(t):
        if t.is_number():
            return t.dest_number()
        elif t.is_comb('of_nat', 1):
            return nat.nat_eval(t.arg)
        elif t.is_comb('of_int', 1):
            return integer.int_eval(t.arg)
        elif t.is_plus():
            return rec(t.arg1) + rec(t.arg)
        elif t.is_minus():
            return rec(t.arg1) - rec(t.arg)
        elif t.is_uminus():
            return -rec(t.arg)
        elif t.is_times():
            return rec(t.arg1) * rec(t.arg)
        elif t.is_divides():
            denom = rec(t.arg)
            if denom == 0:
                raise ConvException('real_eval: divide by zero')
            elif denom == 1:
                return rec(t.arg1)
            else:
                return Fraction(rec(t.arg1)) / denom
        elif t.is_real_inverse():
            denom = rec(t.arg)
            if denom == 0:
                raise ConvException('real_eval: divide by zero')
            else:
                return Fraction(1) / denom
        elif t.is_nat_power():
            return rec(t.arg1) ** nat.nat_eval(t.arg)
        elif t.is_real_power():
            x, p = rec(t.arg1), rec(t.arg)
            if p == 0:
                return 1
            elif x == 0:
                return 0
            elif x == 1:
                return 1
            elif isinstance(p, int):
                if p >= 0:
                    return rec(t.arg1) ** p
                else:
                    return Fraction(1) / (rec(t.arg1) ** (-p))
            else:
                raise ConvException('real_eval: %s' % str(t))
        else:
            raise ConvException('real_eval: %s' % str(t))
    
    res = rec(t)
    if isinstance(res, Fraction) and res.denominator == 1:
        return res.numerator
    else:
        return res

def real_approx_eval(t):
    """Evaluate t to a Python numeral (int or float) value.

    This is an imprecise (but more general) version of real_eval.

    """
    def rec(t):
        if t.is_number():
            return t.dest_number()
        elif t.is_comb('of_nat', 1):
            return nat.nat_eval(t.arg)
        elif t.is_comb('of_int', 1):
            return integer.int_eval(t.arg)
        elif t.is_plus():
            return rec(t.arg1) + rec(t.arg)
        elif t.is_minus():
            return rec(t.arg1) - rec(t.arg)
        elif t.is_uminus():
            return -rec(t.arg)
        elif t.is_times():
            return rec(t.arg1) * rec(t.arg)
        elif t.is_divides():
            denom = rec(t.arg)
            if denom == 0:
                raise ConvException('real_approx_eval: divide by zero')
            else:
                return rec(t.arg1) / denom
        elif t.is_real_inverse():
            denom = rec(t.arg)
            if denom == 0:
                raise ConvException('real_approx_eval: divide by zero')
            else:
                return 1 / denom
        elif t.is_nat_power():
            return rec(t.arg1) ** nat.nat_eval(t.arg)
        elif t.is_real_power():
            x, p = rec(t.arg1), rec(t.arg)
            return x ** p
        elif t.is_comb() and t.head == sqrt:
            return math.sqrt(rec(t.arg))
        elif t == pi:
            return math.pi
        elif t.is_comb() and t.head == sin:
            return math.sin(rec(t.arg))
        elif t.is_comb() and t.head == cos:
            return math.cos(rec(t.arg))
        elif t.is_comb() and t.head == tan:
            return math.tan(rec(t.arg))
        elif t.is_comb() and t.head == cot:
            return math.cot(rec(t.arg))
        elif t.is_comb() and t.head == sec:
            return math.sec(rec(t.arg))
        elif t.is_comb() and t.head == csc:
            return math.csc(rec(t.arg))
        elif t.is_comb() and t.head == atn:
            return math.atan(rec(t.arg))
        elif t.is_comb() and t.head == log:
            return math.log(rec(t.arg))
        elif t.is_comb() and t.head == exp:
            return math.exp(rec(t.arg))
        elif t.is_comb() and t.head == hol_abs:
            return abs(rec(t.arg))
        else:
            raise NotImplementedError

    return rec(t)

@register_macro('real_eval')
class real_eval_macro(Macro):
    """Simplify all arithmetic operations."""
    def __init__(self):
        self.level = 0  # No expand implemented
        self.sig = Term
        self.limit = None

    def eval(self, goal, prevs):
        assert len(prevs) == 0, "real_eval_macro: no conditions expected"
        assert goal.is_equals(), "real_eval_macro: goal must be an equality"
        assert real_eval(goal.lhs) == real_eval(goal.rhs), "real_eval_macro: two sides are not equal"

        return Thm(goal)

class real_eval_conv(Conv):
    """Simplify all arithmetic operations."""
    def get_proof_term(self, t):
        if t.get_type() != RealType:
            return refl(t)
        simp_t = Real(real_eval(t))
        if simp_t == t:
            return refl(t)
        return ProofTerm('real_eval', Eq(t, simp_t))


"""Normalization of polynomials.

Each monomial is in the form x, c * x, or c, where c is a numerical
constant (may be rational) and x is a product of atoms.

Each atom is of the form x ^ n (nat_power), x ^ r (real_power), or
simply x (no powers). Powers are combined (e.g. x ^ m * x ^ n = x ^ (m + n))
but not automatically expanded.

"""

def dest_monomial(t):
    """Remove the coefficient part of a monomial t."""
    if t.is_times() and t.arg1.is_number():
        return t.arg
    elif t.is_number():
        return one
    else:
        return t

class to_coeff_form(Conv):
    """Convert c to c * 1, x to 1 * x, and leave c * x unchanged."""
    def get_proof_term(self, t):
        pt = refl(t)
        if t.is_times() and t.arg1.is_number():
            return pt
        elif t.is_number():  # c to c * 1
            return pt.on_rhs(rewr_conv('real_mul_rid', sym=True))
        else:  # x to 1 * x
            return pt.on_rhs(rewr_conv('real_mul_lid', sym=True))

class from_coeff_form(Conv):
    """Convert c * 1 to c, 1 * x to x, and leave c * x unchanged."""
    def get_proof_term(self, t):
        pt = refl(t)
        if t.arg.is_one():
            return pt.on_rhs(rewr_conv('real_mul_rid'))
        elif t.arg1.is_one():
            return pt.on_rhs(rewr_conv('real_mul_lid'))
        elif t.arg.is_zero():
            return pt.on_rhs(rewr_conv('real_mul_rzero'))
        elif t.arg1.is_zero():
            return pt.on_rhs(rewr_conv('real_mul_lzero'))
        else:
            return pt

class combine_monomial(Conv):
    """Combine (add) two monomials with the same body."""
    def get_proof_term(self, t):
        return refl(t).on_rhs(
            binop_conv(to_coeff_form()),
            rewr_conv('real_add_rdistrib', sym=True),
            arg1_conv(real_eval_conv()),
            from_coeff_form())

class swap_add_r(Conv):
    """Rewrite (a + b) + c to (a + c) + b."""
    def get_proof_term(self, t):
        pt = refl(t)
        return pt.on_rhs(
            rewr_conv('real_add_assoc', sym=True),
            arg_conv(rewr_conv('real_add_comm')),
            rewr_conv('real_add_assoc'))

def atom_less(t1, t2):
    """Compare two atoms, put constants in front."""
    if not t1.has_var() and t2.has_var():
        return True
    elif not t2.has_var() and t1.has_var():
        return False
    else:
        return term_ord.fast_compare(t1, t2) < 0

class norm_add_monomial(Conv):
    """Normalize expression of the form (a_1 + ... + a_n) + b."""
    def get_proof_term(self, t):
        pt = refl(t)
        if t.arg1.is_zero():
            return pt.on_rhs(rewr_conv("real_add_lid"))
        elif t.arg.is_zero():
            return pt.on_rhs(rewr_conv("real_add_rid"))
        elif t.arg1.is_plus():
            # Left side has more than one term. Compare last term with a
            m1, m2 = dest_monomial(t.arg1.arg), dest_monomial(t.arg)
            if m1 == m2:
                pt = pt.on_rhs(rewr_conv('real_add_assoc', sym=True),
                               arg_conv(combine_monomial()))
                if pt.rhs.arg.is_zero():
                    pt = pt.on_rhs(rewr_conv('real_add_rid'))
                return pt
            elif atom_less(m1, m2):
                return pt
            else:
                pt = pt.on_rhs(swap_add_r(), arg1_conv(self))
                if pt.rhs.arg1.is_zero():
                    pt = pt.on_rhs(rewr_conv('real_add_lid'))
                return pt
        else:
            # Left side is an atom. Compare two sides
            m1, m2 = dest_monomial(t.arg1), dest_monomial(t.arg)
            if m1 == m2:
                return pt.on_rhs(combine_monomial())
            elif atom_less(m1, m2):
                return pt
            else:
                return pt.on_rhs(rewr_conv('real_add_comm'))

class norm_add_polynomial(Conv):
    """Normalize expression of the form (a_1 + ... + a_n) + (b_1 + ... + b_m)."""
    def get_proof_term(self, t):
        pt = refl(t)
        if t.arg.is_plus():
            return pt.on_rhs(rewr_conv('real_add_assoc'), arg1_conv(self), norm_add_monomial())
        else:
            return pt.on_rhs(norm_add_monomial())

auto.add_global_autos_norm(plus, norm_add_polynomial())


def dest_atom(t):
    """Remove power part of an atom t."""
    if t.is_comb('exp', 1):
        return exp(one)
    elif t.is_nat_power() and t.arg.is_number():
        return t.arg1
    elif t.is_real_power() and t.arg.is_number():
        return t.arg1
    else:
        return t

class to_exponent_form(Conv):
    """Convert x to x ^ 1, and leave x ^ n or x ^ r unchanged."""
    def get_proof_term(self, t):
        pt = refl(t)
        if t.is_comb('exp', 1):
            return pt
        elif t.is_nat_power() and t.arg.is_number():
            return pt
        elif t.is_real_power() and t.arg.is_number():
            return pt
        else:
            return pt.on_rhs(rewr_conv('real_pow_1', sym=True))

class from_exponent_form(Conv):
    """Convert x ^ 1 to x, and leave x ^ n or x ^ r unchanged."""
    def get_proof_term(self, t):
        pt = refl(t)
        if t.is_comb('exp', 1):
            return pt
        elif t.is_nat_power() and t.arg.is_one():
            return pt.on_rhs(rewr_conv('real_pow_1'))
        elif t.is_real_power() and t.arg.is_one():
            return pt.on_rhs(rewr_conv('rpow_1'))
        elif t.is_real_power() and t.arg.is_zero():
            return pt.on_rhs(rewr_conv('rpow_0'))
        else:
            return pt

class combine_atom(Conv):
    """Combine (multiply) two atoms with the same body.
    
    This may require conditions on the body, as the combination
    (x ^ p) * (x ^ q) = x ^ (p + q), where p and q are rational
    numbers, requires assuming x >= 0. No condition is required
    for (x ^ m) * (x ^ n) = x ^ (m + n), where m and n are
    natural numbers.

    """
    def __init__(self, conds):
        self.conds = conds

    def get_proof_term(self, t):
        pt = refl(t).on_rhs(binop_conv(to_exponent_form()))
        if pt.rhs.arg1.is_comb('exp', 1) and pt.rhs.arg.is_comb('exp', 1):
            # Both sides are exponentials
            return pt.on_rhs(rewr_conv('real_exp_add', sym=True),
                             arg_conv(auto.auto_conv(self.conds)))
        elif pt.rhs.arg1.is_nat_power() and pt.rhs.arg.is_nat_power():
            # Both sides are natural number powers, simply add
            return pt.on_rhs(rewr_conv('real_pow_add', sym=True),
                             arg_conv(nat.nat_conv()))
        else:
            # First check that x > 0 can be proved. If not, just return
            # without change.
            x = pt.rhs.arg1.arg1
            try:
                x_gt_0 = auto.solve(x > 0, self.conds)
            except TacticException:
                return refl(t)

            # Convert both sides to real powers
            if pt.rhs.arg1.is_nat_power():
                pt = pt.on_rhs(arg1_conv(rewr_conv('rpow_pow', sym=True)))
            if pt.rhs.arg.is_nat_power():
                pt = pt.on_rhs(arg_conv(rewr_conv('rpow_pow', sym=True)))
            pt = pt.on_rhs(rewr_conv('rpow_add', sym=True, conds=[x_gt_0]),
                           arg_conv(real_eval_conv()))

            # Simplify back to nat if possible
            if pt.rhs.arg.is_comb('of_nat', 1):
                pt = pt.on_rhs(rewr_conv('rpow_pow'),
                               arg_conv(rewr_conv('nat_of_nat_def', sym=True)))

            return pt.on_rhs(from_exponent_form())

class swap_mult_r(Conv):
    """Rewrite (a * b) * c to (a * c) * b."""
    def get_proof_term(self, t):
        pt = refl(t)
        return pt.on_rhs(
            rewr_conv('real_mult_assoc', sym=True),
            arg_conv(rewr_conv('real_mult_comm')),
            rewr_conv('real_mult_assoc'))

class norm_mult_atom(Conv):
    """Normalize expression of the form (a_1 * ... * a_n) * b.
    
    It is possible for a_i or b to be 1 (signifying empty atom) but not
    any other constant number.
    
    """
    def __init__(self, conds):
        self.conds = conds

    def get_proof_term(self, t):
        pt = refl(t)
        if t.arg1.is_one():
            return pt.on_rhs(rewr_conv('real_mul_lid'))
        elif t.arg.is_one():
            return pt.on_rhs(rewr_conv('real_mul_rid'))
        elif t.arg1.is_times():
            # Left side has more than one atom. Compare last atom with b
            m1, m2 = dest_atom(t.arg1.arg), dest_atom(t.arg)
            if m1 == m2:
                pt = pt.on_rhs(rewr_conv('real_mult_assoc', sym=True),
                               arg_conv(combine_atom(self.conds)))
                if pt.rhs.arg.is_one():
                    pt = pt.on_rhs(rewr_conv('real_mul_rid'))
                return pt
            elif atom_less(m1, m2):
                return pt
            else:
                pt = pt.on_rhs(swap_mult_r(), arg1_conv(self))
                if pt.rhs.arg1.is_one():
                    pt = pt.on_rhs(rewr_conv('real_mul_lid'))
                return pt
        else:
            # Left side is an atom. Compare two sides
            m1, m2 = dest_atom(t.arg1), dest_atom(t.arg)
            if m1 == m2:
                return pt.on_rhs(combine_atom(self.conds))
            elif atom_less(m1, m2):
                return pt
            else:
                return pt.on_rhs(rewr_conv('real_mult_comm'))

class norm_mult_monomial(Conv):
    """Normalize expression of the form (a_1 * ... * a_n) * (b_1 * ... * b_m)."""
    def __init__(self, conds):
        self.conds = conds

    def get_proof_term(self, t):
        pt = refl(t)
        if t.arg.is_times():
            return pt.on_rhs(rewr_conv('real_mult_assoc'),
                             arg1_conv(self),
                             norm_mult_atom(self.conds))
        else:
            return pt.on_rhs(norm_mult_atom(self.conds))

class norm_mult_monomials(Conv):
    """Normalize (c_1 * m_1) * (c_2 * m_2), where c_1, c_2 are constants,
    and m_1, m_2 are monomials.

    """
    def __init__(self, conds):
        self.conds = conds

    def get_proof_term(self, t):
        pt = refl(t)
        is_l_atom = (dest_monomial(t.arg1) == t.arg1)
        is_r_atom = (dest_monomial(t.arg) == t.arg)
        if is_l_atom and is_r_atom:
            return pt.on_rhs(norm_mult_monomial(self.conds))
        elif is_l_atom and not is_r_atom:
            if t.arg.is_number():
                return pt.on_rhs(
                    rewr_conv('real_mult_comm'),
                    try_conv(rewr_conv('real_mul_rid')),
                    try_conv(rewr_conv('real_mul_lzero')))
            else:
                return pt.on_rhs(
                    arg_conv(rewr_conv('real_mult_comm')),
                    rewr_conv('real_mult_assoc'),
                    rewr_conv('real_mult_comm'),
                    arg_conv(norm_mult_monomial(self.conds)))
        elif not is_l_atom and is_r_atom:
            if t.arg1.is_number():
                return pt.on_rhs(
                    try_conv(rewr_conv('real_mul_rid')),
                    try_conv(rewr_conv('real_mul_lzero')))
            else:
                return pt.on_rhs(
                    rewr_conv('real_mult_assoc', sym=True),
                    arg_conv(norm_mult_monomial(self.conds)))
        else:
            return pt.on_rhs(
                binop_conv(to_coeff_form()),  # (c_1 * m_1) * (c_2 * m_2)
                rewr_conv('real_mult_assoc'),  # (c_1 * m_1 * c_2) * m_2
                arg1_conv(swap_mult_r()),  # (c_1 * c_2 * m_1) * m_2
                arg1_conv(arg1_conv(real_eval_conv())),  # (c_1c_2 * m_1) * m_2
                rewr_conv('real_mult_assoc', sym=True),  # c_1c_2 * (m_1 * m_2)
                arg_conv(norm_mult_monomial(self.conds)),
                from_coeff_form())

def norm_mult(t, pts):
    """Normalization of mult. Assume two sides are in normal form."""
    pt = refl(t)
    if t.arg1.is_plus():
        return pt.on_rhs(rewr_conv('real_add_rdistrib'))
    elif t.arg.is_plus():
        return pt.on_rhs(rewr_conv('real_add_ldistrib'))
    else:
        return pt.on_rhs(norm_mult_monomials(pts))

auto.add_global_autos_norm(times, norm_mult)

def norm_uminus(t, pts):
    """Normalization of uminus."""
    pt = refl(t)
    if t.is_number():
        return pt.on_rhs(real_eval_conv())
    else:
        return pt.on_rhs(rewr_conv('real_poly_neg1'))

auto.add_global_autos_norm(uminus, norm_uminus)

auto.add_global_autos_norm(minus, auto.norm_rules(['real_poly_neg2']))

def norm_divides(t, pts):
    """Normalization of divides."""
    pt = refl(t)
    if t.is_number():
        return pt.on_rhs(real_eval_conv())
    else:
        return pt.on_rhs(rewr_conv('real_divide_def'))

auto.add_global_autos_norm(divides, norm_divides)

auto.add_global_autos_norm(
    inverse,
    auto.norm_rules([
        'rpow_neg_one'
    ]))

auto.add_global_autos_norm(
    of_nat,
    auto.norm_rules([
        'real_of_nat_id',
        'real_of_nat_add',
        'real_of_nat_mul'
    ]))

auto.add_global_autos_norm(nat_power, real_eval_conv())

auto.add_global_autos_norm(
    nat_power,
    auto.norm_rules([
        'real_nat_power_def_1',
        'real_nat_power_def_2',
        'real_pow_1',
        'real_pow_one',
        'real_pow_mul',
        'real_pow_pow',
        'rpow_rpow_nat2',
        'real_exp_n_sym',
    ])
)

class real_nat_power_conv(Conv):
    def get_proof_term(self, t):
        """Unfold powers of 2 and 3, leave other powers unexpanded."""
        a, p = t.args

        # Exponent is 2, apply real_add_ldistrib to avoid folding back.
        if p.is_number() and p.dest_number() == 2 and a.is_plus():
            return refl(t).on_rhs(rewr_conv('real_pow_2'),
                                  rewr_conv('real_add_ldistrib'))
        # Exponent is 3
        elif p.is_number() and p.dest_number() == 3 and a.is_plus():
            return refl(t).on_rhs(rewr_conv('real_pow_3'),
                                  rewr_conv('real_add_ldistrib'))

        return refl(t)

auto.add_global_autos_norm(nat_power, real_nat_power_conv())

auto.add_global_autos_norm(real_power, real_eval_conv())

auto.add_global_autos_norm(
    real_power,
    auto.norm_rules([
        'rpow_0',
        'rpow_1',
        'rpow_rpow',
        'rpow_rpow_nat1',
        'rpow_mul',
        'rpow_base_divide',
        'rpow_exp',
        'rpow_abs',
    ])
)

class real_power_conv(Conv):
    def get_proof_term(self, t):
        a, p = t.args

        # Exponent is an integer: apply rpow_pow
        if p.is_number() and p.is_comb('of_nat', 1) and p.arg.is_binary():
            return refl(t).on_rhs(arg_conv(rewr_conv('real_of_nat_id', sym=True)),
                                  rewr_conv('rpow_pow'))

        if not (a.is_number() and p.is_number()):
            raise ConvException

        a, p = a.dest_number(), p.dest_number()
        if a <= 0:
            raise ConvException

        # Case 1: base is a composite number
        factors = factorint(a)
        keys = list(factors.keys())
        if len(keys) > 1 or (len(keys) == 1 and keys[0] != a):
            b1 = list(factors.keys())[0]
            b2 = a // b1
            eq_th = refl(Real(b1) * b2).on_rhs(real_eval_conv())
            pt = refl(t).on_rhs(arg1_conv(rewr_conv(eq_th, sym=True)))
            pt = pt.on_rhs(rewr_conv('rpow_mul'))
            return pt

        # Case 2: exponent is not between 0 and 1
        if isinstance(p, Fraction) and p.numerator // p.denominator != 0:
            div, mod = divmod(p.numerator, p.denominator)
            eq_th = refl(Real(div) + Real(mod) / p.denominator).on_rhs(real_eval_conv())
            pt = refl(t).on_rhs(arg_conv(rewr_conv(eq_th, sym=True)))
            a_gt_0 = auto.auto_solve(Real(a) > 0)
            pt = pt.on_rhs(rewr_conv('rpow_add', conds=[a_gt_0]))
            return pt

        return refl(t)

auto.add_global_autos_norm(real_power, real_power_conv())

auto.add_global_autos_norm(
    sqrt,
    auto.norm_rules([
        'rpow_sqrt'
    ]))

def convert_to_poly(t):
    """Convert a term t to polynomial normal form."""
    if t.is_var():
        return poly.singleton(t)
    elif t.is_number():
        return poly.constant(t.dest_number())
    elif t.is_comb('of_nat', 1):
        return nat.convert_to_poly(t.arg)
    elif t.is_plus():
        t1, t2 = t.args
        return convert_to_poly(t1) + convert_to_poly(t2)
    elif t.is_minus():
        t1, t2 = t.args
        return convert_to_poly(t1) - convert_to_poly(t2)
    elif t.is_uminus():
        return -convert_to_poly(t.arg)
    elif t.is_times():
        t1, t2 = t.args
        return convert_to_poly(t1) * convert_to_poly(t2)
    elif t.is_divides():
        num, denom = t.args
        p_denom = convert_to_poly(denom)
        if p_denom.is_nonzero_constant():
            return convert_to_poly(num).scale(Fraction(1, p_denom.get_constant()))
        else:
            return poly.singleton(t)
    elif t.is_nat_power():
        power = nat.convert_to_poly(t.arg)
        if power.is_constant():
            return convert_to_poly(t.arg1) ** power.get_constant()
        else:
            return poly.singleton(t)
    elif t.is_real_power():
        base = convert_to_poly(t.arg1)
        power = convert_to_poly(t.arg)
        if base.is_constant() and power.is_constant():
            return poly.constant(Fraction(base.get_constant()) ** Fraction(power.get_constant()))
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
        if baseT != RealType:
            base = Const('of_nat', TFun(baseT, RealType))(base)
        if power == 1:
            factors.append(base)
        else:
            factors.append(nat_power(base, Nat(power)))
    if m.coeff != 1:
        factors = [Real(m.coeff)] + factors
    return Prod(RealType, factors)

def from_poly(p):
    """Convert a polynomial to a term t."""
    return Sum(RealType, list(from_mono(m) for m in p.monomials))


@register_macro('real_norm')
class real_norm_macro(Macro):
    """Attempt to prove goal by normalization."""

    def __init__(self):
        self.level = 0  # proof term not implemented
        self.sig = Term
        self.limit = 'real_neg_0'

    def eval(self, goal, pts):
        assert len(pts) == 0, "real_norm_macro"
        assert self.can_eval(goal), "real_norm_macro"

        return Thm(goal)

    def can_eval(self, goal):
        assert isinstance(goal, Term), "real_norm_macro"
        if not (goal.is_equals() and goal.lhs.is_real()):
            return False

        t1, t2 = goal.args
        return convert_to_poly(t1) == convert_to_poly(t2)

    def get_proof_term(self, goal, pts):
        raise NotImplementedError


class real_norm_conv(Conv):
    """Conversion for real_norm."""
    def get_proof_term(self, t):
        t2 = from_poly(convert_to_poly(t))
        if t2 == t:
            return refl(t)
        else:
            return ProofTerm('real_norm', Eq(t, t2))


@register_method('real_norm')
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
        if real_norm_macro().can_eval(cur_th.prop):
            return [{}]
        else:
            return []

    def display_step(self, state, data):
        return pprint.N("real_norm: (solves)")

    def apply(self, state, id, data, prevs):
        assert len(prevs) == 0, "real_norm_method"
        state.apply_tactic(id, MacroTactic('real_norm'))

def is_real_ineq(tm):
    """Check if tm is an real inequality."""
    return (tm.is_less() or tm.is_less_eq() or tm.is_greater() or tm.is_greater_eq()) and tm.arg1.get_type() == RealType

class norm_real_ineq_conv(Conv):
    """
    Given an linear real arithmetic inequation, normalize it to canonical form.
    There are four possible input inequality forms:
    1) a < b <==> a - b < 0
    2) a > b <==> a - b > 0
    3) a ≤ b <==> a - b ≤ 0
    4) a ≥ b <==> a - b ≥ 0
    """
    def get_proof_term(self, tm):
        if not is_real_ineq(tm):
            raise ConvException("Invalid term: %s" % str(tm))

        pt = refl(tm)
        
        if tm.is_less():
            return pt.on_rhs(rewr_conv("real_le_sub"))

        elif tm.is_greater():
            return pt.on_rhs(rewr_conv("real_gt_sub"))
        
        elif tm.is_less_eq():
            return pt.on_rhs(rewr_conv("real_leq_sub"))
        
        elif tm.is_greater_eq():
            return pt.on_rhs(rewr_conv("real_geq_sub"))

class norm_neg_real_ineq_conv(Conv):
    """
    Give a negative linear real arithmetic inequation, normalize it to canonical form:
    There are four possible input inequality form:
    1) Not(a < b) <==> a ≥ b
    2) Not(a ≤ b) <==> a > b
    3) Not(a > b) <==> a ≤ b
    4) Not(a ≥ b) <==> a < b
    """
    def get_proof_term(self, tm):
        if not tm.is_not() or not is_real_ineq(tm.arg):
            raise ConvException("Invalid term: %s" % str(tm))
        pt = refl(tm)
        if tm.arg.is_less():
            return pt.on_rhs(rewr_conv("real_neg_lt"))
        elif tm.arg.is_greater():
            return pt.on_rhs(rewr_conv("real_not_gt"))            
        elif tm.arg.is_less_eq():
            return pt.on_rhs(rewr_conv("real_not_leq")) 
        else:
            return pt.on_rhs(rewr_conv("real_not_geq")) 


@register_macro('real_const_eq')
class RealEqMacro(Macro):
    """Give an real constant (in)equation, prove it (in)correctness."""
    def __init__(self):
        self.level = 0
        self.sig = Term
        self.limit = None

    def eval(self, goal, prevs=None):
        if len(goal.get_vars()) != 0:
            raise ConvException
        try:
            if goal.is_equals():
                if real_eval(goal.lhs) == real_eval(goal.rhs):
                    return Thm(Eq(goal, true))
                else:
                    return Thm(Eq(goal, false))
            else: # inequations
                lhs, rhs = real_eval(goal.arg1), real_eval(goal.arg)
                if goal.is_less():
                    return Thm(Eq(goal, true)) if lhs < rhs else Thm(Eq(goal, false))
                elif goal.is_less_eq():
                    return Thm(Eq(goal, true)) if lhs <= rhs else Thm(Eq(goal, false))
                elif goal.is_greater():
                    return Thm(Eq(goal, true)) if lhs > rhs else Thm(Eq(goal, false))
                elif goal.is_greater_eq():
                    return Thm(Eq(goal, true)) if lhs >= rhs else Thm(Eq(goal, false))
                else:
                    raise NotImplementedError
        except:
            raise ConvException

class real_const_eq_conv(Conv):
    def get_proof_term(self, t):
        return ProofTerm('real_const_eq', t)

class real_norm_comparison(Conv):
    """Given an real comparison(including equation and inequation), move all term to
    left-hand side, and guarantee the left-most term' coefficient is positive.
    """
    def get_proof_term(self, t):
        if not t.is_equals() and not t.is_compares() or t.arg1.get_type() != RealType:
            return refl(t)
        pt = refl(t)
        if t.is_equals():
            pt1 = pt.on_rhs(rewr_conv('real_sub_0', sym=True), auto.auto_conv())
        elif t.is_greater_eq():
            pt1 = pt.on_rhs(rewr_conv('real_geq_sub'), auto.auto_conv())
        elif t.is_greater():
            pt1 = pt.on_rhs(rewr_conv('real_gt_sub'), auto.auto_conv())
        elif t.is_less_eq():
            pt1 = pt.on_rhs(rewr_conv('real_leq_sub'), auto.auto_conv())
        elif t.is_less():
            pt1 = pt.on_rhs(rewr_conv('real_le_sub'), auto.auto_conv())
        else:
            raise ConvException(str(t))

        summands = integer.strip_plus(pt1.rhs.arg1)
        first = summands[0]
        if first.is_var():
            return pt1
        elif first.is_number() and real_eval(first) > 0:
            return pt1
        elif first.is_times() and real_eval(first.arg1) > 0:
            return pt1

        lhs = pt1.rhs
        if lhs.is_equals():
            return pt1.on_rhs(rewr_conv('real_eq_neg2', sym=True), auto.auto_conv())
        elif lhs.is_greater_eq():
            return pt1.on_rhs(rewr_conv('real_geq_leq'), auto.auto_conv())
        elif lhs.is_greater():
            return pt1.on_rhs(rewr_conv('real_gt_le'), auto.auto_conv())
        elif lhs.is_less_eq():
            return pt1.on_rhs(rewr_conv('real_leq_geq'), auto.auto_conv())
        elif lhs.is_less():
            return pt1.on_rhs(rewr_conv('real_le_gt'), auto.auto_conv())

class real_simplex_form(Conv):
    """Convert an inequality to simplex form: 
    c_1 * x_1 + ... + c_n * x_n ⋈ d 
    """
    def get_proof_term(self, t):
        if not is_real_ineq(t):
            return refl(t)

        pt_refl = refl(t).on_rhs(real_norm_comparison())
        left_expr = pt_refl.rhs.arg1
        summands = integer.strip_plus(left_expr)
        first = summands[0]

        if not left_expr.is_plus() or not first.is_constant():
            return pt_refl
        first_value = real_eval(first)
        if pt_refl.rhs.is_greater_eq():
            pt_th = ProofTerm.theorem("real_sub_both_sides_geq")
        elif pt_refl.rhs.is_greater():
            pt_th = ProofTerm.theorem("real_sub_both_sides_gt")
        elif pt_refl.rhs.is_less_eq():
            pt_th = ProofTerm.theorem("real_sub_both_sides_leq")
        elif pt_refl.rhs.is_less():
            pt_th = ProofTerm.theorem("real_sub_both_sides_le")
        else:
            raise NotImplementedError(str(t))

        inst = matcher.first_order_match(pt_th.lhs, pt_refl.rhs, inst=matcher.Inst(c=first))
        return pt_refl.transitive(pt_th.substitution(inst=inst)).on_rhs(auto.auto_conv())
class replace_conv(Conv):
    def __init__(self, pt):
        self.pt = pt

    def get_proof_term(self, t):
        if t == self.pt.prop.lhs:
            return self.pt
        else:
            raise ConvException

@register_macro('real_compare')
class RealCompareMacro(Macro):
    """
    Compare two real numbers.
    """
    def __init__(self):
        self.level = 0
        self.sig = Term
        self.limit = None

    def eval(self, goal, prevs=[]):
        assert goal.is_compares(), "real_compare_macro: Should be an inequality term"
        lhs, rhs = real_eval(goal.arg1), real_eval(goal.arg)
        if goal.is_less():
            assert lhs < rhs, "%f !< %f" % (lhs, rhs)
        elif goal.is_less_eq():
            assert lhs <= rhs, "%f !<= %f" % (lhs, rhs)
        elif goal.is_greater():
            assert lhs > rhs, "%f !> %f" % (lhs, rhs)
        elif goal.is_greater_eq():
            assert lhs >= rhs, "%f !>= %f" % (lhs, rhs)
        
        return Thm(goal)


@register_macro('real_const_ineq')
class real_const_ineq_macro(Macro):
    """Get an pure integer inequality"""
    def __init__(self):
        self.level = 0 # no expand implement
        self.sig = Term
        self.limit = None

    def eval(self, goal, prevs):
        assert len(prevs) == 0, "int_const_ineq: no conditions expected"

        if goal.is_not():
            goal = goal.arg

        assert (goal.is_compares() or goal.is_equals()) and goal.arg1.is_constant() and goal.arg.is_constant()\
            and goal.arg1.get_type() == RealType, repr(goal)
        lhs, rhs = real_eval(goal.arg1), real_eval(goal.arg)
        if goal.is_less():
            if lhs < rhs:
                return Thm(goal)
            else:
                return Thm(Not(goal))
        elif goal.is_less_eq():
            if lhs <= rhs:
                return Thm(goal)
            else:
                return Thm(Not(goal))
        elif goal.is_greater():
            if lhs > rhs:
                return Thm(goal)
            else:
                return Thm(Not(goal))
        elif goal.is_greater_eq():
            if lhs >= rhs:
                return Thm(goal)
            else:
                return Thm(Not(goal))
        elif goal.is_equals():
            if lhs == rhs:
                return Thm(goal)
            else:
                return Thm(Not(goal))
        else:
            raise NotImplementedError

class real_const_compares(Conv):
    """
    Given an int constant comparison, convert it to false or true.
    """
    def get_proof_term(self, tm):
        if not ((tm.is_compares() or tm.is_equals()) and \
            tm.arg1.is_constant() and tm.arg.is_constant()):
            return refl(tm)
        pt = ProofTerm("real_const_ineq", tm)
        if pt.prop.is_not():
            return pt.on_prop(rewr_conv("eq_false"))
        else:
            return pt.on_prop(rewr_conv("eq_true"))

@register_macro("real_eq_comparison")
class RealCompEq(Macro):
    """Given two real comparisons, prove their equality."""
    def __init__(self):
        self.level = 0
        self.sig = Term
        self.limit = None

    def get_proof_term(self, goal, prevs=[]):
        assert goal.is_equals() and goal.lhs.is_compares() and goal.rhs.is_compares()

        comp1, comp2 = goal.lhs, goal.rhs

        pt_refl1, pt_refl2 = refl(goal.lhs).on_rhs(real_norm_comparison()), \
                refl(goal.rhs).on_rhs(real_norm_comparison())

        assert pt_refl1.rhs == pt_refl2.rhs

        return pt_refl1.transitive(pt_refl2.symmetric())

@register_macro('non_strict_simplex')
class relax_strict_simplex_macro(Macro):
    """
    Given a set of strict inequalities, 
        x_1 > 0,
        x_2 > 0,
        ... 
        x_n > 0,

    return a proof term: x_1 > b_1, ... , x_n > b_n ⊢ ∃δ. δ > 0 ∧ x_1 >= δ ∧ ... ∧ x_n >= δ 
    """
    def __init__(self):
        self.level = 1
        self.sig = typing.List[Term]
        self.limit = None

    def handle_geq_stage1(self, pts):
        if not pts:
            return None, None, None

        # ⊢ min(min(...(min(x_1, x_2), x_3)...), x_n-1), x_n) > 0
        min_pos_pt = functools.reduce(lambda pt1, pt2: logic.apply_theorem("min_greater_0", pt1, pt2), 
                        pts[1:], pts[0])

         # ⊢ 0 < 2
        two_pos_pt = ProofTerm("real_compare", Real(0) < Real(2))

        # ⊢ min(...) / 2 > 0
        min_divides_two_pos = logic.apply_theorem("real_lt_div", 
                min_pos_pt.on_prop(rewr_conv("real_ge_to_le")), two_pos_pt).on_prop(rewr_conv("real_ge_to_le", sym=True))        

        # ⊢ 2 ≥ 1
        two_larger_one = ProofTerm("real_compare", Real(2) >= Real(1))

        # ⊢ min(...) ≥ min(...) / 2
        larger_half_pt = logic.apply_theorem("real_divides_larger_1", two_larger_one, min_pos_pt)
        
        # ⊢ min(...) / 2 = δ_1
        delta_1 = Var("δ_1", RealType)
        pt_delta1_eq = ProofTerm.assume(Eq(larger_half_pt.prop.arg, delta_1))
        
        # ⊢ min(...) ≥ δ_1
        larger_half_pt_delta = larger_half_pt.on_prop(top_conv(replace_conv(pt_delta1_eq)))

        # ⊢ δ_1 > 0
        delta_1_pos = min_divides_two_pos.on_prop(arg1_conv(replace_conv(pt_delta1_eq)))

        return larger_half_pt_delta, delta_1_pos, pt_delta1_eq

    def handle_geq_stage2(self, pt_lower_bound, pts, delta):
        # get ⊢ x_i ≥ δ, i = 1...n
        geq_pt = []
        pt_a = pt_lower_bound
        d = set()
        
        for i in range(len(pts)):
            if i != len(pts) - 1:
                pt = logic.apply_theorem("both_geq_min", pt_a)
                pt_1, pt_2 = logic.apply_theorem("conjD1", pt), logic.apply_theorem("conjD2", pt)
            else:
                pt_2 = pt_a

            ineq = pt_2.prop

            if ineq.arg1.is_minus() and ineq.arg1.arg.is_number():
                # move all constant term from left to right in pt_2's prop
                num = ineq.arg1.arg
                expr = greater_eq(ineq.arg1.arg1, num+delta)
                
            else:
                expr = greater_eq(ineq.arg1, Real(0)+delta)

            pt_eq_comp = ProofTerm("real_eq_comparison", Eq(ineq, expr))
            geq_pt.insert(0, pt_2.on_prop(replace_conv(pt_eq_comp)))

            if i != len(pts) - 1:
                pt_a = pt_1

        return geq_pt

    def handle_leq_stage1(self, pts):
        if not pts:
            return None, None, None
        # ⊢ max(max(...(max(x_1, x_2), x_3)...), x_n-1), x_n) < 0      
        max_pos_pt = functools.reduce(lambda pt1, pt2: logic.apply_theorem("max_less_0", pt1, pt2), 
                        pts[1:], pts[0])

        # ⊢ 0 < 2
        two_pos_pt = ProofTerm("real_compare", Real(2) > Real(0))

        # ⊢ max(...) / 2 < 0
        max_divides_two_pos = logic.apply_theorem("real_neg_div_pos", 
                max_pos_pt, two_pos_pt)

        # ⊢ 2 ≥ 1
        two_larger_one = ProofTerm("real_compare", Real(2) >= Real(1))

        # ⊢ max(...) ≤ max(...) / 2
        less_half_pt = logic.apply_theorem("real_neg_divides_larger_1", two_larger_one, max_pos_pt)

        # ⊢ max(...) / 2 = -δ
        delta_2 = Var("δ_2", RealType)
        pt_delta_eq = ProofTerm.assume(Eq(less_half_pt.prop.arg, -delta_2))

        # ⊢ δ > 0
        delta_pos_pt = max_divides_two_pos.on_prop(rewr_conv("real_le_gt"), top_conv(replace_conv(pt_delta_eq)), auto.auto_conv())
        
        # max(...) ≤ -δ
        less_half_pt_delta = less_half_pt.on_prop(arg_conv(replace_conv(pt_delta_eq)))

        return less_half_pt_delta, delta_pos_pt, pt_delta_eq
        

    def handle_leq_stage2(self, pt_upper_bound, pts, delta):
        # get ⊢ x_i ≤ -δ, for i = 1...n
        leq_pt = []
        pt_b = pt_upper_bound

        for i in range(len(pts)):
            if i != len(pts) - 1:
                pt = logic.apply_theorem("both_leq_max", pt_b)
                pt_1, pt_2 = logic.apply_theorem("conjD1", pt), logic.apply_theorem("conjD2", pt)
            else:
                pt_2 = pt_b

            ineq = pt_2.prop

            if ineq.arg1.is_minus() and ineq.arg1.arg.is_number():
                num = ineq.arg1.arg
                expr = less_eq(ineq.arg1.arg1, num-delta)
                
            else:
                expr = less_eq(ineq.arg1, Real(0)-delta)

            pt_eq_comp = ProofTerm("real_eq_comparison", Eq(ineq, expr))
            leq_pt.insert(0, pt_2.on_prop(replace_conv(pt_eq_comp)))
            if i != len(pts) - 1:
                pt_b = pt_1        

        return leq_pt

    def get_proof_term(self, args, prevs=None):
        """
        Let x_i denotes greater comparison, x__i denotes less comparison,
        for the greater comparison, find the smallest number x_min = min(x_1, ..., x_n), since x_min is positive, 
        x_min/2 > 0 ==> x_min >= x_min / 2 ==> x_1, ..., x_n >= x_min / 2 ==> ∃δ. δ > 0 ∧ x_1 >= δ ∧ ... ∧ x_n >= δ.
        for the less comparison, find the largest number x_max = max(x__1, ..., x__n), since x_max is negative, x_max < 
        x_max/2 ==> x__1, ..., x__n <= x_max/2;
        let δ = min(x_min/2, -x_max/2), then all x_i >= δ as well as all x__i <= -δ.
        """
        
        def need_convert(tm):
            return False if real_eval(tm.arg) != 0 else True
        
        original_ineq_pts = [ProofTerm.assume(ineq) for ineq in args]

        # record the ineq which rhs is not 0
        need_convert_pt = {arg for arg in args if need_convert(arg)}

        # record the args order
        order_args = {args[i].arg1: i for i in range(len(args))}

        # convert all ineqs to x_i > 0 or x_i < 0
        normal_ineq_pts = [pt.on_prop(norm_real_ineq_conv()) if pt.prop.arg != Real(0) else pt for pt in original_ineq_pts]

        # dividing less comparison and greater comparison
        greater_ineq_pts = [pt for pt in normal_ineq_pts if pt.prop.is_greater()]
        less_ineq_pts = [pt for pt in normal_ineq_pts if pt.prop.is_less()]

        # stage 1: get the max(min) pos bound
        # ⊢ min(...) ≥ δ_1, δ_1 > 0
        # ⊢ max(...) ≤ δ_2, δ_2 < 0
        pt_lower_bound, lower_bound_pos_pt, pt_assert_delta1 = self.handle_geq_stage1(greater_ineq_pts)
        pt_upper_bound, upper_bound_neg_pt, pt_assert_delta2 = self.handle_leq_stage1(less_ineq_pts)

        delta_1 = Var("δ_1", RealType)
        delta_2 = Var("δ_2", RealType)

        # generate the relaxed inequations
        if pt_lower_bound is None: # all comparisons are ≤
            pts = self.handle_leq_stage2(pt_upper_bound, less_ineq_pts, delta_2)
            bound_pt = upper_bound_neg_pt
            delta = delta_2
            pt_asserts = [pt_assert_delta2]
        elif pt_upper_bound is None: # all comparisons are ≥
            pts = self.handle_geq_stage2(pt_lower_bound, greater_ineq_pts, delta_1)
            bound_pt = lower_bound_pos_pt
            delta = delta_1
            pt_asserts = [pt_assert_delta1]
        else: # have both ≥ and ≤
            # ⊢ δ_1 ≥ min(δ_1, δ_2)
            pt_min_lower_bound = logic.apply_theorem("real_greater_min", inst=matcher.Inst(x=delta_1, y=delta_2))
            # ⊢ -δ_2 ≤ max(-δ_2, -δ_1)
            pt_max_upper_bound = logic.apply_theorem("real_less_max", inst=matcher.Inst(x=-delta_2, y=-delta_1))
            # ⊢ max(-δ_2, -δ_1) = -min(δ_1, δ_2)
            pt_max_min = logic.apply_theorem("max_min", inst=matcher.Inst(x=delta_1, y=delta_2))
            # ⊢ min(...) ≥ min(δ_1, δ_2)
            pt_new_lower_bound = logic.apply_theorem("real_geq_trans", pt_lower_bound, pt_min_lower_bound)
            # ⊢ -δ_2 ≤ -min(δ_1, δ_2)
            pt_max_upper_bound_1 = pt_max_upper_bound.on_prop(arg_conv(replace_conv(pt_max_min)))
            # ⊢ max(...) ≤ -min(δ_1, δ_2)
            pt_new_upper_bound = logic.apply_theorem("real_le_trans", pt_upper_bound, pt_max_upper_bound_1)
            # ⊢ min(δ_1, δ_2) > 0
            pt_new_lower_bound_pos = logic.apply_theorem("min_pos", lower_bound_pos_pt, upper_bound_neg_pt)
            # ⊢ min(δ_1, δ_2) = δ
            delta = Var("δ", RealType)
            pt_delta_eq = ProofTerm.assume(Eq(pt_min_lower_bound.prop.arg, delta))
            pt_asserts = [pt_delta_eq, pt_assert_delta1, pt_assert_delta2]
            # ⊢ min(...) ≥ δ
            pt_new_lower_bound_delta = pt_new_lower_bound.on_prop(arg_conv(replace_conv(pt_delta_eq)))
            # ⊢ max(...) ≤ -δ
            pt_new_upper_bound_delta = pt_new_upper_bound.on_prop(top_conv(replace_conv(pt_delta_eq)))
            # use new bound 
            pts_leq = self.handle_leq_stage2(pt_new_upper_bound_delta, less_ineq_pts, delta)
            pts_geq = self.handle_geq_stage2(pt_new_lower_bound_delta, greater_ineq_pts, delta)
            pts = pts_leq + pts_geq
            bound_pt = pt_new_lower_bound_pos.on_prop(arg1_conv(replace_conv(pt_delta_eq)))
        
        # sort_pts = sorted(pts, key=lambda pt: order_args[pt.prop.arg1])

        pt_conj = functools.reduce(lambda x, y: logic.apply_theorem("conjI", y, x), reversed([bound_pt] + pts))

        # get ⊢∃δ. δ > 0 ∧ x_1 >= δ ∧ ... ∧ x_n >= δ
        th = ProofTerm.theorem("exI")
        inst = matcher.first_order_match(th.prop.arg, Exists(delta, pt_conj.prop))
        pt_conj_exists = logic.apply_theorem("exI", pt_conj, inst=inst)
        pt_final = pt_conj_exists
        for pt_subst in pt_asserts:
            lhs, rhs = pt_subst.prop.args
            if not rhs.is_uminus():
                pt_final = pt_final.implies_intr(pt_subst.prop).forall_intr(rhs).\
                            forall_elim(lhs).implies_elim(ProofTerm.reflexive(lhs))
            else:
                pt_final = pt_final.implies_intr(pt_subst.prop).forall_intr(rhs.arg).\
                    forall_elim(-lhs).on_prop(top_conv(rewr_conv("real_neg_neg"))).implies_elim(ProofTerm.reflexive(lhs))
        return pt_final