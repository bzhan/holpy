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
abs = Const("abs", TFun(RealType, RealType))
sqrt = Const("sqrt", TFun(RealType, RealType))
atn = Const("atn", TFun(RealType, RealType))

# Intervals

closed_interval = Const("real_closed_interval", TFun(RealType, RealType, setT(RealType)))
open_interval = Const("real_open_interval", TFun(RealType, RealType, setT(RealType)))


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

        return Thm([], goal)

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
        a, p = t.args

        # Exponent is 2
        if p.is_number() and p.dest_number() == 2 and a.is_plus():
            return refl(t).on_rhs(rewr_conv('real_pow_2'),
                                  rewr_conv('real_add_rdistrib'))

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

auto.add_global_autos_norm(
    greater_eq,
    auto.norm_rules([
        'log_ge_zero'
    ])
)

auto.add_global_autos_norm(
    greater,
    auto.norm_rules([
        'log_gt_zero'
    ])
)

auto.add_global_autos_norm(
    less_eq,
    auto.norm_rules([
        'log_le_zero'
    ])
)

auto.add_global_autos_norm(
    less,
    auto.norm_rules([
        'log_lt_zero'
    ])
)

auto.add_global_autos(
    greater_eq,
    auto.solve_rules([
        'real_ge_add',
        'real_ge_mul',
        'real_ge_divide'
    ])
)

auto.add_global_autos(
    greater,
    auto.solve_rules([
        'real_gt_add',
        'real_gt_mul'
    ])
)

auto.add_global_autos_neg(
    equals,
    auto.solve_rules([
        'real_gt_to_neq'
    ])
)

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

        return Thm([], goal)

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
    1) a < b <==> 0 < b - a
    2) a > b <==> 0 < a - b
    3) a ≤ b <==> 0 ≤ b - a
    4) a ≥ b <==> 0 ≤ a - b
    """
    def get_proof_term(self, tm):
        if not is_real_ineq(tm):
            raise ConvException("Invalid term: %s" % str(tm))
        if tm.is_less():
            return rewr_conv('real_sub_lt', sym=True).get_proof_term(tm).on_rhs(arg_conv(auto.auto_conv()))
        elif tm.is_greater():
            return rewr_conv('real_ge_to_le').get_proof_term(tm).on_rhs(norm_real_ineq_conv())
        elif tm.is_less_eq():
            return rewr_conv('real_sub_le', sym=True).get_proof_term(tm).on_rhs(arg_conv(auto.auto_conv()))
        elif tm.is_greater_eq():
            return rewr_conv('real_geq_to_leq').get_proof_term(tm).on_rhs(norm_real_ineq_conv())

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
        if tm.arg.is_less():
            return rewr_conv('real_not_lt').get_proof_term(tm)
        elif tm.arg.is_greater():
            return arg_conv(rewr_conv('real_ge_to_le')).get_proof_term(tm).on_rhs(norm_neg_real_ineq_conv())
        elif tm.arg.is_less_eq():
            return rewr_conv('real_not_leq').get_proof_term(tm)
        else:
            return arg_conv(rewr_conv('real_geq_to_leq')).get_proof_term(tm).on_rhs(norm_neg_real_ineq_conv())

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
                    return Thm([], Eq(goal, true))
                else:
                    return Thm([], Eq(goal, false))
            else: # inequations
                lhs, rhs = real_eval(goal.arg1), real_eval(goal.arg)
                if goal.is_less():
                    return Thm([], Eq(goal, true)) if lhs < rhs else Thm([], Eq(goal, false))
                elif goal.is_less_eq():
                    return Thm([], Eq(goal, true)) if lhs <= rhs else Thm([], Eq(goal, false))
                elif goal.is_greater():
                    return Thm([], Eq(goal, true)) if lhs > rhs else Thm([], Eq(goal, false))
                elif goal.is_greater_eq():
                    return Thm([], Eq(goal, true)) if lhs >= rhs else Thm([], Eq(goal, false))
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

class replace_conv(Conv):
    def __init__(self, pt):
        self.pt = pt

    def get_proof_term(self, t):
        if t == self.pt.prop.lhs:
            return self.pt
        else:
            raise ConvException

@register_macro('non_strict_simplex')
class relax_strict_simplex_macro(Macro):
    """
    Given a set of strict inequalities, 
        x_1 > b_1,
        x_2 < b_2,
        ... 
        x_n < b_n,

    return a proof term: x_1 > b_1, ... , x_n < b_n ⊢ ∃δ. δ > 0 ∧ x_1 >= b_1 + δ ∧ ... ∧ x_n <= b_n - δ 
    """
    def __init__(self):
        self.level = 1
        self.sig = typing.List[Term]
        self.limit = None

    def get_proof_term(self, args, prevs=None):
        """
        The strategy is to prove ¬(x_1 > b_1 ⟶ ... ⟶ x_n < b_n ⟶ ∃δ. δ > 0 ∧ x_1 ≥ b_1 + δ ∧ ... ∧ x_n ≤ b_n - δ) ⊢ false.
    
        Use the above hypothesis, we can derive 
        (1)                    ⊢ ∀δ. ¬(δ > 0 ∧ x_1 ≥ b_1 + δ ∧ ... ∧ x_n ≤ b_n - δ)
        and
        (2)                    ⊢ x_1 > b_1, ..., x_n < b_n
        then instantiate δ with x_i - b_i(if x_i > b_i), or b_i - x_i(if b_i > x_i), we can get
        (3)                    ⊢ ¬(x_i - b_i > 0 ∧ x_1 ≥ x_1 ∧ ... ∧ x_n ≤ b_n - x_i + b_i)...
        we know that x_i - b_i > 0(w.r.t b_i - x_i > 0) and x_i ≥ x_i(x_i ≤ x_i) are always true, so we can elimate them,
        then each proposition is a disjunction and contains n - 1 ICs, we can observe a property for the n proof terms,
        we have n ICs, there are n * (n-1)/2 pairs for the combination of them, we have n * (n-1) ICs, if an IC is a < b, there
        is always existing an IC of b < a form, we know that ⊢ a < b ⟶ b < a ⟶ false, this is just like resolution, after resolution,
        we can derive false.
        """
        # first get the proof terms of x_1 - b_1 > 0
        
        # construct term x_1 > b_1 ⟶ ... ⟶ x_n < b_n ⟶ ∃δ. x_1 >= b_1 + δ ∧ ... ∧ x_n <= b_n - δ
        delta = Var("δ", RealType)
        non_strict_tms = [greater_eq(t.arg1, t.arg + delta) if t.is_greater() else
                        less_eq(t.arg1, t.arg - delta) for t in args]
        exists_tm = Exists(delta, And(delta > Real(0), *non_strict_tms))
        implies_tm = functools.reduce(lambda x, y: Implies(y, x), reversed(args), exists_tm)
        # proof
        pt0 = ProofTerm.assume(Not(implies_tm))
        # get ⊢ x_1 > b_1, ..., ⊢ x_n < b_n
        strict_ineq_pts = []
        aux_pt = pt0
        for i in range(len(args)):
            pt_strict = logic.apply_theorem("veriT_not_implies1", aux_pt)
            aux_pt = logic.apply_theorem("veriT_not_implies2", aux_pt)
            strict_ineq_pts.append(pt_strict)
        # get ⊢ x_1 - b_1 > 0, ..., ⊢ b_n - x_n > 0
        # delta_inst_dict = {pt.prop.arg1: pt.on_prop(rewr_conv('real_gt_sub')) if pt.prop.is_greater()
        #         else pt.on_prop(rewr_conv('real_ge_to_le', sym=True), rewr_conv('real_gt_sub')) for pt in strict_ineq_pts}
        delta_inst_dict = {}
        for pt in strict_ineq_pts:
            if pt.prop.is_greater():
                pt_comp = pt.on_prop(rewr_conv('real_gt_sub'))
            else:
                pt_comp = pt.on_prop(rewr_conv('real_ge_to_le', sym=True), rewr_conv('real_gt_sub'))
            delta_inst_dict.update({pt_comp.prop.arg1: pt_comp})
        # get ⊢ ∀δ. ¬(δ > 0 ∧ x_1 ≥ b_1 + δ ∧ ... ∧ x_n ≤ b_n - δ)
        pt1 = aux_pt.on_prop(rewr_conv("not_exists"))
        # instantiate δ with x_i - b_i(b_i - x_i) and elinmate x_i - b_i > 0(w.r.t b_i - x_i > 0) and x_i ≥ x_i(x_i ≤ x_i) 
        pt_leq_than_self = logic.apply_theorem("real_le_refl", inst=matcher.Inst(x=Real(0)))
        pt_geq_than_self = pt_leq_than_self.on_prop(rewr_conv("real_geq_to_leq", sym=True))
        inst_pts = [pt1.forall_elim(value).on_prop(top_conv(replace_conv(pt.on_prop(rewr_conv("eq_true")))), 
                            top_conv(real_norm_comparison()), 
                            top_conv(replace_conv(pt_leq_than_self.on_prop(rewr_conv("eq_true")))),
                            top_conv(replace_conv(pt_geq_than_self.on_prop(rewr_conv("eq_true")))),
                            top_conv(proplogic.norm_full()),
                            top_conv(rewr_conv("real_not_leq")),
                            top_conv(rewr_conv("real_not_geq")),
                            top_conv(rewr_conv("real_gt_neg_lt")),) for value, pt in delta_inst_dict.items()]

        if len(inst_pts) == 1:
            pt = inst_pts[0]
            return logic.apply_theorem("negI", pt.implies_intr(pt.hyps[0])).on_prop(rewr_conv("double_neg"))
        # d is mapping from left hand side to the proof term it belongs to, every key have 2 proof terms, one is its
        # positive form and the other is its negative form
        d_pos, d_neg = {}, {}
        for pt in inst_pts:
            disjs = pt.prop.strip_disj()
            for disj in disjs:
                if disj.is_not():
                    d_neg[disj.arg] = pt
                else:
                    d_pos[disj] = pt
        assert len(d_pos) == len(d_neg) # not strong enough
        # do resolution
        for key in list(d_pos.keys()):
            pt = logic.resolution(d_pos[key], d_neg[key])
            if pt.prop == false:
                break
            if pt.prop.is_disj():
                disjs = pt.prop.strip_disj()
            else:
                disjs = [pt.prop]

            for disj in disjs:
                if disj.is_not():
                    d_neg[disj.arg] = pt
                else:
                    d_pos[disj] = pt

        return logic.apply_theorem("negI", pt.implies_intr(pt.hyps[0])).on_prop(rewr_conv("double_neg"))