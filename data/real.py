# Author: Bohua Zhan

from fractions import Fraction
import math
import sympy
from sympy.ntheory.factor_ import factorint

from kernel.type import Type, TFun, boolT
from kernel import term
from kernel.term import Term, Const
from kernel.thm import Thm
from kernel.theory import Method, global_methods
from kernel import macro
from data import binary
from data import nat
from data.set import setT
from logic import logic
from logic import auto
from logic.logic import TacticException
from logic.conv import rewr_conv, binop_conv, arg1_conv, arg_conv, Conv, ConvException
from logic.proofterm import refl, ProofMacro, ProofTermMacro, ProofTermDeriv
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
inverse = Const("real_inverse", TFun(realT, realT))
less_eq = Const("less_eq", TFun(realT, realT, boolT))
less = Const("less", TFun(realT, realT, boolT))
greater_eq = Const("greater_eq", TFun(realT, realT, boolT))
greater = Const("greater", TFun(realT, realT, boolT))
nat_power = Const("power", TFun(realT, nat.natT, realT))
real_power = Const("power", TFun(realT, realT, realT))
sqrt = Const("sqrt", TFun(realT, realT))
pi = Const("pi", realT)

# Transcendental functions

log = Const("log", TFun(realT, realT))
exp = Const("exp", TFun(realT, realT))
sin = Const("sin", TFun(realT, realT))
cos = Const("cos", TFun(realT, realT))
tan = Const("tan", TFun(realT, realT))
abs = Const("abs", TFun(realT, realT))
sqrt = Const("sqrt", TFun(realT, realT))
atn = Const("atn", TFun(realT, realT))

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

def is_real_power(t):
    return t.is_binop() and t.head == real_power

def is_less_eq(t):
    return t.is_binop() and t.head == less_eq

def is_less(t):
    return t.is_binop() and t.head == less

def to_binary_real(n):
    """Convert a number n to HOL term of type real."""
    if n < 0:
        return uminus(to_binary_real(-n))

    if isinstance(n, Fraction):
        if n.denominator == 1:
            return to_binary_real(n.numerator)
        else:
            return divides(to_binary_real(n.numerator), to_binary_real(n.denominator))
        
    if n == 0:
        return zero
    elif n == 1:
        return one
    else:
        return of_nat(nat.to_binary(n))

def is_binary_real(t):
    """Determine whether a term of type real is a constant."""
    if t.head == uminus and len(t.args) == 1:
        return is_binary_real(t.arg)
    elif t.head == divides and len(t.args) == 2:
        return is_binary_real(t.arg1) and is_binary_real(t.arg)
    else:
        return t == zero or t == one or \
               (t.is_comb() and t.fun == of_nat and
                nat.is_binary(t.arg) and nat.from_binary(t.arg) >= 2)

def from_binary_real(t):
    """Convert a term of type real to a number."""
    assert isinstance(t, Term), "from_binary_real"
    assert is_binary_real(t), "from_binary_real"
    if t.head == uminus:
        return -from_binary_real(t.arg)
    elif t.head == divides:
        return Fraction(from_binary_real(t.arg1)) / from_binary_real(t.arg)
    elif t == zero:
        return 0
    elif t == one:
        return 1
    else:
        return nat.from_binary(t.arg)

def real_eval(t):
    """Evaluate t as a constant. Return an integer or rational number.

    Assume t does not contain non-rational constants.

    """
    def rec(t):
        if is_binary_real(t):
            return from_binary_real(t)
        elif t.head.is_const_name('of_nat'):
            return nat.nat_eval(t.arg)
        elif is_plus(t):
            return rec(t.arg1) + rec(t.arg)
        elif is_minus(t):
            return rec(t.arg1) - rec(t.arg)
        elif is_uminus(t):
            return -rec(t.arg)
        elif is_times(t):
            return rec(t.arg1) * rec(t.arg)
        elif is_divides(t):
            denom = rec(t.arg)
            if denom == 0:
                raise ConvException('real_eval: divide by zero')
            elif denom == 1:
                return rec(t.arg1)
            else:
                return Fraction(rec(t.arg1)) / denom
        elif is_nat_power(t):
            return rec(t.arg1) ** nat.nat_eval(t.arg)
        elif is_real_power(t):
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

class real_eval_macro(ProofMacro):
    """Simplify all arithmetic operations."""
    def __init__(self):
        self.level = 0  # No expand implemented
        self.sig = Term
        self.limit = None

    def eval(self, thy, goal, prevs):
        assert len(prevs) == 0, "real_eval_macro: no conditions expected"
        assert goal.is_equals(), "real_eval_macro: goal must be an equality"
        assert real_eval(goal.lhs) == real_eval(goal.rhs), "real_eval_macro: two sides are not equal"

        return Thm([], goal)

class real_eval_conv(Conv):
    """Simplify all arithmetic operations."""
    def get_proof_term(self, thy, t):
        simp_t = to_binary_real(real_eval(t))
        if simp_t == t:
            return refl(t)
        return ProofTermDeriv('real_eval', thy, Term.mk_equals(t, simp_t))


"""Normalization of polynomials.

Each monomial is in the form x, c * x, or c, where c is a numerical
constant (may be rational) and x is a product of atoms.

Each atom is of the form x ^ n (nat_power), x ^ r (real_power), or
simply x (no powers). Powers are combined (e.g. x ^ m * x ^ n = x ^ (m + n))
but not automatically expanded.

"""

def dest_monomial(t):
    """Remove the coefficient part of a monomial t."""
    if is_times(t) and is_binary_real(t.arg1):
        return t.arg
    elif is_binary_real(t):
        return one
    else:
        return t

class to_coeff_form(Conv):
    """Convert c to c * 1, x to 1 * x, and leave c * x unchanged."""
    def get_proof_term(self, thy, t):
        pt = refl(t)
        if is_times(t) and is_binary_real(t.arg1):
            return pt
        elif is_binary_real(t):  # c to c * 1
            return pt.on_rhs(thy, rewr_conv('real_mul_rid', sym=True))
        else:  # x to 1 * x
            return pt.on_rhs(thy, rewr_conv('real_mul_lid', sym=True))

class from_coeff_form(Conv):
    """Convert c * 1 to c, 1 * x to x, and leave c * x unchanged."""
    def get_proof_term(self, thy, t):
        pt = refl(t)
        if t.arg == one:
            return pt.on_rhs(thy, rewr_conv('real_mul_rid'))
        elif t.arg1 == one:
            return pt.on_rhs(thy, rewr_conv('real_mul_lid'))
        elif t.arg == zero:
            return pt.on_rhs(thy, rewr_conv('real_mul_rzero'))
        elif t.arg1 == zero:
            return pt.on_rhs(thy, rewr_conv('real_mul_lzero'))
        else:
            return pt

class combine_monomial(Conv):
    """Combine (add) two monomials with the same body."""
    def get_proof_term(self, thy, t):
        return refl(t).on_rhs(thy,
            binop_conv(to_coeff_form()),
            rewr_conv('real_add_rdistrib', sym=True),
            arg1_conv(real_eval_conv()),
            from_coeff_form())

class swap_add_r(Conv):
    """Rewrite (a + b) + c to (a + c) + b."""
    def get_proof_term(self, thy, t):
        pt = refl(t)
        return pt.on_rhs(thy,
            rewr_conv('real_add_assoc', sym=True),
            arg_conv(rewr_conv('real_add_comm')),
            rewr_conv('real_add_assoc'))

def atom_less(t1, t2):
    """Compare two atoms, put constants in front."""
    if not term.has_var(t1) and term.has_var(t2):
        return True
    elif not term.has_var(t2) and term.has_var(t1):
        return False
    else:
        return t1 < t2

class norm_add_monomial(Conv):
    """Normalize expression of the form (a_1 + ... + a_n) + b."""
    def get_proof_term(self, thy, t):
        pt = refl(t)
        if t.arg1 == zero:
            return pt.on_rhs(thy, rewr_conv("real_add_lid"))
        elif t.arg == zero:
            return pt.on_rhs(thy, rewr_conv("real_add_rid"))
        elif is_plus(t.arg1):
            # Left side has more than one term. Compare last term with a
            m1, m2 = dest_monomial(t.arg1.arg), dest_monomial(t.arg)
            if m1 == m2:
                pt = pt.on_rhs(thy,
                    rewr_conv('real_add_assoc', sym=True),
                    arg_conv(combine_monomial()))
                if pt.rhs.arg == zero:
                    pt = pt.on_rhs(thy, rewr_conv('real_add_rid'))
                return pt
            elif atom_less(m1, m2):
                return pt
            else:
                pt = pt.on_rhs(thy, swap_add_r(), arg1_conv(self))
                if pt.rhs.arg1 == zero:
                    pt = pt.on_rhs(thy, rewr_conv('real_add_lid'))
                return pt
        else:
            # Left side is an atom. Compare two sides
            m1, m2 = dest_monomial(t.arg1), dest_monomial(t.arg)
            if m1 == m2:
                return pt.on_rhs(thy, combine_monomial())
            elif atom_less(m1, m2):
                return pt
            else:
                return pt.on_rhs(thy, rewr_conv('real_add_comm'))

class norm_add_polynomial(Conv):
    """Normalize expression of the form (a_1 + ... + a_n) + (b_1 + ... + b_m)."""
    def get_proof_term(self, thy, t):
        pt = refl(t)
        if is_plus(t.arg):
            return pt.on_rhs(thy, rewr_conv('real_add_assoc'), arg1_conv(self), norm_add_monomial())
        else:
            return pt.on_rhs(thy, norm_add_monomial())

auto.add_global_autos_norm(plus, norm_add_polynomial())


def dest_atom(t):
    """Remove power part of an atom t."""
    if t.head == exp:
        return exp(one)
    elif is_nat_power(t) and nat.is_binary_nat(t.arg):
        return t.arg1
    elif is_real_power(t) and is_binary_real(t.arg):
        return t.arg1
    else:
        return t

class to_exponent_form(Conv):
    """Convert x to x ^ 1, and leave x ^ n or x ^ r unchanged."""
    def get_proof_term(self, thy, t):
        pt = refl(t)
        if t.head == exp:
            return pt
        elif is_nat_power(t) and nat.is_binary_nat(t.arg):
            return pt
        elif is_real_power(t) and is_binary_real(t.arg):
            return pt
        else:
            return pt.on_rhs(thy, rewr_conv('real_pow_1', sym=True))

class from_exponent_form(Conv):
    """Convert x ^ 1 to x, and leave x ^ n or x ^ r unchanged."""
    def get_proof_term(self, thy, t):
        pt = refl(t)
        if t.head == exp:
            return pt
        elif is_nat_power(t) and t.arg == nat.one:
            return pt.on_rhs(thy, rewr_conv('real_pow_1'))
        elif is_real_power(t) and t.arg == one:
            return pt.on_rhs(thy, rewr_conv('rpow_1'))
        elif is_real_power(t) and t.arg == zero:
            return pt.on_rhs(thy, rewr_conv('rpow_0'))
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

    def get_proof_term(self, thy, t):
        pt = refl(t).on_rhs(thy, binop_conv(to_exponent_form()))
        if pt.rhs.arg1.head == exp and pt.rhs.arg.head == exp:
            # Both sides are exponentials
            return pt.on_rhs(thy, rewr_conv('real_exp_add', sym=True), arg_conv(auto.auto_conv(self.conds)))
        elif is_nat_power(pt.rhs.arg1) and is_nat_power(pt.rhs.arg):
            # Both sides are natural number powers, simply add
            return pt.on_rhs(thy, rewr_conv('real_pow_add', sym=True), arg_conv(nat.nat_conv()))
        else:
            # First check that x > 0 can be proved. If not, just return
            # without change.
            x = pt.rhs.arg1.arg1
            try:
                x_ge_0 = auto.solve(thy, greater(x, zero), self.conds)
            except TacticException:
                return refl(t)

            # Convert both sides to real powers
            if is_nat_power(pt.rhs.arg1):
                pt = pt.on_rhs(thy, arg1_conv(rewr_conv('rpow_pow', sym=True)))
            if is_nat_power(pt.rhs.arg):
                pt = pt.on_rhs(thy, arg_conv(rewr_conv('rpow_pow', sym=True)))
            pt = pt.on_rhs(thy, rewr_conv('rpow_add', sym=True, conds=[x_ge_0]), arg_conv(real_eval_conv()))

            # Simplify back to nat if possible
            if pt.rhs.arg.head == of_nat:
                pt = pt.on_rhs(thy,
                    rewr_conv('rpow_pow'),
                    arg_conv(rewr_conv('nat_of_nat_def', sym=True)))

            return pt.on_rhs(thy, from_exponent_form())

class swap_mult_r(Conv):
    """Rewrite (a * b) * c to (a * c) * b."""
    def get_proof_term(self, thy, t):
        pt = refl(t)
        return pt.on_rhs(thy,
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

    def get_proof_term(self, thy, t):
        pt = refl(t)
        if t.arg1 == one:
            return pt.on_rhs(thy, rewr_conv('real_mul_lid'))
        elif t.arg == one:
            return pt.on_rhs(thy, rewr_conv('real_mul_rid'))
        elif is_times(t.arg1):
            # Left side has more than one atom. Compare last atom with b
            m1, m2 = dest_atom(t.arg1.arg), dest_atom(t.arg)
            if m1 == m2:
                pt = pt.on_rhs(thy,
                    rewr_conv('real_mult_assoc', sym=True),
                    arg_conv(combine_atom(self.conds)))
                if pt.rhs.arg == one:
                    pt = pt.on_rhs(thy, rewr_conv('real_mul_rid'))
                return pt
            elif atom_less(m1, m2):
                return pt
            else:
                pt = pt.on_rhs(thy, swap_mult_r(), arg1_conv(self))
                if pt.rhs.arg1 == one:
                    pt = pt.on_rhs(thy, rewr_conv('real_mul_lid'))
                return pt
        else:
            # Left side is an atom. Compare two sides
            m1, m2 = dest_atom(t.arg1), dest_atom(t.arg)
            if m1 == m2:
                return pt.on_rhs(thy, combine_atom(self.conds))
            elif atom_less(m1, m2):
                return pt
            else:
                return pt.on_rhs(thy, rewr_conv('real_mult_comm'))

class norm_mult_monomial(Conv):
    """Normalize expression of the form (a_1 * ... * a_n) * (b_1 * ... * b_m)."""
    def __init__(self, conds):
        self.conds = conds

    def get_proof_term(self, thy, t):
        pt = refl(t)
        if is_times(t.arg):
            return pt.on_rhs(thy, rewr_conv('real_mult_assoc'), arg1_conv(self), norm_mult_atom(self.conds))
        else:
            return pt.on_rhs(thy, norm_mult_atom(self.conds))

class norm_mult_monomials(Conv):
    """Normalize (c_1 * m_1) * (c_2 * m_2), where c_1, c_2 are constants,
    and m_1, m_2 are monomials.

    """
    def __init__(self, conds):
        self.conds = conds

    def get_proof_term(self, thy, t):
        pt = refl(t)
        return pt.on_rhs(thy,
            binop_conv(to_coeff_form()),
            rewr_conv('real_mult_assoc'),  # (c_1 * m_1 * c_2) * m_2
            arg1_conv(swap_mult_r()),  # (c_1 * c_2 * m_1) * m_2
            arg1_conv(arg1_conv(real_eval_conv())),  # (c_1c_2 * m_1) * m_2
            rewr_conv('real_mult_assoc', sym=True),  # c_1c_2 * (m_1 * m_2)
            arg_conv(norm_mult_monomial(self.conds)),
            from_coeff_form())

def norm_mult(thy, t, pts):
    """Normalization of mult. Assume two sides are in normal form."""
    pt = refl(t)
    if is_plus(t.arg1):
        return pt.on_rhs(thy, rewr_conv('real_add_rdistrib'))
    elif is_plus(t.arg):
        return pt.on_rhs(thy, rewr_conv('real_add_ldistrib'))
    else:
        return pt.on_rhs(thy, norm_mult_monomials(pts))

auto.add_global_autos_norm(times, norm_mult)

def norm_uminus(thy, t, pts):
    """Normalization of uminus."""
    pt = refl(t)
    if is_binary_real(t):
        return pt.on_rhs(thy, real_eval_conv())
    else:
        return pt.on_rhs(thy, rewr_conv('real_poly_neg1'))

auto.add_global_autos_norm(uminus, norm_uminus)

auto.add_global_autos_norm(minus, auto.norm_rules(['real_poly_neg2']))

def norm_divides(thy, t, pts):
    """Normalization of divides."""
    pt = refl(t)
    if is_binary_real(t):
        return pt.on_rhs(thy, real_eval_conv())
    else:
        return pt.on_rhs(thy, rewr_conv('real_divide_def'))

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

auto.add_global_autos_norm(
    nat_power,
    auto.norm_rules([
        'real_nat_power_def_1',
        'real_nat_power_def_2',
        'real_pow_1',
        'real_pow_one',
        'real_pow_mul',
        'real_pow_pow',
        'rpow_mult_nat2',
        'real_exp_n_sym',
    ])
)

auto.add_global_autos_norm(nat_power, real_eval_conv())

auto.add_global_autos_norm(
    real_power,
    auto.norm_rules([
        'rpow_0',
        'rpow_1',
        'rpow_mult',
        'rpow_mult_nat1',
        'rpow_base_mult',
        'rpow_base_mult2',
        'rpow_base_divide',
        'rpow_exp',
        'rpow_abs',
    ])
)

class real_power_conv(Conv):
    def get_proof_term(self, thy, t):
        a, p = t.args

        # Exponent is an integer: apply rpow_pow
        if is_binary_real(p) and p.is_comb() and binary.is_binary(p.arg):
            pt = refl(t)
            pt = pt.on_rhs(thy, arg_conv(rewr_conv('real_of_nat_id', sym=True)),
                                rewr_conv('rpow_pow'))
            return pt

        if not (is_binary_real(a) and is_binary_real(p)):
            raise ConvException

        a, p = from_binary_real(a), from_binary_real(p)
        if a <= 0:
            raise ConvException

        # Case 1: base is a composite number
        factors = factorint(a)
        keys = list(factors.keys())
        if len(keys) > 1 or (len(keys) == 1 and keys[0] != a):
            b1 = list(factors.keys())[0]
            b2 = a // b1
            eq_th = refl(times(to_binary_real(b1), to_binary_real(b2))).on_rhs(thy, real_eval_conv())
            pt = refl(t).on_rhs(thy, arg1_conv(rewr_conv(eq_th, sym=True)))
            b1_gt_0 = auto.auto_solve(thy, greater(to_binary_real(b1), zero))
            b2_gt_0 = auto.auto_solve(thy, greater(to_binary_real(b2), zero))
            pt = pt.on_rhs(thy, rewr_conv('rpow_base_mult', conds=[b1_gt_0, b2_gt_0]))
            return pt

        # Case 2: exponent is not between 0 and 1
        if isinstance(p, Fraction) and p.numerator // p.denominator != 0:
            div, mod = divmod(p.numerator, p.denominator)
            eq_th = refl(plus(to_binary_real(div), divides(to_binary_real(mod), to_binary_real(p.denominator))))
            eq_th = eq_th.on_rhs(thy, real_eval_conv())
            pt = refl(t).on_rhs(thy, arg_conv(rewr_conv(eq_th, sym=True)))
            a_gt_0 = auto.auto_solve(thy, greater(to_binary_real(a), zero))
            pt = pt.on_rhs(thy, rewr_conv('rpow_add', conds=[a_gt_0]))
            return pt

        return refl(t)

auto.add_global_autos_norm(real_power, real_power_conv())
auto.add_global_autos_norm(real_power, real_eval_conv())

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
),

auto.add_global_autos_norm(
    less_eq,
    auto.norm_rules([
        'log_le_zero'
    ])
)

auto.add_global_autos(
    greater_eq,
    auto.solve_rules([
        'real_ge_mul',
        'real_ge_divide'
    ])
)

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
    elif is_real_power(t):
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
    "real_eval": real_eval_macro(),
    "real_norm": real_norm_macro()
})

global_methods.update({
    "real_norm": real_norm_method()
})
