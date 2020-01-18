# Author: Bohua Zhan

from kernel.type import Type, TFun, boolT
from kernel import term
from kernel.term import Term, Const
from kernel.thm import Thm
from kernel.theory import Method, global_methods
from kernel import macro
from data import binary
from data.binary import bit0, bit1, to_binary, from_binary, is_binary
from logic.conv import Conv, ConvException, all_conv, rewr_conv, \
    then_conv, arg_conv, arg1_conv, every_conv, binop_conv
from logic.proofterm import ProofTerm, ProofMacro, ProofTermMacro, ProofTermDeriv, refl
from logic import auto
from logic.logic import apply_theorem
from logic import logic
from logic import term_ord
from server.tactic import MacroTactic
from syntax import pprint, settings
from util import poly


"""Utility functions for natural number arithmetic."""

# Basic definitions

natT = binary.natT
zero = binary.zero
one = binary.one
Suc = Const("Suc", TFun(natT, natT))
Pre = Const("Pre", TFun(natT, natT))
of_nat = Const("of_nat", TFun(natT, natT))
plus = Const("plus", TFun(natT, natT, natT))
minus = Const("minus", TFun(natT, natT, natT))
times = Const("times", TFun(natT, natT, natT))
less_eq = Const("less_eq", TFun(natT, natT, boolT))
less = Const("less", TFun(natT, natT, boolT))

def is_Suc(t):
    return t.is_comb() and t.fun == Suc

def is_Pre(t):
    return t.is_comb() and t.fun == Pre

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

def is_plus(t):
    return t.is_binop() and t.head == plus

def is_minus(t):
    return t.is_binop() and t.head == minus

def is_times(t):
    return t.is_binop() and t.head == times

def is_less_eq(t):
    return t.is_binop() and t.head == less_eq

def is_less(t):
    return t.is_binop() and t.head == less

# Arithmetic on binary numbers

def to_binary_nat(n):
    """Convert Python integer n to HOL binary form (appending of_nat)."""
    assert isinstance(n, int) and n >= 0, "to_binary_nat"
    if n == 0:
        return zero
    elif n == 1:
        return one
    else:
        return of_nat(to_binary(n))

def is_binary_nat(t):
    return t == zero or t == one or \
           (t.is_comb() and t.fun.is_const_name("of_nat") and
            is_binary(t.arg) and from_binary(t.arg) >= 2)

def from_binary_nat(t):
    """Convert HOL binary form (with of_nat) to Python integer."""
    assert is_binary_nat(t), "from_binary_nat"
    if t == zero:
        return 0
    elif t == one:
        return 1
    else:
        return from_binary(t.arg)

def convert_to_poly(t):
    """Convert natural number expression to polynomial."""
    if t.is_var():
        return poly.singleton(t)
    elif is_binary_nat(t):
        return poly.constant(from_binary_nat(t))
    elif is_plus(t):
        t1, t2 = t.args
        return convert_to_poly(t1) + convert_to_poly(t2)
    elif is_times(t):
        t1, t2 = t.args
        return convert_to_poly(t1) * convert_to_poly(t2)
    elif is_minus(t):
        t1, t2 = t.args
        p1, p2 = convert_to_poly(t1), convert_to_poly(t2)
        if p1.is_constant() and p2.is_constant():
            n1 = p1.get_constant()
            n2 = p2.get_constant()
            if n1 <= n2:
                return poly.constant(0)
            else:
                return poly.constant(n1 - n2)
        else:
            return poly.singleton(t)
    else:
        return poly.singleton(t)

class Suc_conv(Conv):
    """Computes Suc of a binary number."""
    def eval(self, thy, t):
        return Thm.mk_equals(t, to_binary(from_binary(t.arg) + 1))

    def get_proof_term(self, thy, t):
        n = t.arg  # remove Suc
        pt = refl(t)
        if n == zero:
            return pt.on_rhs(thy, rewr_conv("nat_one_def", sym=True))
        elif n == one:
            return pt.on_rhs(thy, rewr_conv("one_Suc"))
        elif n.head == bit0:
            return pt.on_rhs(thy, rewr_conv("bit0_Suc"))
        else:
            return pt.on_rhs(thy, rewr_conv("bit1_Suc"), arg_conv(self))

class add_conv(Conv):
    """Computes the sum of two binary numbers."""
    def eval(self, thy, t):
        return Thm.mk_equals(t, to_binary(from_binary(t.arg1) + from_binary(t.arg)))

    def get_proof_term(self, thy, t):
        if not (is_plus(t) and is_binary(t.arg1) and is_binary(t.arg)):
            raise ConvException("add_conv")
        pt = refl(t)
        n1, n2 = t.arg1, t.arg  # two summands
        if n1 == zero:
            return pt.on_rhs(thy, rewr_conv("nat_plus_def_1"))
        elif n2 == zero:
            return pt.on_rhs(thy, rewr_conv("add_0_right"))
        elif n1 == one:
            return pt.on_rhs(thy, rewr_conv("add_1_left"), Suc_conv())
        elif n2 == one:
            return pt.on_rhs(thy, rewr_conv("add_1_right"), Suc_conv())
        elif n1.head == bit0 and n2.head == bit0:
            return pt.on_rhs(thy, rewr_conv("bit0_bit0_add"), arg_conv(self))
        elif n1.head == bit0 and n2.head == bit1:
            return pt.on_rhs(thy, rewr_conv("bit0_bit1_add"), arg_conv(self))
        elif n1.head == bit1 and n2.head == bit0:
            return pt.on_rhs(thy, rewr_conv("bit1_bit0_add"), arg_conv(self))
        else:
            return pt.on_rhs(thy, rewr_conv("bit1_bit1_add"),
                             arg_conv(arg_conv(self)), arg_conv(Suc_conv()))

class mult_conv(Conv):
    """Computes the product of two binary numbers."""
    def eval(self, thy, t):
        return Thm.mk_equals(t, to_binary(from_binary(t.arg1) * from_binary(t.arg)))

    def get_proof_term(self, thy, t):
        n1, n2 = t.arg1, t.arg  # two summands
        pt = refl(t)
        if n1 == zero:
            return pt.on_rhs(thy, rewr_conv("nat_times_def_1"))
        elif n2 == zero:
            return pt.on_rhs(thy, rewr_conv("mult_0_right"))
        elif n1 == one:
            return pt.on_rhs(thy, rewr_conv("mult_1_left"))
        elif n2 == one:
            return pt.on_rhs(thy, rewr_conv("mult_1_right"))
        elif n1.head == bit0 and n2.head == bit0:
            return pt.on_rhs(thy, rewr_conv("bit0_bit0_mult"), arg_conv(arg_conv(self)))
        elif n1.head == bit0 and n2.head == bit1:
            return pt.on_rhs(thy, rewr_conv("bit0_bit1_mult"), arg_conv(self))
        elif n1.head == bit1 and n2.head == bit0:
            return pt.on_rhs(thy, rewr_conv("bit1_bit0_mult"), arg_conv(self))
        else:
            return pt.on_rhs(thy, rewr_conv("bit1_bit1_mult"),
                             arg_conv(arg1_conv(add_conv())),
                             arg_conv(arg_conv(arg_conv(self))),
                             arg_conv(add_conv()))

class rewr_of_nat_conv(Conv):
    """Remove or apply of_nat."""
    def __init__(self, *, sym=False):
        self.sym = sym

    def get_proof_term(self, thy, t):
        pt = refl(t)
        if t == zero or t == one:
            return pt
        else:
            return pt.on_rhs(thy, rewr_conv("nat_of_nat_def", sym=self.sym))

def nat_eval(t):
    if is_binary_nat(t):
        return from_binary_nat(t)
    elif t.is_comb():
        if t.head == Suc:
            return nat_eval(t.arg) + 1
        elif t.head == plus:
            return nat_eval(t.arg1) + nat_eval(t.arg)
        elif t.head == minus:
            m, n = nat_eval(t.arg1), nat_eval(t.arg)
            if m <= n:
                return 0
            else:
                return m - n
        elif t.head == times:
            return nat_eval(t.arg1) * nat_eval(t.arg)
        else:
            raise ConvException('nat_eval: %s' % str(t))
    else:
        raise ConvException('nat_eval: %s' % str(t))

class nat_conv(Conv):
    """Simplify all arithmetic operations."""
    def eval(self, thy, t):
        return Thm.mk_equals(t, to_binary_nat(nat_eval(t)))

    def get_proof_term(self, thy, t):
        pt = refl(t)
        if is_binary_nat(t):
            return pt
        else:
            if t.head == Suc:
                return pt.on_rhs(thy, arg_conv(self),
                                 arg_conv(rewr_of_nat_conv()),
                                 Suc_conv(),
                                 rewr_of_nat_conv(sym=True))
            elif t.head == plus:
                return pt.on_rhs(thy, binop_conv(self),
                                 binop_conv(rewr_of_nat_conv()),
                                 add_conv(),
                                 rewr_of_nat_conv(sym=True))
            elif t.head == times:
                return pt.on_rhs(thy, binop_conv(self),
                                 binop_conv(rewr_of_nat_conv()),
                                 mult_conv(),
                                 rewr_of_nat_conv(sym=True))
            else:
                raise ConvException("nat_conv")

# Conversion using a macro
class nat_eval_macro(ProofMacro):
    """Simplify all arithmetic operations."""
    def __init__(self):
        self.level = 0  # No expand implemented
        self.sig = Term
        self.limit = None

    def eval(self, thy, goal, prevs):
        assert len(prevs) == 0, "nat_eval_macro: no conditions expected"
        assert goal.is_equals(), "nat_eval_macro: goal must be an equality"
        assert nat_eval(goal.lhs) == nat_eval(goal.rhs), "nat_eval_macro: two sides are not equal"

        return Thm([], goal)

class nat_eval_conv(Conv):
    """Simplify all arithmetic operations."""
    def get_proof_term(self, thy, t):
        simp_t = to_binary_nat(nat_eval(t))
        if simp_t == t:
            return refl(t)
        return ProofTermDeriv('nat_eval', thy, Term.mk_equals(t, simp_t))

auto.add_global_autos_norm(minus, nat_eval_conv())

# Normalization on the semiring.

# First level normalization: AC rules for addition only.

def compare_atom(t1, t2):
    """Compare two atoms, placing numbers last."""
    if is_binary_nat(t1) and is_binary_nat(t2):
        return term_ord.EQUAL
    elif is_binary_nat(t1):
        return term_ord.GREATER
    elif is_binary_nat(t2):
        return term_ord.LESS
    else:
        return term_ord.fast_compare(t1, t2)

class swap_add_r(Conv):
    """Rewrite (a + b) + c to (a + c) + b, or if the left argument
    is an atom, rewrite a + b to b + a.

    """
    def get_proof_term(self, thy, t):
        pt = refl(t)
        if is_plus(t.arg1):
            return pt.on_rhs(thy, rewr_conv("add_assoc"),
                             arg_conv(rewr_conv("add_comm")),
                             rewr_conv("add_assoc", sym=True))
        else:
            return pt.on_rhs(thy, rewr_conv("add_comm"))

class norm_add_atom_1(Conv):
    """Normalize expression of the form (a_1 + ... + a_n) + a."""
    def get_proof_term(self, thy, t):
        pt = refl(t)
        if t.arg1 == zero:
            return pt.on_rhs(thy, rewr_conv("nat_plus_def_1"))
        elif t.arg == zero:
            return pt.on_rhs(thy, rewr_conv("add_0_right"))
        elif is_plus(t.arg1):
            if compare_atom(t.arg1.arg, t.arg) == term_ord.GREATER:
                return pt.on_rhs(thy, swap_add_r(), arg1_conv(norm_add_atom_1()))
            else:
                return pt
        else:
            if compare_atom(t.arg1, t.arg) == term_ord.GREATER:
                return pt.on_rhs(thy, rewr_conv("add_comm"))
            else:
                return pt

class norm_add_1(Conv):
    """Normalize expression of the form (a_1 + ... + a_n) + (b_1 + ... + b_n)."""
    def get_proof_term(self, thy, t):
        pt = refl(t)
        if is_plus(t.arg):
            return pt.on_rhs(thy, rewr_conv("add_assoc", sym=True),
                             arg1_conv(norm_add_1()),
                             norm_add_atom_1())
        else:
            return pt.on_rhs(thy, norm_add_atom_1())

# Second level normalization.

class swap_times_r(Conv):
    """Rewrite (a * b) * c to (a * c) * b, or if the left argument
    is an atom, rewrite a * b to b * a.

    """
    def get_proof_term(self, thy, t):
        pt = refl(t)
        if is_times(t.arg1):
            return pt.on_rhs(thy, rewr_conv("mult_assoc"),
                             arg_conv(rewr_conv("mult_comm")),
                             rewr_conv("mult_assoc", sym=True))
        else:
            return pt.on_rhs(thy, rewr_conv("mult_comm"))

def has_binary_thms(thy):
    return thy.has_theorem('bit1_bit1_mult')

class norm_mult_atom(Conv):
    """Normalize expression of the form (a_1 * ... * a_n) * a."""
    def get_proof_term(self, thy, t):
        pt = refl(t)
        if t.arg1 == zero:
            return pt.on_rhs(thy, rewr_conv("nat_times_def_1"))
        elif t.arg == zero:
            return pt.on_rhs(thy, rewr_conv("mult_0_right"))
        elif t.arg1 == one:
            return pt.on_rhs(thy, rewr_conv("mult_1_left"))
        elif t.arg == one:
            return pt.on_rhs(thy, rewr_conv("mult_1_right"))
        elif is_times(t.arg1):
            cmp = compare_atom(t.arg1.arg, t.arg)
            if cmp == term_ord.GREATER:
                return pt.on_rhs(thy, swap_times_r(), arg1_conv(norm_mult_atom()))
            elif cmp == term_ord.EQUAL:
                if is_binary_nat(t.arg) and has_binary_thms(thy):
                    return pt.on_rhs(thy, rewr_conv("mult_assoc"), arg_conv(nat_conv()))
                else:
                    return pt
            else:
                return pt
        else:
            cmp = compare_atom(t.arg1, t.arg)
            if cmp == term_ord.GREATER:
                return pt.on_rhs(thy, rewr_conv("mult_comm"))
            elif cmp == term_ord.EQUAL:
                if is_binary_nat(t.arg) and has_binary_thms(thy):
                    return pt.on_rhs(thy, nat_conv())
                else:
                    return pt
            else:
                return pt

class norm_mult_monomial(Conv):
    """Normalize expression of the form (a_1 * ... * a_n) * (b_1 * ... * b_n)."""
    def get_proof_term(self, thy, t):
        if is_times(t.arg):
            return every_conv(
                rewr_conv("mult_assoc", sym=True),
                arg1_conv(norm_mult_monomial()),
                norm_mult_atom()
            ).get_proof_term(thy, t)
        else:
            return norm_mult_atom().get_proof_term(thy, t)

def dest_monomial(t):
    """Remove coefficient part of a monomial t."""
    if is_times(t) and is_binary_nat(t.arg):
        return t.arg1
    elif is_binary_nat(t):
        return one
    else:
        return t

def compare_monomial(thy, t1, t2):
    """Compare two monomials by their body."""
    if has_binary_thms(thy):
        return term_ord.fast_compare(dest_monomial(t1), dest_monomial(t2))
    else:
        return term_ord.fast_compare(t1, t2)

class to_coeff_form(Conv):
    """Convert a to a * 1, n to 1 * n, and leave a * n unchanged."""
    def get_proof_term(self, thy, t):
        if is_times(t) and is_binary_nat(t.arg):
            return all_conv().get_proof_term(thy, t)
        elif is_binary_nat(t):
            return rewr_conv("mult_1_left", sym=True).get_proof_term(thy, t)
        else:
            return rewr_conv("mult_1_right", sym=True).get_proof_term(thy, t)

class from_coeff_form(Conv):
    """Convert a * 1 to a, 1 * n to n, and leave a * n unchanged."""
    def get_proof_term(self, thy, t):
        if t.arg == one:
            return rewr_conv("mult_1_right").get_proof_term(thy, t)
        elif t.arg1 == one:
            return rewr_conv("mult_1_left").get_proof_term(thy, t)
        else:
            return all_conv().get_proof_term(thy, t)

def combine_monomial(thy):
    """Combine two monomials with the same body."""
    return every_conv(
        binop_conv(to_coeff_form()),
        rewr_conv("distrib_l", sym=True),
        arg_conv(nat_conv()),
        from_coeff_form()
    )

class norm_add_monomial(Conv):
    """Normalize expression of the form (a_1 + ... + a_n) + a."""
    def get_proof_term(self, thy, t):
        pt = refl(t)
        if t.arg1 == zero:
            return pt.on_rhs(thy, rewr_conv("nat_plus_def_1"))
        elif t.arg == zero:
            return pt.on_rhs(thy, rewr_conv("add_0_right"))
        elif is_plus(t.arg1):
            cmp = compare_monomial(thy, t.arg1.arg, t.arg)
            if cmp == term_ord.GREATER:
                return pt.on_rhs(thy, swap_add_r(), arg1_conv(norm_add_monomial()))
            elif cmp == term_ord.EQUAL and has_binary_thms(thy):
                return pt.on_rhs(thy, rewr_conv("add_assoc"), arg_conv(combine_monomial(thy)))
            else:
                return pt
        else:
            cmp = compare_monomial(thy, t.arg1, t.arg)
            if cmp == term_ord.GREATER:
                return pt.on_rhs(thy, rewr_conv("add_comm"))
            elif cmp == term_ord.EQUAL and has_binary_thms(thy):
                return pt.on_rhs(thy, combine_monomial(thy))
            else:
                return pt

class norm_add_polynomial(Conv):
    """Normalize expression of the form (a_1 + ... + a_n) + (b_1 + ... + b_n)."""
    def get_proof_term(self, thy, t):
        pt = refl(t)
        if is_plus(t.arg):
            return pt.on_rhs(thy, rewr_conv("add_assoc", sym=True),
                             arg1_conv(norm_add_polynomial()),
                             norm_add_monomial())
        else:
            return pt.on_rhs(thy, norm_add_monomial())

class norm_mult_poly_monomial(Conv):
    """Normalize expression of the form (a_1 + ... + a_n) * b."""
    def get_proof_term(self, thy, t):
        pt = refl(t)
        if is_plus(t.arg1):
            return pt.on_rhs(thy, rewr_conv("distrib_r"),
                             arg1_conv(norm_mult_poly_monomial()),
                             arg_conv(norm_mult_monomial()),
                             norm_add_polynomial())
        else:
            return pt.on_rhs(thy, norm_mult_monomial())

class norm_mult_polynomial(Conv):
    """Normalize expression of the form (a_1 + ... + a_n) * (b_1 + ... + b_n)."""
    def get_proof_term(self, thy, t):
        pt = refl(t)
        if is_plus(t.arg):
            return pt.on_rhs(thy, rewr_conv("distrib_l"),
                             arg1_conv(norm_mult_polynomial()),
                             arg_conv(norm_mult_poly_monomial()),
                             norm_add_polynomial())
        else:
            return pt.on_rhs(thy, norm_mult_poly_monomial())

class norm_full(Conv):
    """Normalize expressions on natural numbers involving plus and times."""
    def get_proof_term(self, thy, t):
        pt = refl(t)
        if thy.has_theorem('mult_comm'):
            # Full conversion, with or without binary numbers
            if is_binary_nat(t):
                return pt
            elif is_Suc(t):
                return pt.on_rhs(thy, rewr_conv("add_1_right", sym=True), norm_full())
            elif is_plus(t):
                return pt.on_rhs(thy, binop_conv(norm_full()), norm_add_polynomial())
            elif is_times(t):
                return pt.on_rhs(thy, binop_conv(norm_full()), norm_mult_polynomial())
            else:
                return pt
        elif thy.has_theorem('add_assoc'):
            # Conversion using only AC rules for addition
            if is_binary_nat(t):
                return pt
            elif is_Suc(t):
                return pt.on_rhs(thy, rewr_conv("add_1_right", sym=True), norm_full())
            elif is_plus(t):
                return pt.on_rhs(thy, binop_conv(norm_full()), norm_add_1())
            else:
                return pt
        else:
            return pt


class nat_norm_macro(ProofTermMacro):
    """Attempt to prove goal by normalization."""

    def __init__(self):
        self.level = 10
        self.sig = Term
        self.limit = 'nat_nat_power_def_1'

    def eval(self, thy, goal, pts):
        # Simply produce the goal.
        assert len(pts) == 0, "nat_norm_macro"
        return Thm([], goal)

    def can_eval(self, thy, goal):
        assert isinstance(goal, Term), "nat_norm_macro"
        if not (goal.is_equals() and goal.lhs.get_type() == natT):
            return False

        t1, t2 = goal.args
        pt1 = norm_full().get_proof_term(thy, t1)
        pt2 = norm_full().get_proof_term(thy, t2)
        return pt1.prop.rhs == pt2.prop.rhs

    def get_proof_term(self, thy, goal, pts):
        assert len(pts) == 0, "nat_norm_macro"
        assert goal.is_equals(), "nat_norm_macro: goal is not an equality."

        t1, t2 = goal.args
        pt1 = norm_full().get_proof_term(thy, t1)
        pt2 = norm_full().get_proof_term(thy, t2)
        assert pt1.prop.rhs == pt2.prop.rhs, "nat_norm_macro: normalization is not equal."

        return ProofTerm.transitive(pt1, ProofTerm.symmetric(pt2))

class nat_norm_method(Method):
    """Apply nat_norm macro."""
    def __init__(self):
        self.sig = []
        self.limit = 'nat_nat_power_def_1'

    def search(self, state, id, prevs, data=None):
        if data:
            return [data]

        if len(prevs) != 0:
            return []

        cur_th = state.get_proof_item(id).th
        if nat_norm_macro().can_eval(state.thy, cur_th.prop):
            return [{}]
        else:
            return []

    @settings.with_settings
    def display_step(self, state, data):
        return pprint.N("nat_norm: (solves)")

    def apply(self, state, id, data, prevs):
        assert len(prevs) == 0, "nat_norm_method"
        state.apply_tactic(id, MacroTactic('nat_norm'))


def ineq_zero_proof_term(thy, n):
    """Returns the inequality n ~= 0."""
    assert n != 0, "ineq_zero_proof_term: n = 0"
    if n == 1:
        return ProofTerm.theorem(thy, "one_nonzero")
    elif n % 2 == 0:
        return apply_theorem(thy, "bit0_nonzero", ineq_zero_proof_term(thy, n // 2))
    else:
        return apply_theorem(thy, "bit1_nonzero", inst={"m": to_binary(n // 2)})

def ineq_one_proof_term(thy, n):
    """Returns the inequality n ~= 1."""
    assert n != 1, "ineq_one_proof_term: n = 1"
    if n == 0:
        return apply_theorem(thy, "ineq_sym", ProofTerm.theorem(thy, "one_nonzero"))
    elif n % 2 == 0:
        return apply_theorem(thy, "bit0_neq_one", inst={"m": to_binary(n // 2)})
    else:
        return apply_theorem(thy, "bit1_neq_one", ineq_zero_proof_term(thy, n // 2))

def ineq_proof_term(thy, m, n):
    """Returns the inequality m ~= n."""
    assert m != n, "ineq_proof_term: m = n"
    if n == 0:
        return ineq_zero_proof_term(thy, m)
    elif n == 1:
        return ineq_one_proof_term(thy, m)
    elif m == 0:
        return apply_theorem(thy, "ineq_sym", ineq_zero_proof_term(thy, n))
    elif m == 1:
        return apply_theorem(thy, "ineq_sym", ineq_one_proof_term(thy, n))
    elif m % 2 == 0 and n % 2 == 0:
        return apply_theorem(thy, "bit0_neq", ineq_proof_term(thy, m // 2, n // 2))
    elif m % 2 == 1 and n % 2 == 1:
        return apply_theorem(thy, "bit1_neq", ineq_proof_term(thy, m // 2, n // 2))
    elif m % 2 == 0 and n % 2 == 1:
        return apply_theorem(thy, "bit0_bit1_neq", inst={"m": to_binary(m // 2), "n": to_binary(n // 2)})
    else:
        return apply_theorem(thy, "ineq_sym", ineq_proof_term(thy, n, m))

class nat_const_ineq_macro(ProofTermMacro):
    """Given m and n, with m ~= n, return the inequality theorem."""

    def __init__(self):
        self.level = 10
        self.sig = Term
        self.limit = 'bit1_neq_one'

    def can_eval(self, thy, goal):
        assert isinstance(goal, Term), "nat_const_ineq_macro"
        if not (logic.is_neg(goal) and goal.arg.is_equals()):
            return False

        m, n = goal.arg.args
        return is_binary_nat(m) and is_binary_nat(n) and from_binary_nat(m) != from_binary_nat(n)

    def eval(self, thy, goal, pts):
        assert len(pts) == 0 and self.can_eval(thy, goal), "nat_const_ineq_macro"

        # Simply produce the goal.
        return Thm([], goal)

    def get_proof_term(self, thy, goal, pts):
        assert len(pts) == 0 and self.can_eval(thy, goal), "nat_const_ineq_macro"

        m, n = goal.arg.args
        pt = ineq_proof_term(thy, from_binary_nat(m), from_binary_nat(n))
        return pt.on_prop(thy, arg_conv(binop_conv(rewr_of_nat_conv(sym=True))))

def nat_const_ineq(thy, a, b):
    goal = logic.neg(Term.mk_equals(a, b))
    return ProofTermDeriv("nat_const_ineq", thy, goal, [])


class nat_const_ineq_method(Method):
    """Apply nat_const_ineq macro."""
    def __init__(self):
        self.sig = []
        self.limit = 'bit1_neq_one'

    def search(self, state, id, prevs, data=None):
        if data:
            return [data]

        if len(prevs) != 0:
            return []

        cur_th = state.get_proof_item(id).th
        if nat_const_ineq_macro().can_eval(state.thy, cur_th.prop):
            return [{}]
        else:
            return []

    @settings.with_settings
    def display_step(self, state, data):
        return pprint.N("nat_const_ineq: (solves)")

    def apply(self, state, id, data, prevs):
        assert len(prevs) == 0, "nat_const_ineq_method"
        state.apply_tactic(id, MacroTactic('nat_const_ineq'))

class nat_const_less_eq_macro(ProofTermMacro):
    """Given m and n, with m <= n, return the less-equal theorem."""
    def __init__(self):
        self.level = 10
        self.sig = Term
        self.limit = 'bit1_neq_one'

    def can_eval(self, thy, goal):
        assert isinstance(goal, Term), "nat_const_less_eq_macro"
        if not is_less_eq(goal):
            return False

        m, n = goal.args
        return is_binary_nat(m) and is_binary_nat(n) and from_binary_nat(m) <= from_binary_nat(n)

    def eval(self, thy, goal, pts):
        assert len(pts) == 0 and self.can_eval(thy, goal), "nat_const_less_eq_macro"

        # Simply produce the goal.
        return Thm([], goal)

    def get_proof_term(self, thy, goal, pts):
        assert len(pts) == 0 and self.can_eval(thy, goal), "nat_const_less_eq_macro"

        m, n = goal.args
        assert from_binary_nat(m) <= from_binary_nat(n)
        p = to_binary_nat(from_binary_nat(n) - from_binary_nat(m))
        eq = ProofTerm.symmetric(norm_full().get_proof_term(thy, plus(m, p)))
        goal2 = rewr_conv('less_eq_exist').eval(thy, goal).prop.rhs
        ex_eq = apply_theorem(thy, 'exI', eq, concl=goal2)
        return ex_eq.on_prop(thy, rewr_conv('less_eq_exist', sym=True))

def nat_less_eq(thy, t1, t2):
    return ProofTermDeriv("nat_const_less_eq", thy, less_eq(t1, t2))

class nat_const_less_macro(ProofTermMacro):
    """Given m and n, with m < n, return the less-than theorem."""
    def __init__(self):
        self.level = 10
        self.sig = Term
        self.limit = 'bit1_neq_one'

    def get_proof_term(self, thy, goal, pts):
        assert isinstance(goal, Term)
        assert len(pts) == 0, "nat_const_less_macro"
        m, n = goal.args
        assert from_binary_nat(m) < from_binary_nat(n)
        less_eq_goal = less_eq(m, n)
        less_eq_pt = nat_const_less_eq_macro().get_proof_term(thy, less_eq_goal, [])
        ineq_goal = logic.neg(Term.mk_equals(m, n))
        ineq_pt = nat_const_ineq_macro().get_proof_term(thy, ineq_goal, [])
        return apply_theorem(thy, "less_lesseqI", less_eq_pt, ineq_pt)

def nat_less(thy, t1, t2):
    return ProofTermDeriv("nat_const_less", thy, less(t1, t2))

class nat_eq_conv(Conv):
    """Simplify equality a = b to either True or False."""
    def get_proof_term(self, thy, t):
        if not t.is_equals():
            return refl(t)

        a, b = t.args
        if not (is_binary_nat(a) and is_binary_nat(b)):
            return refl(t)

        if a == b:
            return refl(a).on_prop(thy, rewr_conv("eq_true"))
        else:
            return nat_const_ineq(thy, a, b).on_prop(thy, rewr_conv("eq_false"))


macro.global_macros.update({
    "nat_eval": nat_eval_macro(),
    "nat_norm": nat_norm_macro(),
    "nat_const_ineq": nat_const_ineq_macro(),
    "nat_const_less_eq": nat_const_less_eq_macro(),
    "nat_const_less": nat_const_less_macro(),
})

global_methods.update({
    "nat_norm": nat_norm_method(),
    "nat_const_ineq": nat_const_ineq_method(),
})