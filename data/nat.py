# Author: Bohua Zhan

from kernel.type import TFun, BoolType, NatType
from kernel import term
from kernel.term import Term, Const, Not, Eq, Binary, Nat, Inst
from kernel.thm import Thm
from kernel import theory
from kernel.theory import register_macro
from kernel.macro import Macro
from kernel import term_ord
from logic.conv import Conv, ConvException, all_conv, rewr_conv, \
    then_conv, arg_conv, arg1_conv, binop_conv
from kernel.proofterm import ProofTerm, refl
from logic import auto
from logic.logic import apply_theorem
from logic import logic
from logic.tactic import MacroTactic
from server.method import Method, register_method
from syntax import pprint, settings
from util import poly


"""Utility functions for natural number arithmetic."""

# Basic definitions

zero = term.nat_zero
one = term.nat_one
plus = term.plus(NatType)
minus = term.minus(NatType)
times = term.times(NatType)
equals = term.equals(NatType)
less_eq = term.less_eq(NatType)
less = term.less(NatType)
greater_eq = term.greater_eq(NatType)
greater = term.greater(NatType)

Suc = Const("Suc", TFun(NatType, NatType))
Pre = Const("Pre", TFun(NatType, NatType))

# Arithmetic on binary numbers

def convert_to_poly(t):
    """Convert natural number expression to polynomial."""
    if t.is_var():
        return poly.singleton(t)
    elif t.is_number():
        return poly.constant(t.dest_number())
    elif t.is_plus():
        t1, t2 = t.args
        return convert_to_poly(t1) + convert_to_poly(t2)
    elif t.is_times():
        t1, t2 = t.args
        return convert_to_poly(t1) * convert_to_poly(t2)
    elif t.is_minus():
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

def is_bit0(t):
    return t.is_comb('bit0', 1)

def is_bit1(t):
    return t.is_comb('bit1', 1)

class Suc_conv(Conv):
    """Computes Suc of a binary number."""
    def eval(self, t):
        return Thm([], Eq(t, Binary(t.arg.dest_binary() + 1)))

    def get_proof_term(self, t):
        pt = refl(t)
        if t.arg.is_zero():
            return pt.on_rhs(rewr_conv("nat_one_def", sym=True))
        elif t.arg.is_one():
            return pt.on_rhs(rewr_conv("one_Suc"))
        elif is_bit0(t.arg):
            return pt.on_rhs(rewr_conv("bit0_Suc"))
        else:
            return pt.on_rhs(rewr_conv("bit1_Suc"), arg_conv(self))

class add_conv(Conv):
    """Computes the sum of two binary numbers."""
    def eval(self, t):
        return Thm([], Eq(t, Binary(t.arg1.dest_binary() + t.arg.dest_binary())))

    def get_proof_term(self, t):
        if not (t.is_plus() and t.arg1.is_binary() and t.arg.is_binary()):
            raise ConvException("add_conv")
        pt = refl(t)
        n1, n2 = t.arg1, t.arg  # two summands
        if n1.is_zero():
            return pt.on_rhs(rewr_conv("nat_plus_def_1"))
        elif n2.is_zero():
            return pt.on_rhs(rewr_conv("add_0_right"))
        elif n1.is_one():
            return pt.on_rhs(rewr_conv("add_1_left"), Suc_conv())
        elif n2.is_one():
            return pt.on_rhs(rewr_conv("add_1_right"), Suc_conv())
        elif is_bit0(n1) and is_bit0(n2):
            return pt.on_rhs(rewr_conv("bit0_bit0_add"), arg_conv(self))
        elif is_bit0(n1) and is_bit1(n2):
            return pt.on_rhs(rewr_conv("bit0_bit1_add"), arg_conv(self))
        elif is_bit1(n1) and is_bit0(n2):
            return pt.on_rhs(rewr_conv("bit1_bit0_add"), arg_conv(self))
        else:
            return pt.on_rhs(rewr_conv("bit1_bit1_add"),
                             arg_conv(arg_conv(self)), arg_conv(Suc_conv()))

class mult_conv(Conv):
    """Computes the product of two binary numbers."""
    def eval(self, t):
        return Thm([], Eq(t, Binary(t.arg1.dest_binary() * t.arg.dest_binary())))

    def get_proof_term(self, t):
        n1, n2 = t.arg1, t.arg  # two summands
        pt = refl(t)
        if n1.is_zero():
            return pt.on_rhs(rewr_conv("nat_times_def_1"))
        elif n2.is_zero():
            return pt.on_rhs(rewr_conv("mult_0_right"))
        elif n1.is_one():
            return pt.on_rhs(rewr_conv("mult_1_left"))
        elif n2.is_one():
            return pt.on_rhs(rewr_conv("mult_1_right"))
        elif is_bit0(n1) and is_bit0(n2):
            return pt.on_rhs(rewr_conv("bit0_bit0_mult"), arg_conv(arg_conv(self)))
        elif is_bit0(n1) and is_bit1(n2):
            return pt.on_rhs(rewr_conv("bit0_bit1_mult"), arg_conv(self))
        elif is_bit1(n1) and is_bit0(n2):
            return pt.on_rhs(rewr_conv("bit1_bit0_mult"), arg_conv(self))
        else:
            return pt.on_rhs(rewr_conv("bit1_bit1_mult"),
                             arg_conv(arg1_conv(add_conv())),
                             arg_conv(arg_conv(arg_conv(self))),
                             arg_conv(add_conv()))

class rewr_of_nat_conv(Conv):
    """Remove or apply of_nat."""
    def __init__(self, *, sym=False):
        self.sym = sym

    def get_proof_term(self, t):
        pt = refl(t)
        if t.is_zero() or t.is_one():
            return pt
        else:
            return pt.on_rhs(rewr_conv("nat_of_nat_def", sym=self.sym))

def nat_eval(t):
    """Evaluate a term with arithmetic operations.
    
    Return a Python integer.
    
    """
    if t.is_number():
        return t.dest_number()
    elif t.is_comb('Suc', 1):
        return nat_eval(t.arg) + 1
    elif t.is_plus():
        return nat_eval(t.arg1) + nat_eval(t.arg)
    elif t.is_minus():
        m, n = nat_eval(t.arg1), nat_eval(t.arg)
        return 0 if m <= n else m - n
    elif t.is_times():
        return nat_eval(t.arg1) * nat_eval(t.arg)
    else:
        raise ConvException('nat_eval: %s' % str(t))

class nat_conv(Conv):
    """Simplify all arithmetic operations."""
    def eval(self, t):
        return Thm([], Eq(t, Nat(nat_eval(t))))

    def get_proof_term(self, t):
        pt = refl(t)
        if t.is_number():
            return pt
        elif t.is_comb('Suc', 1):
            return pt.on_rhs(arg_conv(self),
                             arg_conv(rewr_of_nat_conv()),
                             Suc_conv(),
                             rewr_of_nat_conv(sym=True))
        elif t.is_plus():
            return pt.on_rhs(binop_conv(self),
                             binop_conv(rewr_of_nat_conv()),
                             add_conv(),
                             rewr_of_nat_conv(sym=True))
        elif t.is_times():
            return pt.on_rhs(binop_conv(self),
                             binop_conv(rewr_of_nat_conv()),
                             mult_conv(),
                             rewr_of_nat_conv(sym=True))
        else:
            raise ConvException("nat_conv")

# Conversion using a macro
@register_macro('nat_eval')
class nat_eval_macro(Macro):
    """Simplify all arithmetic operations."""
    def __init__(self):
        self.level = 0  # No expand implemented
        self.sig = Term
        self.limit = None

    def eval(self, goal, prevs):
        assert len(prevs) == 0, "nat_eval_macro: no conditions expected"
        assert goal.is_equals(), "nat_eval_macro: goal must be an equality"
        assert nat_eval(goal.lhs) == nat_eval(goal.rhs), "nat_eval_macro: two sides are not equal"

        return Thm([], goal)

class nat_eval_conv(Conv):
    """Simplify all arithmetic operations."""
    def get_proof_term(self, t):
        simp_t = Nat(nat_eval(t))
        if simp_t == t:
            return refl(t)
        return ProofTerm('nat_eval', Eq(t, simp_t))

auto.add_global_autos_norm(plus, nat_eval_conv())
auto.add_global_autos_norm(minus, nat_eval_conv())
auto.add_global_autos_norm(times, nat_eval_conv())

# Normalization on the semiring.

# First level normalization: AC rules for addition only.

def compare_atom(t1, t2):
    """Compare two atoms, placing numbers last."""
    if t1.is_number() and t2.is_number():
        return 0
    elif t1.is_number():
        return 1
    elif t2.is_number():
        return -1
    else:
        return term_ord.fast_compare(t1, t2)

class swap_add_r(Conv):
    """Rewrite (a + b) + c to (a + c) + b, or if the left argument
    is an atom, rewrite a + b to b + a.

    """
    def get_proof_term(self, t):
        pt = refl(t)
        if t.arg1.is_plus():
            return pt.on_rhs(rewr_conv("add_assoc"),
                             arg_conv(rewr_conv("add_comm")),
                             rewr_conv("add_assoc", sym=True))
        else:
            return pt.on_rhs(rewr_conv("add_comm"))

class norm_add_atom_1(Conv):
    """Normalize expression of the form (a_1 + ... + a_n) + a."""
    def get_proof_term(self, t):
        pt = refl(t)
        if t.arg1.is_zero():
            return pt.on_rhs(rewr_conv("nat_plus_def_1"))
        elif t.arg.is_zero():
            return pt.on_rhs(rewr_conv("add_0_right"))
        elif t.arg1.is_plus():
            if compare_atom(t.arg1.arg, t.arg) > 0:
                return pt.on_rhs(swap_add_r(), arg1_conv(norm_add_atom_1()))
            else:
                return pt
        else:
            if compare_atom(t.arg1, t.arg) > 0:
                return pt.on_rhs(rewr_conv("add_comm"))
            else:
                return pt

class norm_add_1(Conv):
    """Normalize expression of the form (a_1 + ... + a_n) + (b_1 + ... + b_n)."""
    def get_proof_term(self, t):
        pt = refl(t)
        if t.arg.is_plus():
            return pt.on_rhs(rewr_conv("add_assoc", sym=True),
                             arg1_conv(norm_add_1()),
                             norm_add_atom_1())
        else:
            return pt.on_rhs(norm_add_atom_1())

# Second level normalization.

class swap_times_r(Conv):
    """Rewrite (a * b) * c to (a * c) * b, or if the left argument
    is an atom, rewrite a * b to b * a.

    """
    def get_proof_term(self, t):
        pt = refl(t)
        if t.arg1.is_times():
            return pt.on_rhs(rewr_conv("mult_assoc"),
                             arg_conv(rewr_conv("mult_comm")),
                             rewr_conv("mult_assoc", sym=True))
        else:
            return pt.on_rhs(rewr_conv("mult_comm"))

def has_binary_thms():
    return theory.thy.has_theorem('bit1_bit1_mult')

class norm_mult_atom(Conv):
    """Normalize expression of the form (a_1 * ... * a_n) * a."""
    def get_proof_term(self, t):
        pt = refl(t)
        if t.arg1.is_zero():
            return pt.on_rhs(rewr_conv("nat_times_def_1"))
        elif t.arg.is_zero():
            return pt.on_rhs(rewr_conv("mult_0_right"))
        elif t.arg1.is_one():
            return pt.on_rhs(rewr_conv("mult_1_left"))
        elif t.arg.is_one():
            return pt.on_rhs(rewr_conv("mult_1_right"))
        elif t.arg1.is_times():
            cp = compare_atom(t.arg1.arg, t.arg)
            if cp > 0:
                return pt.on_rhs(swap_times_r(), arg1_conv(norm_mult_atom()))
            elif cp == 0:
                if t.arg.is_number() and has_binary_thms():
                    return pt.on_rhs(rewr_conv("mult_assoc"), arg_conv(nat_conv()))
                else:
                    return pt
            else:
                return pt
        else:
            cp = compare_atom(t.arg1, t.arg)
            if cp > 0:
                return pt.on_rhs(rewr_conv("mult_comm"))
            elif cp == 0:
                if t.arg.is_number() and has_binary_thms():
                    return pt.on_rhs(nat_conv())
                else:
                    return pt
            else:
                return pt

class norm_mult_monomial(Conv):
    """Normalize expression of the form (a_1 * ... * a_n) * (b_1 * ... * b_n)."""
    def get_proof_term(self, t):
        pt = refl(t)
        if t.arg.is_times():
            return pt.on_rhs(rewr_conv("mult_assoc", sym=True),
                             arg1_conv(norm_mult_monomial()),
                             norm_mult_atom())
        else:
            return pt.on_rhs(norm_mult_atom())

def dest_monomial(t):
    """Remove coefficient part of a monomial t."""
    if t.is_times() and t.arg.is_number():
        return t.arg1
    elif t.is_number():
        return one
    else:
        return t

def compare_monomial(t1, t2):
    """Compare two monomials by their body."""
    if has_binary_thms():
        return term_ord.fast_compare(dest_monomial(t1), dest_monomial(t2))
    else:
        return term_ord.fast_compare(t1, t2)

class to_coeff_form(Conv):
    """Convert a to a * 1, n to 1 * n, and leave a * n unchanged."""
    def get_proof_term(self, t):
        pt = refl(t)
        if t.is_times() and t.arg.is_number():
            return pt
        elif t.is_number():
            return pt.on_rhs(rewr_conv("mult_1_left", sym=True))
        else:
            return pt.on_rhs(rewr_conv("mult_1_right", sym=True))

class from_coeff_form(Conv):
    """Convert a * 1 to a, 1 * n to n, and leave a * n unchanged."""
    def get_proof_term(self, t):
        pt = refl(t)
        if t.arg.is_one():
            return pt.on_rhs(rewr_conv("mult_1_right"))
        elif t.arg1.is_one():
            return pt.on_rhs(rewr_conv("mult_1_left"))
        else:
            return pt

class combine_monomial(Conv):
    """Combine two monomials with the same body."""
    def get_proof_term(self, t):
        return refl(t).on_rhs(
            binop_conv(to_coeff_form()),
            rewr_conv("distrib_l", sym=True),
            arg_conv(nat_conv()),
            from_coeff_form())

class norm_add_monomial(Conv):
    """Normalize expression of the form (a_1 + ... + a_n) + a."""
    def get_proof_term(self, t):
        pt = refl(t)
        if t.arg1.is_zero():
            return pt.on_rhs(rewr_conv("nat_plus_def_1"))
        elif t.arg.is_zero():
            return pt.on_rhs(rewr_conv("add_0_right"))
        elif t.arg1.is_plus():
            cp = compare_monomial(t.arg1.arg, t.arg)
            if cp > 0:
                return pt.on_rhs(swap_add_r(), arg1_conv(norm_add_monomial()))
            elif cp == 0 and has_binary_thms():
                return pt.on_rhs(rewr_conv("add_assoc"), arg_conv(combine_monomial()))
            else:
                return pt
        else:
            cp = compare_monomial(t.arg1, t.arg)
            if cp > 0:
                return pt.on_rhs(rewr_conv("add_comm"))
            elif cp == 0 and has_binary_thms():
                return pt.on_rhs(combine_monomial())
            else:
                return pt

class norm_add_polynomial(Conv):
    """Normalize expression of the form (a_1 + ... + a_n) + (b_1 + ... + b_n)."""
    def get_proof_term(self, t):
        pt = refl(t)
        if t.arg.is_plus():
            return pt.on_rhs(rewr_conv("add_assoc", sym=True),
                             arg1_conv(norm_add_polynomial()),
                             norm_add_monomial())
        else:
            return pt.on_rhs(norm_add_monomial())

class norm_mult_poly_monomial(Conv):
    """Normalize expression of the form (a_1 + ... + a_n) * b."""
    def get_proof_term(self, t):
        pt = refl(t)
        if t.arg1.is_plus():
            return pt.on_rhs(rewr_conv("distrib_r"),
                             arg1_conv(norm_mult_poly_monomial()),
                             arg_conv(norm_mult_monomial()),
                             norm_add_polynomial())
        else:
            return pt.on_rhs(norm_mult_monomial())

class norm_mult_polynomial(Conv):
    """Normalize expression of the form (a_1 + ... + a_n) * (b_1 + ... + b_n)."""
    def get_proof_term(self, t):
        pt = refl(t)
        if t.arg.is_plus():
            return pt.on_rhs(rewr_conv("distrib_l"),
                             arg1_conv(norm_mult_polynomial()),
                             arg_conv(norm_mult_poly_monomial()),
                             norm_add_polynomial())
        else:
            return pt.on_rhs(norm_mult_poly_monomial())

class norm_full(Conv):
    """Normalize expressions on natural numbers involving plus and times."""
    def get_proof_term(self, t):
        pt = refl(t)
        if theory.thy.has_theorem('mult_comm'):
            # Full conversion, with or without binary numbers
            if t.is_number():
                return pt
            elif t.is_comb('Suc', 1):
                return pt.on_rhs(rewr_conv("add_1_right", sym=True), norm_full())
            elif t.is_plus():
                return pt.on_rhs(binop_conv(norm_full()), norm_add_polynomial())
            elif t.is_times():
                return pt.on_rhs(binop_conv(norm_full()), norm_mult_polynomial())
            else:
                return pt
        elif theory.thy.has_theorem('add_assoc'):
            # Conversion using only AC rules for addition
            if t.is_number():
                return pt
            elif t.is_comb('Suc', 1):
                return pt.on_rhs(rewr_conv("add_1_right", sym=True), norm_full())
            elif t.is_plus():
                return pt.on_rhs(binop_conv(norm_full()), norm_add_1())
            else:
                return pt
        else:
            return pt


@register_macro('nat_norm')
class nat_norm_macro(Macro):
    """Attempt to prove goal by normalization."""

    def __init__(self):
        self.level = 10
        self.sig = Term
        self.limit = 'nat_nat_power_def_1'

    def eval(self, goal, pts):
        # Simply produce the goal.
        assert len(pts) == 0, "nat_norm_macro"
        return Thm([], goal)

    def can_eval(self, goal):
        assert isinstance(goal, Term), "nat_norm_macro"
        if not (goal.is_equals() and goal.lhs.get_type() == NatType):
            return False

        t1, t2 = goal.args
        pt1 = norm_full().get_proof_term(t1)
        pt2 = norm_full().get_proof_term(t2)
        return pt1.prop.rhs == pt2.prop.rhs

    def get_proof_term(self, goal, pts):
        assert len(pts) == 0, "nat_norm_macro"
        assert goal.is_equals(), "nat_norm_macro: goal is not an equality."

        t1, t2 = goal.args
        pt1 = norm_full().get_proof_term(t1)
        pt2 = norm_full().get_proof_term(t2)
        assert pt1.prop.rhs == pt2.prop.rhs, "nat_norm_macro: normalization is not equal."
        return pt1.transitive(pt2.symmetric())


@register_method('nat_norm')
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
        if nat_norm_macro().can_eval(cur_th.prop):
            return [{}]
        else:
            return []

    def display_step(self, state, data):
        return pprint.N("nat_norm: (solves)")

    def apply(self, state, id, data, prevs):
        assert len(prevs) == 0, "nat_norm_method"
        state.apply_tactic(id, MacroTactic('nat_norm'))


def ineq_zero_proof_term(n):
    """Returns the inequality n ~= 0."""
    assert n != 0, "ineq_zero_proof_term: n = 0"
    if n == 1:
        return ProofTerm.theorem("one_nonzero")
    elif n % 2 == 0:
        return apply_theorem("bit0_nonzero", ineq_zero_proof_term(n // 2))
    else:
        return apply_theorem("bit1_nonzero", inst=Inst(m=Binary(n // 2)))

def ineq_one_proof_term(n):
    """Returns the inequality n ~= 1."""
    assert n != 1, "ineq_one_proof_term: n = 1"
    if n == 0:
        return apply_theorem("ineq_sym", ProofTerm.theorem("one_nonzero"))
    elif n % 2 == 0:
        return apply_theorem("bit0_neq_one", inst=Inst(m=Binary(n // 2)))
    else:
        return apply_theorem("bit1_neq_one", ineq_zero_proof_term(n // 2))

def ineq_proof_term(m, n):
    """Returns the inequality m ~= n."""
    assert m != n, "ineq_proof_term: m = n"
    if n == 0:
        return ineq_zero_proof_term(m)
    elif n == 1:
        return ineq_one_proof_term(m)
    elif m == 0:
        return apply_theorem("ineq_sym", ineq_zero_proof_term(n))
    elif m == 1:
        return apply_theorem("ineq_sym", ineq_one_proof_term(n))
    elif m % 2 == 0 and n % 2 == 0:
        return apply_theorem("bit0_neq", ineq_proof_term(m // 2, n // 2))
    elif m % 2 == 1 and n % 2 == 1:
        return apply_theorem("bit1_neq", ineq_proof_term(m // 2, n // 2))
    elif m % 2 == 0 and n % 2 == 1:
        return apply_theorem("bit0_bit1_neq", inst=Inst(m=Binary(m // 2), n=Binary(n // 2)))
    else:
        return apply_theorem("ineq_sym", ineq_proof_term(n, m))


@register_macro('nat_const_ineq')
class nat_const_ineq_macro(Macro):
    """Given m and n, with m ~= n, return the inequality theorem."""
    def __init__(self):
        self.level = 10
        self.sig = Term
        self.limit = 'bit1_neq_one'

    def can_eval(self, goal):
        assert isinstance(goal, Term), "nat_const_ineq_macro"
        if not (goal.is_not() and goal.arg.is_equals()):
            return False

        m, n = goal.arg.args
        return m.is_number() and n.is_number() and m.dest_number() != n.dest_number()

    def eval(self, goal, pts):
        assert len(pts) == 0 and self.can_eval(goal), "nat_const_ineq_macro"

        # Simply produce the goal.
        return Thm([], goal)

    def get_proof_term(self, goal, pts):
        assert len(pts) == 0 and self.can_eval(goal), "nat_const_ineq_macro"

        m, n = goal.arg.args
        pt = ineq_proof_term(m.dest_number(), n.dest_number())
        return pt.on_prop(arg_conv(binop_conv(rewr_of_nat_conv(sym=True))))

def nat_const_ineq(a, b):
    return ProofTerm("nat_const_ineq", Not(Eq(a, b)), [])


@register_method('nat_const_ineq')
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
        if nat_const_ineq_macro().can_eval(cur_th.prop):
            return [{}]
        else:
            return []

    def display_step(self, state, data):
        return pprint.N("nat_const_ineq: (solves)")

    def apply(self, state, id, data, prevs):
        assert len(prevs) == 0, "nat_const_ineq_method"
        state.apply_tactic(id, MacroTactic('nat_const_ineq'))


@register_macro('nat_const_less_eq')
class nat_const_less_eq_macro(Macro):
    """Given m and n, with m <= n, return the less-equal theorem."""
    def __init__(self):
        self.level = 10
        self.sig = Term
        self.limit = 'bit1_neq_one'

    def can_eval(self, goal):
        assert isinstance(goal, Term), "nat_const_less_eq_macro"
        if not goal.is_less_eq():
            return False

        m, n = goal.args
        return m.is_number() and n.is_number() and m.dest_number() <= n.dest_number()

    def eval(self, goal, pts):
        assert len(pts) == 0 and self.can_eval(goal), "nat_const_less_eq_macro"

        # Simply produce the goal.
        return Thm([], goal)

    def get_proof_term(self, goal, pts):
        assert len(pts) == 0 and self.can_eval(goal), "nat_const_less_eq_macro"

        m, n = goal.args
        assert m.dest_number() <= n.dest_number()
        p = Nat(n.dest_number() - m.dest_number())
        eq = refl(m + p).on_rhs(norm_full()).symmetric()
        goal2 = rewr_conv('less_eq_exist').eval(goal).prop.rhs
        ex_eq = apply_theorem('exI', eq, concl=goal2)
        return ex_eq.on_prop(rewr_conv('less_eq_exist', sym=True))

def nat_less_eq(t1, t2):
    return ProofTerm("nat_const_less_eq", t1 <= t2)

@register_macro('nat_const_less')
class nat_const_less_macro(Macro):
    """Given m and n, with m < n, return the less-than theorem."""
    def __init__(self):
        self.level = 10
        self.sig = Term
        self.limit = 'bit1_neq_one'

    def get_proof_term(self, goal, pts):
        assert isinstance(goal, Term)
        assert len(pts) == 0, "nat_const_less_macro"
        m, n = goal.args
        assert m.dest_number() < n.dest_number()
        less_eq_pt = nat_const_less_eq_macro().get_proof_term(m <= n, [])
        ineq_pt = nat_const_ineq_macro().get_proof_term(Not(Eq(m, n)), [])
        return apply_theorem("less_lesseqI", less_eq_pt, ineq_pt)

def nat_less(t1, t2):
    return ProofTerm("nat_const_less", t1 < t2)

class nat_eq_conv(Conv):
    """Simplify equality a = b to either True or False."""
    def get_proof_term(self, t):
        if not t.is_equals():
            return refl(t)

        a, b = t.args
        if not (a.is_number() and b.is_number()):
            return refl(t)

        if a == b:
            return refl(a).on_prop(rewr_conv("eq_true"))
        else:
            return nat_const_ineq(a, b).on_prop(rewr_conv("eq_false"))
