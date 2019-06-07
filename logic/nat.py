# Author: Bohua Zhan

from kernel.type import Type, TFun
from kernel.term import Term, Const
from kernel.thm import Thm
from kernel.theory import global_methods
from kernel import macro
from logic.conv import Conv, ConvException, all_conv, rewr_conv, \
    then_conv, arg_conv, arg1_conv, every_conv, binop_conv
from logic.proofterm import ProofTerm, ProofTermMacro, ProofTermDeriv, refl
from logic.logic_macro import apply_theorem
from logic import logic
from logic import term_ord
from server.method import Method
from server.tactic import MacroTactic

"""Utility functions for natural number arithmetic."""

natT = Type("nat")
zero = Const("zero", natT)
Suc = Const("Suc", TFun(natT, natT))
one = Suc(zero)
plus = Const("plus", TFun(natT, natT, natT))
times = Const("times", TFun(natT, natT, natT))

def is_Suc(t):
    return t.is_comb() and t.fun == Suc

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

def is_times(t):
    return t.is_binop() and t.head == times

bit0 = Const("bit0", TFun(natT, natT))
bit1 = Const("bit1", TFun(natT, natT))
    
def to_binary(n):
    """Convert integer n to binary form."""
    if n == 0:
        return zero
    elif n == 1:
        return one
    elif n % 2 == 0:
        return bit0(to_binary(n // 2))
    else:
        return bit1(to_binary(n // 2))

def is_binary(t):
    """Whether the term t is in standard binary form."""
    if t == zero or t == one:
        return True
    elif t.ty != Term.COMB:
        return False
    elif t.head == bit0 or t.head == bit1:
        return is_binary(t.arg)
    else:
        return False

def from_binary(t):
    """Convert binary form to integer."""
    if t == zero:
        return 0
    elif t == one:
        return 1
    elif t.head == bit0:
        return 2 * from_binary(t.arg)
    else:
        return 2 * from_binary(t.arg) + 1

class Suc_conv(Conv):
    """Computes Suc of a binary number."""
    def eval(self, thy, t):
        return Thm.mk_equals(t, to_binary(from_binary(t.arg) + 1))

    def get_proof_term(self, thy, t):
        n = t.arg  # remove Suc
        if n == zero:
            return all_conv().get_proof_term(thy, t)
        elif n == one:
            return rewr_conv("one_Suc").get_proof_term(thy, t)
        elif n.head == bit0:
            return rewr_conv("bit0_Suc").get_proof_term(thy, t)
        else:
            return then_conv(rewr_conv("bit1_Suc"), arg_conv(self)).get_proof_term(thy, t)

class add_conv(Conv):
    """Computes the sum of two binary numbers."""
    def eval(self, thy, t):
        return Thm.mk_equals(t, to_binary(from_binary(t.arg1) + from_binary(t.arg)))

    def get_proof_term(self, thy, t):
        if not (is_plus(t) and is_binary(t.arg1) and is_binary(t.arg)):
            raise ConvException
        n1, n2 = t.arg1, t.arg  # two summands
        if n1 == zero:
            cv = rewr_conv("plus_def_1")
        elif n2 == zero:
            cv = rewr_conv("add_0_right")
        elif n1 == one:
            cv = then_conv(rewr_conv("add_1_left"), Suc_conv())
        elif n2 == one:
            cv = then_conv(rewr_conv("add_1_right"), Suc_conv())
        elif n1.head == bit0 and n2.head == bit0:
            cv = then_conv(rewr_conv("bit0_bit0_add"), arg_conv(self))
        elif n1.head == bit0 and n2.head == bit1:
            cv = then_conv(rewr_conv("bit0_bit1_add"), arg_conv(self))
        elif n1.head == bit1 and n2.head == bit0:
            cv = then_conv(rewr_conv("bit1_bit0_add"), arg_conv(self))
        else:
            cv = every_conv(rewr_conv("bit1_bit1_add"),
                arg_conv(arg_conv(self)),
                arg_conv(Suc_conv()))

        return cv.get_proof_term(thy, t)

class mult_conv(Conv):
    """Computes the product of two binary numbers."""
    def eval(self, thy, t):
        return Thm.mk_equals(t, to_binary(from_binary(t.arg1) * from_binary(t.arg)))

    def get_proof_term(self, thy, t):
        n1, n2 = t.arg1, t.arg  # two summands
        if n1 == zero:
            cv = rewr_conv("times_def_1")
        elif n2 == zero:
            cv = rewr_conv("mult_0_right")
        elif n1 == one:
            cv = rewr_conv("mult_1_left")
        elif n2 == one:
            cv = rewr_conv("mult_1_right")
        elif n1.head == bit0 and n2.head == bit0:
            cv = then_conv(rewr_conv("bit0_bit0_mult"), arg_conv(arg_conv(self)))
        elif n1.head == bit0 and n2.head == bit1:
            cv = then_conv(rewr_conv("bit0_bit1_mult"), arg_conv(self))
        elif n1.head == bit1 and n2.head == bit0:
            cv = then_conv(rewr_conv("bit1_bit0_mult"), arg_conv(self))
        else:
            cv = every_conv(rewr_conv("bit1_bit1_mult"),
                arg_conv(arg1_conv(add_conv())),
                arg_conv(arg_conv(arg_conv(self))),
                arg_conv(add_conv()))

        return cv.get_proof_term(thy, t)

class nat_conv(Conv):
    """Simplify all arithmetic operations."""
    def eval(self, thy, t):
        def val(t):
            """Evaluate the given term."""
            if is_binary(t):
                return from_binary(t)
            else:
                if t.head == Suc:
                    return val(t.arg) + 1
                elif t.head == plus:
                    return val(t.arg1) + val(t.arg)
                elif t.head == times:
                    return val(t.arg1) * val(t.arg)
                else:
                    raise ConvException()

        return Thm.mk_equals(t, to_binary(val(t)))

    def get_proof_term(self, thy, t):
        pt = refl(t)
        if is_binary(t):
            return pt
        else:
            if t.head == Suc:
                return pt.on_rhs(thy, arg_conv(self), Suc_conv())
            elif t.head == plus:
                return pt.on_rhs(thy, binop_conv(self), add_conv())
            elif t.head == times:
                return pt.on_rhs(thy, binop_conv(self), mult_conv())
            else:
                raise ConvException()

class swap_times_r(Conv):
    """Rewrite (a * b) * c to (a * c) * b, or if the left argument
    is an atom, rewrite a * b to b * a.

    """
    def get_proof_term(self, thy, t):
        if is_times(t.arg1):
            return every_conv(
                rewr_conv("mult_assoc"),
                arg_conv(rewr_conv("mult_comm")),
                rewr_conv("mult_assoc", sym=True)
            ).get_proof_term(thy, t)
        else:
            return rewr_conv("mult_comm").get_proof_term(thy, t)

def compare_atom(t1, t2):
    """Compare two atoms, placing numbers last."""
    if is_binary(t1) and is_binary(t2):
        return term_ord.EQUAL
    elif is_binary(t1):
        return term_ord.GREATER
    elif is_binary(t2):
        return term_ord.LESS
    else:
        return term_ord.fast_compare(t1, t2)

class norm_mult_atom(Conv):
    """Normalize expression of the form (a_1 * ... * a_n) * a."""
    def get_proof_term(self, thy, t):
        if t.arg1 == zero:
            cv = rewr_conv("times_def_1")
        elif t.arg == zero:
            cv = rewr_conv("mult_0_right")
        elif t.arg1 == one:
            cv = rewr_conv("mult_1_left")
        elif t.arg == one:
            cv = rewr_conv("mult_1_right")
        elif is_times(t.arg1):
            cmp = compare_atom(t.arg1.arg, t.arg)
            if cmp == term_ord.GREATER:
                cv = then_conv(swap_times_r(), arg1_conv(norm_mult_atom()))
            elif cmp == term_ord.EQUAL:
                if is_binary(t.arg):
                    cv = then_conv(rewr_conv("mult_assoc"), arg_conv(nat_conv()))
                else:
                    cv = all_conv()
            else:
                cv = all_conv()
        else:
            cmp = compare_atom(t.arg1, t.arg)
            if cmp == term_ord.GREATER:
                cv = rewr_conv("mult_comm")
            elif cmp == term_ord.EQUAL:
                if is_binary(t.arg):
                    cv = nat_conv()
                else:
                    cv = all_conv()
            else:
                cv = all_conv()

        return cv.get_proof_term(thy, t)

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

class swap_add_r(Conv):
    """Rewrite (a + b) + c to (a + c) + b, or if the left argument
    is an atom, rewrite a + b to b + a.

    """
    def get_proof_term(self, thy, t):
        if is_plus(t.arg1):
            return every_conv(
                rewr_conv("add_assoc"),
                arg_conv(rewr_conv("add_comm")),
                rewr_conv("add_assoc", sym=True)
            ).get_proof_term(thy, t)
        else:
            return rewr_conv("add_comm").get_proof_term(thy, t)

def dest_monomial(t):
    """Remove coefficient part of a monomial t."""
    if is_times(t) and is_binary(t.arg):
        return t.arg1
    elif is_binary(t):
        return one
    else:
        return t

def compare_monomial(t1, t2):
    """Compare two monomials by their body."""
    return term_ord.fast_compare(dest_monomial(t1), dest_monomial(t2))

class to_coeff_form(Conv):
    """Convert a to a * 1, n to 1 * n, and leave a * n unchanged."""
    def get_proof_term(self, thy, t):
        if is_times(t) and is_binary(t.arg):
            return all_conv().get_proof_term(thy, t)
        elif is_binary(t):
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
        if t.arg1 == zero:
            cv = rewr_conv("plus_def_1")
        elif t.arg == zero:
            cv = rewr_conv("add_0_right")
        elif is_plus(t.arg1):
            cmp = compare_monomial(t.arg1.arg, t.arg)
            if cmp == term_ord.GREATER:
                cv = then_conv(swap_add_r(), arg1_conv(norm_add_monomial()))
            elif cmp == term_ord.EQUAL:
                cv = then_conv(rewr_conv("add_assoc"), arg_conv(combine_monomial(thy)))
            else:
                cv = all_conv()
        else:
            cmp = compare_monomial(t.arg1, t.arg)
            if cmp == term_ord.GREATER:
                cv = rewr_conv("add_comm")
            elif cmp == term_ord.EQUAL:
                cv = combine_monomial(thy)
            else:
                cv = all_conv()

        return cv.get_proof_term(thy, t)

class norm_add_polynomial(Conv):
    """Normalize expression of the form (a_1 + ... + a_n) + (b_1 + ... + b_n)."""
    def get_proof_term(self, thy, t):
        if is_plus(t.arg):
            return every_conv(
                rewr_conv("add_assoc", sym=True),
                arg1_conv(norm_add_polynomial()),
                norm_add_monomial()
            ).get_proof_term(thy, t)
        else:
            return norm_add_monomial().get_proof_term(thy, t)

class norm_mult_poly_monomial(Conv):
    """Normalize expression of the form (a_1 + ... + a_n) * b."""
    def get_proof_term(self, thy, t):
        if is_plus(t.arg1):
            return every_conv(
                rewr_conv("distrib_r"),
                arg1_conv(norm_mult_poly_monomial()),
                arg_conv(norm_mult_monomial()),
                norm_add_polynomial()
            ).get_proof_term(thy, t)
        else:
            return norm_mult_monomial().get_proof_term(thy, t)

class norm_mult_polynomial(Conv):
    """Normalize expression of the form (a_1 + ... + a_n) * (b_1 + ... + b_n)."""
    def get_proof_term(self, thy, t):
        if is_plus(t.arg):
            return every_conv(
                rewr_conv("distrib_l"),
                arg1_conv(norm_mult_polynomial()),
                arg_conv(norm_mult_poly_monomial()),
                norm_add_polynomial()
            ).get_proof_term(thy, t)
        else:
            return norm_mult_poly_monomial().get_proof_term(thy, t)

class norm_full(Conv):
    """Normalize expressions on natural numbers involving plus and times."""
    def get_proof_term(self, thy, t):
        if is_binary(t):
            cv = all_conv()
        elif is_Suc(t):
            cv = then_conv(rewr_conv("add_1_right", sym=True), norm_full())
        elif is_plus(t):
            cv = then_conv(binop_conv(norm_full()), norm_add_polynomial())
        elif is_times(t):
            cv = then_conv(binop_conv(norm_full()), norm_mult_polynomial())
        else:
            cv = all_conv()

        return cv.get_proof_term(thy, t)


class nat_norm_macro(ProofTermMacro):
    """Attempt to prove goal by normalization."""

    def __init__(self):
        self.level = 10
        self.sig = Term

    def eval(self, thy, goal, pts):
        # Simply produce the goal.
        assert len(pts) == 0, "nat_norm_macro"
        return Thm([], goal)

    def can_eval(self, thy, goal):
        assert isinstance(goal, Term), "nat_norm_macro"
        if not goal.is_equals():
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

    def search(self, state, id, prevs):
        if len(prevs) != 0:
            return []

        cur_th = state.get_proof_item(id).th
        if nat_norm_macro().can_eval(state.thy, cur_th.prop):
            return [{}]
        else:
            return []

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
        return apply_theorem(thy, "ineq_symmetric", ProofTerm.theorem(thy, "one_nonzero"))
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
        return apply_theorem(thy, "ineq_symmetric", ineq_zero_proof_term(thy, n))
    elif m == 1:
        return apply_theorem(thy, "ineq_symmetric", ineq_one_proof_term(thy, n))
    elif m % 2 == 0 and n % 2 == 0:
        return apply_theorem(thy, "bit0_neq", ineq_proof_term(thy, m // 2, n // 2))
    elif m % 2 == 1 and n % 2 == 1:
        return apply_theorem(thy, "bit1_neq", ineq_proof_term(thy, m // 2, n // 2))
    elif m % 2 == 0 and n % 2 == 1:
        return apply_theorem(thy, "bit0_bit1_neq", inst={"m": to_binary(m // 2), "n": to_binary(n // 2)})
    else:
        return apply_theorem(thy, "ineq_symmetric", ineq_proof_term(thy, n, m))

class nat_const_ineq_macro(ProofTermMacro):
    """Given m and n, with m ~= n, return the inequality theorem."""

    def __init__(self):
        self.level = 10
        self.sig = Term

    def eval(self, thy, goal, pts):
        # Simply produce the goal.
        assert len(pts) == 0, "nat_const_ineq_macro"
        return Thm([], goal)

    def can_eval(self, thy, goal):
        assert isinstance(goal, Term), "nat_const_ineq_macro"
        if not (logic.is_neg(goal) and goal.arg.is_equals()):
            return False

        m, n = goal.arg.args
        return is_binary(m) and is_binary(n) and from_binary(m) != from_binary(n)

    def get_proof_term(self, thy, goal, pts):
        assert len(pts) == 0, "nat_const_ineq_macro"
        assert logic.is_neg(goal) and goal.arg.is_equals(), \
               "nat_ineq_macro: goal is not an inequality."

        m, n = goal.arg.args
        assert is_binary(m) and is_binary(n), "nat_ineq_macro: m and n are not in binary form."
        assert from_binary(m) != from_binary(n), "nat_ineq_macro: m and n are equal."

        return ineq_proof_term(thy, from_binary(m), from_binary(n))

def nat_const_ineq(thy, a, b):
    goal = logic.neg(Term.mk_equals(a, b))
    return ProofTermDeriv("nat_const_ineq", thy, goal, [])


class nat_const_ineq_method(Method):
    """Apply nat_const_ineq macro."""
    def __init__(self):
        self.sig = []

    def search(self, state, id, prevs):
        if len(prevs) != 0:
            return []

        cur_th = state.get_proof_item(id).th
        if nat_const_ineq_macro().can_eval(state.thy, cur_th.prop):
            return [{}]
        else:
            return []

    def apply(self, state, id, data, prevs):
        assert len(prevs) == 0, "nat_const_ineq_method"
        state.apply_tactic(id, MacroTactic('nat_const_ineq'))


class nat_eq_conv(Conv):
    """Simplify equality a = b to either True or False."""
    def get_proof_term(self, thy, t):
        if not t.is_equals():
            return refl(t)

        a, b = t.args
        if not (is_binary(a) and is_binary(b)):
            return refl(t)

        if a == b:
            return refl(a).on_prop(thy, rewr_conv("eq_true"))
        else:
            return nat_const_ineq(thy, a, b).on_prop(thy, rewr_conv("eq_false"))


macro.global_macros.update({
    "nat_norm": nat_norm_macro(),
    "nat_const_ineq": nat_const_ineq_macro(),
})

global_methods.update({
    "nat_norm": nat_norm_method(),
    "nat_const_ineq": nat_const_ineq_method(),
})