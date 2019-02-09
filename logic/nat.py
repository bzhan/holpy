# Author: Bohua Zhan

from kernel.type import Type, TFun
from kernel.term import Term, Const
from kernel.thm import Thm
from kernel.macro import ProofMacro, MacroSig, global_macros
from logic.conv import Conv, ConvException, all_conv, rewr_conv_thm, rewr_conv_thm_sym, \
    then_conv, arg_conv, arg1_conv, every_conv, binop_conv
from logic.proofterm import ProofTerm, ProofTermMacro
from logic import term_ord

"""Utility functions for natural number arithmetic."""

natT = Type("nat")
zero = Const("zero", natT)
Suc = Const("Suc", TFun(natT, natT))
one = Suc(zero)
plus = Const("plus", TFun(natT, natT, natT))
times = Const("times", TFun(natT, natT, natT))

def is_Suc(t):
    return t.ty == Term.COMB and t.fun == Suc

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
    return t.is_binop() and t.get_head() == plus

def is_times(t):
    return t.is_binop() and t.get_head() == times

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
    head = t.get_head()
    if t == zero or t == one:
        return True
    elif t.ty != Term.COMB:
        return False
    elif head == bit0 or head == bit1:
        return is_binary(t.arg)
    else:
        return False

def from_binary(t):
    """Convert binary form to integer."""
    if t == zero:
        return 0
    elif t == one:
        return 1
    elif t.get_head() == bit0:
        return 2 * from_binary(t.arg)
    else:
        return 2 * from_binary(t.arg) + 1

class Suc_conv(Conv):
    """Computes Suc of a binary number."""
    def __call__(self, t):
        return Thm.mk_equals(t, to_binary(from_binary(t.arg) + 1))

    def get_proof_term(self, t):
        from logic import basic
        thy = basic.loadTheory('nat')

        n = t.arg  # remove Suc
        if n == zero:
            return all_conv().get_proof_term(t)
        elif n == one:
            return rewr_conv_thm(thy, "one_Suc").get_proof_term(t)
        elif n.get_head() == bit0:
            return rewr_conv_thm(thy, "bit0_Suc").get_proof_term(t)
        else:
            return then_conv(rewr_conv_thm(thy, "bit1_Suc"), arg_conv(Suc_conv())).get_proof_term(t)

class add_conv(Conv):
    """Computes the sum of two binary numbers."""
    def __call__(self, t):
        return Thm.mk_equals(t, to_binary(from_binary(t.arg1) + from_binary(t.arg)))

    def get_proof_term(self, t):
        from logic import basic
        thy = basic.loadTheory('nat')

        n1, n2 = t.arg1, t.arg  # two summands
        if n1 == zero:
            cv = rewr_conv_thm(thy, "plus_def_1")
        elif n2 == zero:
            cv = rewr_conv_thm(thy, "add_0_right")
        elif n1 == one:
            cv = then_conv(rewr_conv_thm(thy, "add_1_left"), Suc_conv())
        elif n2 == one:
            cv = then_conv(rewr_conv_thm(thy, "add_1_right"), Suc_conv())
        elif n1.get_head() == bit0 and n2.get_head() == bit0:
            cv = then_conv(rewr_conv_thm(thy, "bit0_bit0_add"), arg_conv(add_conv()))
        elif n1.get_head() == bit0 and n2.get_head() == bit1:
            cv = then_conv(rewr_conv_thm(thy, "bit0_bit1_add"), arg_conv(add_conv()))
        elif n1.get_head() == bit1 and n2.get_head() == bit0:
            cv = then_conv(rewr_conv_thm(thy, "bit1_bit0_add"), arg_conv(add_conv()))
        else:
            cv = every_conv(rewr_conv_thm(thy, "bit1_bit1_add"),
                arg_conv(arg_conv(add_conv())),
                arg_conv(Suc_conv()))

        return cv.get_proof_term(t)

class mult_conv(Conv):
    """Computes the product of two binary numbers."""
    def __call__(self, t):
        return Thm.mk_equals(t, to_binary(from_binary(t.arg1) * from_binary(t.arg)))

    def get_proof_term(self, t):
        from logic import basic
        thy = basic.loadTheory('nat')

        n1, n2 = t.arg1, t.arg  # two summands
        if n1 == zero:
            cv = rewr_conv_thm(thy, "times_def_1")
        elif n2 == zero:
            cv = rewr_conv_thm(thy, "mult_0_right")
        elif n1 == one:
            cv = rewr_conv_thm(thy, "mult_1_left")
        elif n2 == one:
            cv = rewr_conv_thm(thy, "mult_1_right")
        elif n1.get_head() == bit0 and n2.get_head() == bit0:
            cv = then_conv(rewr_conv_thm(thy, "bit0_bit0_mult"), arg_conv(arg_conv(mult_conv())))
        elif n1.get_head() == bit0 and n2.get_head() == bit1:
            cv = then_conv(rewr_conv_thm(thy, "bit0_bit1_mult"), arg_conv(mult_conv()))
        elif n1.get_head() == bit1 and n2.get_head() == bit0:
            cv = then_conv(rewr_conv_thm(thy, "bit1_bit0_mult"), arg_conv(mult_conv()))
        else:
            cv = every_conv(rewr_conv_thm(thy, "bit1_bit1_mult"),
                arg_conv(arg1_conv(add_conv())),
                arg_conv(arg_conv(arg_conv(mult_conv()))),
                arg_conv(add_conv()))

        return cv.get_proof_term(t)

class nat_conv(Conv):
    """Simplify all arithmetic operations."""
    def __call__(self, t):
        def val(t):
            """Evaluate the given term."""
            if is_binary(t):
                return from_binary(t)
            else:
                f = t.get_head()
                if f == Suc:
                    return val(t.arg) + 1
                elif f == plus:
                    return val(t.arg1) + val(t.arg)
                elif f == times:
                    return val(t.arg1) * val(t.arg)
                else:
                    raise ConvException()

        return Thm.mk_equals(t, to_binary(val(t)))

    def get_proof_term(self, t):
        if is_binary(t):
            cv = all_conv()
        else:
            f = t.get_head()
            if f == Suc:
                cv = then_conv(arg_conv(nat_conv()), Suc_conv())
            elif f == plus:
                cv = then_conv(binop_conv(nat_conv()), add_conv())
            elif f == times:
                cv = then_conv(binop_conv(nat_conv()), mult_conv())
            else:
                raise ConvException()
        
        return cv.get_proof_term(t)

class swap_times_r(Conv):
    """Rewrite (a * b) * c to (a * c) * b, or if the left argument
    is an atom, rewrite a * b to b * a.

    """
    def get_proof_term(self, t):
        from logic import basic
        thy = basic.loadTheory('nat')

        if is_times(t.arg1):
            return every_conv(
                rewr_conv_thm(thy, "mult_assoc"),
                arg_conv(rewr_conv_thm(thy, "mult_comm")),
                rewr_conv_thm_sym(thy, "mult_assoc")
            ).get_proof_term(t)
        else:
            return rewr_conv_thm(thy, "mult_comm").get_proof_term(t)

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
    def get_proof_term(self, t):
        from logic import basic
        thy = basic.loadTheory('nat')

        if t.arg1 == zero:
            cv = rewr_conv_thm(thy, "times_def_1")
        elif t.arg == zero:
            cv = rewr_conv_thm(thy, "mult_0_right")
        elif t.arg1 == one:
            cv = rewr_conv_thm(thy, "mult_1_left")
        elif t.arg == one:
            cv = rewr_conv_thm(thy, "mult_1_right")
        elif is_times(t.arg1):
            cmp = compare_atom(t.arg1.arg, t.arg)
            if cmp == term_ord.GREATER:
                cv = then_conv(
                    swap_times_r(),
                    arg1_conv(norm_mult_atom())
                )
            elif cmp == term_ord.EQUAL:
                if is_binary(t.arg):
                    cv = then_conv(
                        rewr_conv_thm(thy, "mult_assoc"),
                        arg_conv(nat_conv())
                    )
                else:
                    cv = all_conv()
            else:
                cv = all_conv()
        else:
            cmp = compare_atom(t.arg1, t.arg)
            if cmp == term_ord.GREATER:
                cv = rewr_conv_thm(thy, "mult_comm")
            elif cmp == term_ord.EQUAL:
                if is_binary(t.arg):
                    cv = nat_conv()
                else:
                    cv = all_conv()
            else:
                cv = all_conv()

        return cv.get_proof_term(t)

class norm_mult_monomial(Conv):
    """Normalize expression of the form (a_1 * ... * a_n) * (b_1 * ... * b_n)."""
    def get_proof_term(self, t):
        from logic import basic
        thy = basic.loadTheory('nat')

        if is_times(t.arg):
            return every_conv(
                rewr_conv_thm_sym(thy, "mult_assoc"),
                arg1_conv(norm_mult_monomial()),
                norm_mult_atom()
            ).get_proof_term(t)
        else:
            return norm_mult_atom().get_proof_term(t)

class swap_add_r(Conv):
    """Rewrite (a + b) + c to (a + c) + b, or if the left argument
    is an atom, rewrite a + b to b + a.

    """
    def get_proof_term(self, t):
        from logic import basic
        thy = basic.loadTheory('nat')

        if is_plus(t.arg1):
            return every_conv(
                rewr_conv_thm(thy, "add_assoc"),
                arg_conv(rewr_conv_thm(thy, "add_comm")),
                rewr_conv_thm_sym(thy, "add_assoc")
            ).get_proof_term(t)
        else:
            return rewr_conv_thm(thy, "add_comm").get_proof_term(t)

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
    def get_proof_term(self, t):
        from logic import basic
        thy = basic.loadTheory('nat')

        if is_times(t) and is_binary(t.arg):
            return all_conv().get_proof_term(t)
        elif is_binary(t):
            return rewr_conv_thm_sym(thy, "mult_1_left").get_proof_term(t)
        else:
            return rewr_conv_thm_sym(thy, "mult_1_right").get_proof_term(t)

class from_coeff_form(Conv):
    """Convert a * 1 to a, 1 * n to n, and leave a * n unchanged."""
    def get_proof_term(self, t):
        from logic import basic
        thy = basic.loadTheory('nat')

        if t.arg == one:
            return rewr_conv_thm(thy, "mult_1_right").get_proof_term(t)
        elif t.arg1 == one:
            return rewr_conv_thm(thy, "mult_1_left").get_proof_term(t)
        else:
            return all_conv().get_proof_term(t)

def combine_monomial():
    """Combine two monomials with the same body."""
    from logic import basic
    thy = basic.loadTheory('nat')

    return every_conv(
        binop_conv(to_coeff_form()),
        rewr_conv_thm_sym(thy, "distrib_l"),
        arg_conv(nat_conv()),
        from_coeff_form()
    )

class norm_add_monomial(Conv):
    """Normalize expression of the form (a_1 + ... + a_n) + a."""
    def get_proof_term(self, t):
        from logic import basic
        thy = basic.loadTheory('nat')

        if t.arg1 == zero:
            cv = rewr_conv_thm(thy, "plus_def_1")
        elif t.arg == zero:
            cv = rewr_conv_thm(thy, "add_0_right")
        elif is_plus(t.arg1):
            cmp = compare_monomial(t.arg1.arg, t.arg)
            if cmp == term_ord.GREATER:
                cv = then_conv(swap_add_r(), arg1_conv(norm_add_monomial()))
            elif cmp == term_ord.EQUAL:
                cv = then_conv(
                    rewr_conv_thm(thy, "add_assoc"),
                    arg_conv(combine_monomial())
                )
            else:
                cv = all_conv()
        else:
            cmp = compare_monomial(t.arg1, t.arg)
            if cmp == term_ord.GREATER:
                cv = rewr_conv_thm(thy, "add_comm")
            elif cmp == term_ord.EQUAL:
                cv = combine_monomial()
            else:
                cv = all_conv()

        return cv.get_proof_term(t)

class norm_add_polynomial(Conv):
    """Normalize expression of the form (a_1 + ... + a_n) + (b_1 + ... + b_n)."""
    def get_proof_term(self, t):
        from logic import basic
        thy = basic.loadTheory('nat')

        if is_plus(t.arg):
            return every_conv(
                rewr_conv_thm_sym(thy, "add_assoc"),
                arg1_conv(norm_add_polynomial()),
                norm_add_monomial()
            ).get_proof_term(t)
        else:
            return norm_add_monomial().get_proof_term(t)

class norm_mult_poly_monomial(Conv):
    """Normalize expression of the form (a_1 + ... + a_n) * b."""
    def get_proof_term(self, t):
        from logic import basic
        thy = basic.loadTheory('nat')

        if is_plus(t.arg1):
            return every_conv(
                rewr_conv_thm(thy, "distrib_r"),
                arg1_conv(norm_mult_poly_monomial()),
                arg_conv(norm_mult_monomial()),
                norm_add_polynomial()
            ).get_proof_term(t)
        else:
            return norm_mult_monomial().get_proof_term(t)

class norm_mult_polynomial(Conv):
    """Normalize expression of the form (a_1 + ... + a_n) * (b_1 + ... + b_n)."""
    def get_proof_term(self, t):
        from logic import basic
        thy = basic.loadTheory('nat')

        if is_plus(t.arg):
            return every_conv(
                rewr_conv_thm(thy, "distrib_l"),
                arg1_conv(norm_mult_polynomial()),
                arg_conv(norm_mult_poly_monomial()),
                norm_add_polynomial()
            ).get_proof_term(t)
        else:
            return norm_mult_poly_monomial().get_proof_term(t)

class norm_full(Conv):
    """Normalize expressions on natural numbers involving plus and times."""
    def get_proof_term(self, t):
        from logic import basic
        thy = basic.loadTheory('nat')

        if is_binary(t):
            cv = all_conv()
        elif is_Suc(t):
            cv = then_conv(rewr_conv_thm_sym(thy, "add_1_right"), norm_full())
        elif is_plus(t):
            cv = then_conv(binop_conv(norm_full()), norm_add_polynomial())
        elif is_times(t):
            cv = then_conv(binop_conv(norm_full()), norm_mult_polynomial())
        else:
            cv = all_conv()

        return cv.get_proof_term(t)


class nat_norm_macro(ProofTermMacro):
    """Attempt to prove goal by normalization."""

    def __init__(self):
        self.level = 10
        self.sig = MacroSig.TERM
        self.has_theory = False

    def __call__(self, args):
        # Simply produce the goal.
        return Thm([], args)

    def get_proof_term(self, args):
        assert args.is_equals(), "nat_norm_macro: goal is not an equality."

        t1, t2 = args.arg1, args.arg
        pt1 = norm_full().get_proof_term(t1)
        pt2 = norm_full().get_proof_term(t2)
        assert pt1.th.concl.arg == pt2.th.concl.arg, "nat_norm_macro: normalization is not equal."

        return ProofTerm.transitive(pt1, ProofTerm.symmetric(pt2))


global_macros.update({
    "nat_norm": nat_norm_macro()
})
