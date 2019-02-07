# Author: Bohua Zhan

from kernel.type import Type, TFun
from kernel.term import Term, Const
from kernel.thm import Thm
from logic.conv import Conv, ConvException, all_conv, rewr_conv_thm, \
    then_conv, arg_conv, arg1_conv, every_conv, binop_conv
from logic.proofterm import ProofTerm

"""Utility functions for natural number arithmetic."""

natT = Type("nat")
zero = Const("zero", natT)
Suc = Const("Suc", TFun(natT, natT))
one = Suc(zero)
plus = Const("plus", TFun(natT, natT, natT))
times = Const("times", TFun(natT, natT, natT))

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
        thy = basic.NatTheory

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
        thy = basic.NatTheory

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
        thy = basic.NatTheory

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
