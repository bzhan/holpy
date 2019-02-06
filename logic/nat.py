# Author: Bohua Zhan

from kernel.type import Type, TFun
from kernel.term import Term, Const

class Nat():
    """Utility functions for natural number arithmetic."""

    nat = Type("nat")
    zero = Const("zero", nat)
    Suc = Const("Suc", TFun(nat, nat))
    one = Suc(zero)
    plus = Const("plus", TFun(nat, nat, nat))
    times = Const("times", TFun(nat, nat, nat))

    @staticmethod
    def mk_plus(*args):
        if not args:
            return Nat.zero
        elif len(args) == 1:
            return args[0]
        else:
            return Nat.plus(Nat.mk_plus(*args[:-1]), args[-1])

    @staticmethod
    def mk_times(*args):
        if not args:
            return Nat.one
        elif len(args) == 1:
            return args[0]
        else:
            return Nat.times(Nat.mk_times(*args[:-1]), args[-1])

nat = Nat.nat
bit0 = Const("bit0", TFun(nat, nat))
bit1 = Const("bit1", TFun(nat, nat))
    
def to_binary(n):
    """Convert integer n to binary form."""
    if n == 0:
        return Nat.zero
    elif n == 1:
        return Nat.one
    elif n % 2 == 0:
        return bit0(to_binary(n // 2))
    else:
        return bit1(to_binary(n // 2))

def is_binary(t):
    """Whether the term t is in standard binary form."""
    head = t.get_head()
    if t == Nat.zero or t == Nat.one:
        return True
    elif t.ty != Term.COMB:
        return False
    elif head == bit0 or head == bit1:
        return is_binary(t.arg)
    else:
        return False

def from_binary(t):
    """Convert binary form to integer."""
    head = t.get_head()
    if head == Nat.zero:
        return 0
    elif head == Nat.one:
        return 1
    elif head == bit0:
        return 2 * from_binary(t.arg)
    else:
        return 2 * from_binary(t.arg) + 1
