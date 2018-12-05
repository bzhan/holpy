# Author: Bohua Zhan

from kernel.type import Type, TFun
from kernel.term import Const

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
