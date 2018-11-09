# Author: Bohua Zhan

from kernel.type import Type, TFun
from kernel.term import Const

class Nat():
    """Utility functions for natural number arithmetic."""

    nat = Type("nat")
    zero = Const("0", nat)
    Suc = Const("Suc", TFun(nat, nat))
    one = Suc(zero)
    plus = Const("plus", TFun(nat, nat, nat))
    times = Const("times", TFun(nat, nat, nat))
