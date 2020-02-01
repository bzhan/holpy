# Author: Bohua Zhan

from kernel.type import Type, TFun
from kernel.term import Term, Const

"""Binary numbers"""

natT = Type("nat")
zero = Const("zero", natT)
one = Const("one", natT)

bit0 = Const("bit0", TFun(natT, natT))
bit1 = Const("bit1", TFun(natT, natT))
    
def to_binary(n):
    """Convert Python integer n to HOL binary form (without
    appending of_nat).
    
    """
    assert isinstance(n, int), "to_binary"
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
    assert isinstance(t, Term), "is_binary"
    if t == zero or t == one or t.is_const("zero") or t.is_const("one"):
        return True
    elif not t.is_comb():
        return False
    elif t.head == bit0 or t.head == bit1:
        return is_binary(t.arg)
    else:
        return False

def from_binary(t):
    """Convert HOL binary form (without of_nat) to Python integer."""
    assert isinstance(t, Term), "from_binary"
    if t == zero or t.is_const("zero"):
        return 0
    elif t == one or t.is_const("one"):
        return 1
    elif t.head == bit0:
        return 2 * from_binary(t.arg)
    else:
        return 2 * from_binary(t.arg) + 1
