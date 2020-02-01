# Author: Bohua Zhan

from kernel.type import Type, TFun, boolT
from kernel.term import Const
from data import nat

# Basic definitions

intT = Type("int")
zero = Const("zero", intT)
one = Const("one", intT)
of_nat = Const("of_nat", TFun(nat.natT, intT))
plus = Const("plus", TFun(intT, intT, intT))
minus = Const("minus", TFun(intT, intT, intT))
uminus = Const("uminus", TFun(intT, intT))
times = Const("times", TFun(intT, intT, intT))
less_eq = Const("less_eq", TFun(intT, intT, boolT))
less = Const("less", TFun(intT, intT, boolT))

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

def is_uminus(t):
    return t.is_comb() and t.head == uminus

def is_minus(t):
    return t.is_binop() and t.head == minus

def is_times(t):
    return t.is_binop() and t.head == times

def is_less_eq(t):
    return t.is_binop() and t.head == less_eq

def is_less(t):
    return t.is_binop() and t.head == less

def to_binary_int(n):
    if n < 0:
        return uminus(to_binary_int(-n))
    if n == 0:
        return zero
    elif n == 1:
        return one
    else:
        return of_nat(nat.to_binary(n))

def is_binary_int(t):
    if t.is_comb('uminus', 1):
        return is_binary_int(t.arg)
    else:
        return t == zero or t == one or \
               (t.is_comb('of_nat', 1) and nat.is_binary(t.arg) and nat.from_binary(t.arg) >= 2)

def from_binary_int(t):
    assert is_binary_int(t), "from_binary_int"
    if t.is_comb('uminus', 1):
        return -from_binary_int(t.arg)
    if t == zero:
        return 0
    elif t == one:
        return 1
    else:
        return nat.from_binary(t.arg)
