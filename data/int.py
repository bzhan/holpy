# Author: Bohua Zhan

from kernel.type import Type, TFun, boolT
from kernel.term import Const
from data import nat

# Basic definitions

intT = Type("int")
zero = Const("int_zero", intT)
one = Const("int_one", intT)
of_nat = Const("int_of_nat", TFun(nat.natT, intT))
plus = Const("int_plus", TFun(intT, intT, intT))
minus = Const("int_minus", TFun(intT, intT, intT))
uminus = Const("int_uminus", TFun(intT, intT))
times = Const("int_times", TFun(intT, intT, intT))
less_eq = Const("int_less_eq", TFun(intT, intT, boolT))
less = Const("int_less", TFun(intT, intT, boolT))

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
    if n == 0:
        return zero
    elif n == 1:
        return one
    else:
        return of_nat(nat.to_binary(n))

def is_binary_int(t):
    return t == zero or t == one or \
           (t.is_comb() and t.fun.is_const_name("int_of_nat") and nat.is_binary(t.arg))

def from_binary_int(t):
    assert is_binary_int(t), "from_binary_int"
    if t == zero:
        return 0
    elif t == one:
        return 1
    else:
        return nat.from_binary(t.arg)
