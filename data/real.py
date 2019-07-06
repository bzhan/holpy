# Author: Bohua Zhan

from kernel.type import Type, TFun, boolT
from kernel.term import Const
from data import nat

# Basic definitions

realT = Type("real")
zero = Const("real_zero", realT)
one = Const("real_one", realT)
of_nat = Const("real_of_nat", TFun(nat.natT, realT))
plus = Const("real_plus", TFun(realT, realT, realT))
minus = Const("real_minus", TFun(realT, realT, realT))
uminus = Const("real_uminus", TFun(realT, realT))
times = Const("real_times", TFun(realT, realT, realT))
less_eq = Const("real_less_eq", TFun(realT, realT, boolT))
less = Const("real_less", TFun(realT, realT, boolT))

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

def is_less_eq(t):
    return t.is_binop() and t.head == less_eq

def is_less(t):
    return t.is_binop() and t.head == less

def to_binary_real(n):
    if n == 0:
        return zero
    elif n == 1:
        return one
    else:
        return of_nat(nat.to_binary(n))
