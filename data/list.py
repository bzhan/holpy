# Author: Bohua Zhan

from kernel.type import TVar, Type, TFun, NatType
from kernel.term import Term, Const

"""Utility functions for lists."""

def listT(T):
    return Type("list", T)

def nil(T):
    if T is None:
        return Const("nil", None)
    return Const("nil", listT(T))

def cons(T):
    if T is None:
        return Const("cons", None)
    return Const("cons", TFun(T, listT(T), listT(T)))

def append(T):
    if T is None:
        return Const("append", None)
    return Const("append", TFun(listT(T), listT(T), listT(T)))

def is_nil(t):
    return t.is_const("nil")

def is_cons(t):
    return t.is_comb('cons', 2)

def is_append(t):
    return t.is_comb('append', 2)

def mk_cons(x, xs):
    return cons(x.get_type())(x, xs)

def mk_append(xs, ys):
    T = xs.get_type().args[0]
    return append(T)(xs, ys)

def is_literal_list(t):
    """Whether t is of the form [x_1, ..., x_n]."""
    if is_nil(t):
        return True
    elif is_cons(t):
        return is_literal_list(t.arg)
    else:
        return False

def dest_literal_list(t):
    """Given term of the form [x_1, ..., x_n], return the list
    of terms x_1, ..., x_n.

    """
    if is_nil(t):
        return []
    elif is_cons(t):
        return [t.arg1] + dest_literal_list(t.arg)
    else:
        raise AssertionError("dest_literal_list")

def mk_literal_list(ts, T):
    """Given terms x_1, ..., x_n of type T, return the term
    [x_1, ..., x_n].
    
    """
    if ts:
        return cons(T)(ts[0], mk_literal_list(ts[1:], T))
    else:
        return nil(T)

def length(xs):
    """Returns the term length xs."""
    T = xs.get_type().args[0]
    return Const("length", TFun(listT(T), NatType))(xs)

def nth(xs, n):
    """Returns the term nth xs n."""
    T = xs.get_type().args[0]
    return Const("nth", TFun(listT(T), NatType, T))(xs, n)
