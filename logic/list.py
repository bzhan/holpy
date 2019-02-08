# Author: Bohua Zhan

from kernel.type import TVar, Type, TFun
from kernel.term import Const

"""Utility functions for lists."""

_Ta = TVar("a")
_Talist = Type("list", _Ta)

def listT(T):
    return Type("list", T)

nil = Const("nil", _Talist)
cons = Const("cons", TFun(_Ta, _Talist, _Talist))
append = Const("append", TFun(_Talist, _Talist, _Talist))

def is_cons(t):
    return t.is_binop() and t.get_head() == cons

def is_append(t):
    return t.is_binop() and t.get_head() == append

def is_literal_list(t):
    """Whether t is of the form [x_1, ..., x_n]."""
    if t == nil:
        return True
    elif is_cons(t):
        return is_literal_list(t.arg)
    else:
        return False

def dest_literal_list(t):
    """Given term of the form [x_1, ..., x_n], return the list
    of terms x_1, ..., x_n.

    """
    if t == nil:
        return []
    elif is_cons(t):
        return [t.arg1] + dest_literal_list(t.arg)

def mk_literal_list(ts):
    """Given terms x_1, ..., x_n, return the term [x_1, ..., x_n]."""
    if ts:
        return cons(ts[0], mk_literal_list(ts[1:]))
    else:
        return nil
