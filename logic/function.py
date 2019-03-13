# Author: Bohua Zhan

from kernel.type import TFun
from kernel.term import Const, Abs

"""Utility functions for the function library."""

def is_fun_upd(t):
    """Whether t is fun_upd applied to three parameters, that
    is, whether t is of the form f (a := b).

    """
    c, args = t.strip_comb()
    return len(args) == 3 and c.is_const_with_name("fun_upd")

def fun_upd(T1, T2):
    """Returns the term fun_upd on functions of type T1 => T2."""
    return Const("fun_upd", TFun(TFun(T1, T2), T1, T2, T1, T2))

def mk_const_fun(T, k):
    """Returns the term %x::T. k."""
    return Abs("x", T, k)

def mk_fun_upd(*args):
    """Returns the term (f)(a1 := b1, a2 := b2, ...)."""
    if len(args) == 3:
        f, a, b = args
        return fun_upd(a.get_type(), b.get_type())(f, a, b)
    elif len(args) > 3:
        return mk_fun_upd(mk_fun_upd(*args[:3]), *args[3:])
    else:
        raise TypeError()

def strip_fun_upd(t):
    """Given t of the form (f)(a1 := b1, a2 := b2, ...), return
    (f, [(a1, b1), (a2, b2), ...]).

    """
    if is_fun_upd(t):
        _, (f1, a, b) = t.strip_comb()
        f, upds = strip_fun_upd(f1)
        return f, upds + [(a, b)]
    else:
        return t, []
