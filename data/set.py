# Author: Bohua Zhan

from kernel.type import TConst, TFun, BoolType
from kernel.term import Term, Const, Lambda


"""Utility functions for sets."""

def setT(T):
    return TConst("set", T)

def empty_set(T):
    if T is None:
        return Const("empty_set", None)
    return Const("empty_set", setT(T))

def is_empty_set(t):
    return t.is_const("empty_set")

def univ(T):
    return Const("univ", setT(T))

def mem(T):
    return Const("member", TFun(T, setT(T), BoolType))

def inter(T):
    return Const("inter", TFun(setT(T), setT(T), setT(T)))

def union(T):
    return Const("union", TFun(setT(T), setT(T), setT(T)))

def Inter(T):
    return Const("Inter", TFun(setT(setT(T)), setT(T)))

def Union(T):
    return Const("Union", TFun(setT(setT(T)), setT(T)))

def mk_mem(x, A):
    return mem(x.get_type())(x, A)

def is_mem(t):
    return t.is_comb('member', 2)

def subset(T):
    return Const("subset", TFun(setT(T), setT(T), BoolType))

def mk_subset(A, B):
    return subset(A.get_type().args[0])(A, B)

def image(T1, T2):
    return Const("image", TFun(TFun(T1, T2), setT(T1), setT(T2)))

def mk_image(f, S):
    T1 = f.get_type().domain_type()
    T2 = f.get_type().range_type()
    return image(T1, T2)(f, S)

def mk_inter(A, B):
    return inter(A.get_type().args[0])(A, B)

def mk_union(A, B):
    return union(A.get_type().args[0])(A, B)

def mk_Inter(t):
    return Inter(t.get_type().args[0].args[0])(t)

def mk_Union(t):
    return Union(t.get_type().args[0].args[0])(t)

def insert(T):
    if T is None:
        return Const("insert", None)
    return Const("insert", TFun(T, setT(T), setT(T)))

def mk_insert(x, A):
    return insert(x.get_type())(x, A)

def is_insert(t):
    return t.is_comb('insert', 2)

def mk_literal_set(ts, T):
    if ts:
        return insert(T)(ts[0], mk_literal_set(ts[1:], T))
    else:
        return empty_set(T)

def is_literal_set(t):
    if is_empty_set(t):
        return True
    elif is_insert(t):
        return is_literal_set(t.arg)
    else:
        return False

def dest_literal_set(t):
    """Given term of the form {x_1, x_2, ..., x_n}, return the list
    of terms x_1, x_2, ..., x_n.

    """
    if is_empty_set(t):
        return []
    elif is_insert(t):
        return [t.arg1] + dest_literal_set(t.arg)
    else:
        raise AssertionError("dest_literal_set")

def collect(T):
    if T is None:
        return Const("collect", None)
    return Const("collect", TFun(TFun(T, BoolType), setT(T)))

def mk_collect(x, body):
    """Given term x and a term P possibly depending on x, return
    the term {x. P}.

    """
    assert x.is_var(), "mk_collect"
    return collect(x.T)(Lambda(x, body))
