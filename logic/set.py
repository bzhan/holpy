# Author: Bohua Zhan

from kernel.type import Type, TFun, boolT
from kernel.term import Const

"""Utility functions for sets."""

def setT(T):
    return Type("set", T)

def empty_set(T):
    return Const("empty_set", setT(T))

def univ(T):
    return Const("univ", setT(T))

def mem(T):
    return Const("member", TFun(T, setT(T), boolT))

def inter(T):
    return Const("inter", TFun(setT(T), setT(T), setT(T)))

def union(T):
    return Const("union", TFun(setT(T), setT(T), setT(T)))

def mk_mem(x, A):
    return mem(x.get_type())(x, A)

def subset(T):
    return Const("subset", TFun(setT(T), setT(T), boolT))

def mk_subset(A, B):
    return subset(A.get_type().args[0])(A, B)

def mk_inter(A, B):
    return inter(A.get_type().args[0])(A, B)

def mk_union(A, B):
    return union(A.get_type().args[0])(A, B)

def is_literal_set(t):
    return t.is_const_name("empty_set")
