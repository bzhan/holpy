# Author: Bohua Zhan

from kernel.type import Type
from kernel.term import Term

"""Ordering on terms."""

LESS, EQUAL, GREATER = range(3)

def compare(n1, n2):
    """Compare two integers, strings, etc."""
    if n1 < n2:
        return LESS
    elif n1 > n2:
        return GREATER
    else:
        return EQUAL

def compare_pair(p1, p2, cp1, cp2):
    """Given comparison functions for the first and second part of
    the pair, compare the two pairs using the two functions under
    lexicographic order.

    """
    res1 = cp1(p1[0], p2[0])
    if res1 != EQUAL:
        return res1
    else:
        return cp2(p1[1], p2[1])

def compare_list(l1, l2, cp):
    """Given comparison functions for elements of the list,
    compare the two lists under lexicographic order.

    """
    for i in range(min(len(l1), len(l2))):
        res = cp(l1[i], l2[i])
        if res != EQUAL:
            return res

    return compare(len(l1), len(l2))

def fast_compare_typ(T1, T2):
    if T1.ty != T2.ty:
        return compare(T1.ty, T2.ty)
    elif T1.ty == Type.TVAR:
        return compare(T1.name, T2.name)
    elif T1.ty == Type.TYPE:
        return compare_pair((T1.name, T1.args), (T2.name, T2.args),
                            compare, lambda l1, l2: compare_list(l1, l2, fast_compare_typ))
    else:
        raise TypeError

def fast_compare(t1, t2):
    """Fast ordering between t1 and t2."""
    if t1.ty != t2.ty:
        return compare(t1.ty, t2.ty)
    elif t1.is_var() or t1.is_const():
        return compare_pair((t1.name, t1.T), (t2.name, t2.T), compare, fast_compare_typ)
    elif t1.is_comb():
        return compare_pair((t1.fun, t1.arg), (t2.fun, t2.arg), fast_compare, fast_compare)
    elif t1.is_abs():
        return compare_pair((t1.var_T, t1.body), (t2.var_T, t2.body), fast_compare_typ, fast_compare)
    elif t1.is_bound():
        return compare(t1.n, t2.n)
    else:
        raise TypeError
