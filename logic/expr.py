# Author: Bohua Zhan

from kernel.type import Type, TFun, hol_bool
from kernel.term import Const
from kernel.thm import Thm
from logic import nat
from logic.nat import natT

"""Automation for arithmetic expressions."""

aexpT = Type("aexp")

N = Const("N", TFun(natT, aexpT))
V = Const("V", TFun(natT, aexpT))
Plus = Const("Plus", TFun(aexpT, aexpT, aexpT))
Times = Const("Times", TFun(aexpT, aexpT, aexpT))

avalI = Const("avalI", TFun(TFun(natT, natT), aexpT, natT, hol_bool))

def prove_avalI(thy, s, t):
    """Given a state s and an expression t, return a theorem of
    the form avalI s t n, where n is a constant natural number.

    """
    f, args = t.strip_comb()
    if f == N:
        n = args[0]
        return Thm([], avalI(s, N(n), n))
    elif f == V:
        x = args[0]
        return Thm([], avalI(s, V(x), s(x)))
    elif f == Plus:
        a1, a2 = args
        th1 = prove_avalI(thy, s, a1)
        th2 = prove_avalI(thy, s, a2)
        _, args1 = th1.concl.strip_comb()
        _, args2 = th2.concl.strip_comb()
        return Thm([], avalI(s, t, nat.plus(args1[2], args2[2])))
    elif f == Times:
        a1, a2 = args
        th1 = prove_avalI(thy, s, a1)
        th2 = prove_avalI(thy, s, a2)
        _, args1 = th1.concl.strip_comb()
        _, args2 = th2.concl.strip_comb()
        return Thm([], avalI(s, t, nat.times(args1[2], args2[2])))
    else:
        raise NotImplementedError
