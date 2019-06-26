# Author: Bohua Zhan

from kernel.type import TFun
from kernel.term import Const
from data.nat import natT
from data.set import setT

def mk_interval(m, n):
    return Const("nat_interval", TFun(natT, natT, setT(natT)))(m, n)

def is_interval(t):
    return t.is_binop() and t.head.is_const_name("nat_interval")
