"""Utility for limits, differentiation, and integration."""

from kernel.type import TConst, TFun, RealType
from kernel.term import Const
from data import set


def netT(T):
    return TConst("net", T)

def atreal(x):
    """Given a term x of type real, return at_real x."""
    return Const('atreal', TFun(RealType, netT(RealType)))(x)

def within(net, S):
    """Form the term within net S.
    
    net -- a term of type 'a net.
    S -- a term of type 'a set.
    
    """
    Ta = net.get_type().args[0]
    return Const('within', TFun(netT(Ta), set.setT(Ta), netT(Ta)))(net, S)
