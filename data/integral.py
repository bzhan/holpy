"""Utility for limits, differentiation, and integration."""

from kernel.type import Type, TFun
from kernel.term import Const
from data import set
from data.real import realT


def netT(T):
    return Type("net", T)

def atreal(x):
    """Given a term x of type real, return at_real x."""
    return Const('atreal', TFun(realT, netT(realT)))(x)

def within(net, S):
    """Form the term within net S.
    
    net -- a term of type 'a net.
    S -- a term of type 'a set.
    
    """
    Ta = net.get_type().args[0]
    return Const('within', TFun(netT(Ta), set.setT(Ta), netT(Ta)))(net, S)
