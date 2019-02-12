# Author: Bohua Zhan

from kernel.type import TypeMatchException
from kernel.term import Term, Comb, Abs, Bound

class MatchException(Exception):
    pass

"""Matching between two terms.

By default, all variables in the pattern can be instantiated.

"""
def first_order_match_incr(pat, t, instsp):
    """First-order matching of pat with t, where instsp is the
    current partial instantiation for type and term variables. The
    instantiations are updated by the function.
    
    """
    tyinst, inst = instsp
    if pat.ty == Term.VAR:
        if pat.name in inst:
            if t != inst[pat.name]:
                raise MatchException()
        elif Term.is_open(t):
            raise MatchException()
        else:
            try:
                pat.T.match_incr(t.get_type(), tyinst)
            except TypeMatchException:
                raise MatchException()
            inst[pat.name] = t
    elif pat.ty != t.ty:
        raise MatchException()
    elif pat.ty == Term.CONST:
        if pat.name != t.name:
            raise MatchException()
        else:
            try:
                pat.T.match_incr(t.T, tyinst)
            except TypeMatchException:
                raise MatchException()
    elif pat.ty == Term.COMB:
        if pat.fun.ty == Term.VAR and pat.arg == Bound(0):
            if pat.fun.name not in inst:
                inst[pat.fun.name] = Abs("x", pat.fun.T.domain_type(), t)
            else:
                inst_name = inst[pat.fun.name]
                if inst_name.ty == Term.ABS and inst_name.body == t:
                    pass
                elif inst_name.ty == Term.VAR and t == Comb(inst_name, Bound(0)):
                    pass
                else:
                    raise MatchException()
        else:
            first_order_match_incr(pat.fun, t.fun, instsp)
            first_order_match_incr(pat.arg, t.arg, instsp)
    elif pat.ty == Term.ABS:
        try:
            pat.var_T.match_incr(t.var_T, tyinst)
        except TypeMatchException:
            raise MatchException()
        first_order_match_incr(pat.body, t.body, instsp)
    elif pat.ty == Term.BOUND:
        if pat.n == t.n:
            return None
        else:
            raise MatchException()
    else:
        raise TypeError()

def first_order_match(pat, t):
    """First-order matching of pat with t. Return the instantiation
    or throws MatchException.

    """
    tyinst, inst = dict(), dict()
    first_order_match_incr(pat, t, (tyinst, inst))
    return tyinst, inst
