# Author: Bohua Zhan

from kernel.term import Term

class MatchException(Exception):
    pass

class Matcher():
    """Matching between two terms.

    By default, all variables in the pattern can be instantiated.

    """
    @staticmethod
    def first_order_match_incr(pat, t, inst):
        """First-order matching of pat with t, where inst is the current
        partial instantiation. This is updated by the function.
        
        """
        if pat.ty == Term.VAR:
            if pat.name in inst:
                if t != inst[pat.name]:
                    raise MatchException()
            else:
                if Term.is_open(t):
                    raise MatchException()
                else:
                    inst[pat.name] = t
        elif pat.ty != t.ty:
            raise MatchException()
        elif pat.ty == Term.CONST:
            if pat == t:
                return None
            else:
                raise MatchException()
        elif pat.ty == Term.COMB:
            Matcher.first_order_match_incr(pat.fun, t.fun, inst)
            Matcher.first_order_match_incr(pat.arg, t.arg, inst)
        elif pat.ty == Term.ABS:
            Matcher.first_order_match_incr(pat.body, t.body, inst)
        elif pat.ty == Term.BOUND:
            if pat.n == t.n:
                return None
            else:
                raise MatchException()
        else:
            raise TypeError()

    @staticmethod
    def first_order_match(pat, t):
        """First-order matching of pat with t. Return the instantiation
        or throws MatchException.

        """
        inst = dict()
        Matcher.first_order_match_incr(pat, t, inst)
        return inst
