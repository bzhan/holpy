# Author: Bohua Zhan

from collections import OrderedDict

from kernel.type import TFun, TypeMatchException
from kernel.term import Term, Var, Comb, Abs, Bound
from kernel import term
from logic import logic

class MatchException(Exception):
    pass

"""Matching between two terms.

By default, all variables in the pattern can be instantiated.

"""
def first_order_match_incr(pat, t, instsp, *, bd_vars=None, match_vars=None):
    """First-order matching of pat with t, where instsp is the
    current partial instantiation for type and term variables. The
    instantiations are updated by the function.
    
    """
    assert isinstance(pat, Term) and isinstance(t, Term), \
           "first_order_match_incr: pat and t must be terms."
    tyinst, inst = instsp

    if bd_vars is None:
        bd_vars = []

    if match_vars is None:
        match_vars = set(term.get_vars(pat))

    if pat.head in match_vars:
        # Case where the head of the function is a variable.
        if pat.head.name not in inst:
            # If the variable is not instantiated, check that the
            # arguments are distinct bound variables, and all bound
            # variables appearing in t also appear as an argument.
            # If all conditions hold, assign appropriately.
            t_vars = term.get_vars(t)
            if any(v not in bd_vars for v in pat.args):
                raise MatchException
            if len(set(pat.args)) != len(pat.args):
                raise MatchException
            if any(v in t_vars and v not in pat.args for v in bd_vars):
                raise MatchException
            
            pat_T = TFun(*([v.T for v in pat.args] + [t.get_type()]))
            try:
                pat.head.T.match_incr(pat_T, tyinst)
            except TypeMatchException:
                raise MatchException
            inst_t = t
            for v in reversed(pat.args):
                inst_t = Term.mk_abs(v, inst_t)
            inst[pat.head.name] = inst_t
        else:
            # If the variable is already instantiated, apply the
            # instantiation, simplify, and match again.
            pat2 = logic.beta_norm(inst[pat.head.name](*pat.args))
            first_order_match_incr(pat2, t, instsp, bd_vars=bd_vars, match_vars=match_vars-{pat.head})
    elif pat.ty != t.ty:
        # In all other cases, top-level structure of the term
        # must agree.
        raise MatchException
    elif pat.is_var():
        # The case where pat come from a bound variable.
        if pat.name != t.name:
            raise MatchException
    elif pat.is_const():
        # When pat is a constant, t must also be a constant with
        # the same name and matching type.
        if pat.name != t.name:
            raise MatchException
        else:
            try:
                pat.T.match_incr(t.T, tyinst)
            except TypeMatchException:
                raise MatchException
    elif pat.is_comb():
        # In the combination case (where the head is not a variable),
        # match fun and arg.
        first_order_match_incr(pat.fun, t.fun, instsp, bd_vars=bd_vars, match_vars=match_vars)
        first_order_match_incr(pat.arg, t.arg, instsp, bd_vars=bd_vars, match_vars=match_vars)
    elif pat.is_abs():
        # When pat is a lambda term, t must also be a lambda term.
        # Replace bound variable by a variable, then match the body.
        try:
            pat.var_T.match_incr(t.var_T, tyinst)
        except TypeMatchException:
            raise MatchException
        T = pat.var_T.subst(tyinst)
        v = Var(pat.var_name, T)
        pat_body = pat.subst_type(tyinst).subst_bound(v)
        t_body = t.subst_bound(v)
        first_order_match_incr(pat_body, t_body, instsp, bd_vars=bd_vars + [v], match_vars=match_vars)
    elif pat.is_bound():
        raise MatchException
    else:
        raise TypeError

def first_order_match(pat, t):
    """First-order matching of pat with t. Return the instantiation
    or throws MatchException.

    """
    tyinst, inst = dict(), dict()
    first_order_match_incr(pat, t, (tyinst, inst))
    return tyinst, inst
