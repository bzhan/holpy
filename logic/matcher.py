# Author: Bohua Zhan

"""Matching between two terms.

By default, all variables in the pattern can be instantiated.

"""
from collections import OrderedDict

from kernel.type import HOLType, TVar, Type, TFun, TypeMatchException
from kernel.term import Term, Var, Const, Comb, Abs, Bound
from kernel import term

class MatchException(Exception):
    pass


def to_internal_tvars(pat_T):
    """Add underscore to each type variable in the pattern."""
    if pat_T.ty == HOLType.TVAR:
        return TVar("_" + pat_T.name)
    elif pat_T.ty == HOLType.TYPE:
        return Type(pat_T.name, *[to_internal_tvars(arg) for arg in pat_T.args])

def to_internal_vars(pat):
    """Add underscore to each variable in the pattern."""
    if pat.is_var():
        return Var("_" + pat.name, to_internal_tvars(pat.T))
    elif pat.is_const():
        return Const(pat.name, to_internal_tvars(pat.T))
    elif pat.is_comb():
        return to_internal_vars(pat.fun)(to_internal_vars(pat.arg))
    elif pat.is_abs():
        return Abs(pat.var_name, to_internal_tvars(pat.var_T), to_internal_vars(pat.body))
    elif pat.is_bound():
        return pat
    else:
        raise TypeError

def to_internal_instsp(instsp):
    """Convert instantiation pair to assignments of internal variables."""
    tyinst, inst = instsp
    tyinst2 = {"_" + nm: T for nm, T in tyinst.items()}
    inst2 = {"_" + nm: t for nm, t in inst.items()}
    return tyinst2, inst2

def from_internal_instsp(instsp):
    """Convert instantiation pair consisting of assignments to internal
    variables to assignments on normal variables.

    """
    tyinst, inst = instsp
    tyinst2 = {nm[1:]: T for nm, T in tyinst.items()}
    inst2 = {nm[1:]: t for nm, t in inst.items()}
    return tyinst2, inst2

def is_pattern(t, matched_vars):
    """Test whether t is a matchable pattern, given the current instantiations."""
    if t.is_abs():
        return is_pattern(t.body, matched_vars)
    else:
        if t.head.is_var():
            if t.head.name in matched_vars:
                return is_pattern_list(t.args, matched_vars)
            else:
                return all(arg.is_bound() for arg in t.args) and \
                       len(set(t.args)) == len(t.args)
        else:
            return is_pattern_list(t.args, matched_vars)

def is_pattern_list(ts, matched_vars):
    """Test whether a list of ts can be matched."""
    if len(ts) == 0:
        return True
    elif len(ts) == 1:
        return is_pattern(ts[0], matched_vars)
    else:
        if is_pattern(ts[0], matched_vars):
            all_vars = list(set(matched_vars + [v.name for v in term.get_vars(ts[0])]))
            return is_pattern_list(ts[1:], all_vars)
        elif is_pattern_list(ts[1:], matched_vars):
            all_vars = list(set(matched_vars + [v.name for v in term.get_vars(ts[1:])]))
            return is_pattern(ts[0], all_vars)
        else:
            return False

def first_order_match_incr(pat, t, instsp):
    """First-order matching of pat with t, where instsp is the
    current partial instantiation for type and term variables. The
    instantiations are updated by the function.
    
    """
    assert isinstance(pat, Term) and isinstance(t, Term), \
           "first_order_match_incr: pat and t must be terms."
    # print("First order match", pat, "with", t)

    def match(pat, t, instsp, bd_vars):
        tyinst, inst = instsp
        # print("Match", pat, "with", t)
        if pat.head.is_var() and pat.head.name.startswith('_'):
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
                    pat.head.T.match_incr(pat_T, tyinst, internal_only=True)
                except TypeMatchException:
                    raise MatchException
                inst_t = t
                for v in reversed(pat.args):
                    if inst_t.is_comb() and inst_t.arg == v and v not in term.get_vars(inst_t.fun):
                        inst_t = inst_t.fun
                    else:
                        inst_t = Term.mk_abs(v, inst_t)
                inst[pat.head.name] = inst_t
            else:
                # If the variable is already instantiated, apply the
                # instantiation, simplify, and match again.
                pat2 = inst[pat.head.name](*pat.args).beta_norm()
                match(pat2, t.beta_norm(), instsp, bd_vars)
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
                    pat.T.match_incr(t.T, tyinst, internal_only=True)
                except TypeMatchException:
                    raise MatchException
        elif pat.is_comb():
            # In the combination case (where the head is not a variable),
            # match fun and arg.
            if is_pattern(pat.fun, list(instsp[1].keys())):
                match(pat.fun, t.fun, instsp, bd_vars)
                match(pat.arg, t.arg, instsp, bd_vars)
            else:
                match(pat.arg, t.arg, instsp, bd_vars)
                match(pat.fun, t.fun, instsp, bd_vars)
        elif pat.is_abs():
            # When pat is a lambda term, t must also be a lambda term.
            # Replace bound variable by a variable, then match the body.
            try:
                pat.var_T.match_incr(t.var_T, tyinst, internal_only=True)
            except TypeMatchException:
                raise MatchException
            T = pat.var_T.subst(tyinst)
            v = Var(pat.var_name, T)
            pat_body = pat.subst_type(tyinst).subst_bound(v)
            t_body = t.subst_bound(v)
            match(pat_body, t_body, instsp, bd_vars + [v])
        elif pat.is_bound():
            raise MatchException
        else:
            raise TypeError

    instsp2 = to_internal_instsp(instsp)
    match(to_internal_vars(pat), t, instsp2, [])
    instsp[0].update(from_internal_instsp(instsp2)[0])
    instsp[1].update(from_internal_instsp(instsp2)[1])

def first_order_match(pat, t):
    """First-order matching of pat with t. Return the instantiation
    or throws MatchException.

    """
    tyinst, inst = dict(), dict()
    first_order_match_incr(pat, t, (tyinst, inst))
    return tyinst, inst
