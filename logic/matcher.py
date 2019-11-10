# Author: Bohua Zhan

"""Matching between two terms.

By default, all variables in the pattern can be instantiated.

"""
from collections import OrderedDict

from kernel import type as hol_type
from kernel.type import HOLType, TVar, Type, TFun, TypeMatchException
from kernel.term import Term, Var, Const, Comb, Abs, Bound
from kernel import term
from util import name

class MatchException(Exception):
    pass


def is_pattern(t, matched_vars):
    """Test whether t is a matchable pattern, given the current instantiations."""
    if t.is_abs():
        return is_pattern(t.body, matched_vars)
    else:
        if t.head.is_svar() and t.head.name not in matched_vars:
            return all(arg.is_bound() or arg.is_svar() and arg.name in matched_vars for arg in t.args) and \
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
            all_vars = list(set(matched_vars + [v.name for v in term.get_svars(ts[0])]))
            return is_pattern_list(ts[1:], all_vars)
        else:
            if not is_pattern_list(ts[1:], matched_vars):
                return False
            all_vars = list(set(matched_vars + [v.name for v in term.get_svars(ts[1:])]))
            return is_pattern(ts[0], all_vars)

def find_term(t, sub_t):
    if t == sub_t:
        return True
    if t.is_comb():
        return find_term(t.fun) or find_term(t.arg)
    if t.is_abs():
        return find_term(t.body)
    return False

def first_order_match_incr(pat, t, instsp):
    """First-order matching of pat with t, where instsp is the
    current partial instantiation for type and term variables. The
    instantiations are updated by the function.
    
    """
    assert isinstance(pat, Term) and isinstance(t, Term), \
           "first_order_match_incr: pat and t must be terms."
    assert len(term.get_svars(t)) == 0, "first_order_match_incr: t should not contain patterns."

    # print("First order match", pat, "with", t)
    def match(pat, t, instsp, bd_vars):
        tyinst, inst = instsp
        # print("Match", repr(pat), "with", repr(t), "inst", inst)
        if pat.head.is_svar():
            # Case where the head of the function is a variable.
            if pat.head.name not in inst:
                # If the head variable is not instantiated, check that the
                # arguments are distinct, and each argument is either a
                # bound variable or a matched variable. In addition, all bound
                # variables appearing in t also appear as an argument.
                # If all conditions hold, assign appropriately.

                heuristic_match = False
                # Check each argument is either a bound variable or is a
                # schematic variable that is already matched.
                for v in pat.args:
                    if not (v in bd_vars or (v.is_svar() and v.name in inst)):
                        heuristic_match = True

                # Check arguments of pat are distinct.
                if len(set(pat.args)) != len(pat.args):
                    heuristic_match = True

                # Check t does not contain any extra bound variables.
                t_vars = term.get_vars(t)
                if any(v in t_vars and v not in pat.args for v in bd_vars):
                    heuristic_match = True

                if heuristic_match:
                    # Heuristic matching: just assign pat.fun to t.fun.
                    if pat.is_svar():
                        # t contains bound variables, so match fails
                        raise MatchException
                    elif t.is_comb():
                        inst[pat.head.name] = t.fun
                        match(pat.arg, t.arg, instsp, bd_vars)
                    else:
                        raise MatchException
                else:
                    # First, obtain and match the expected type of pat_T.
                    Tlist = []
                    for v in pat.args:
                        if v in bd_vars:
                            Tlist.append(v.T)
                        else:
                            Tlist.append(inst[v.name].get_type())
                    Tlist.append(t.get_type())
                    try:
                        pat.head.T.match_incr(TFun(*Tlist), tyinst)
                    except TypeMatchException:
                        raise MatchException

                    # The instantiation of the head variable is computed by starting
                    # with t, then abstract each of the arguments.
                    inst_t = t
                    for v in reversed(pat.args):
                        if v in bd_vars:
                            if inst_t.is_comb() and inst_t.arg == v and v not in term.get_vars(inst_t.fun):
                                # inst_t is of the form f x, where x is the argument.
                                # In this case, directly reduce to f.
                                inst_t = inst_t.fun
                            else:
                                # Otherwise, perform the abstraction.
                                inst_t = Term.mk_abs(v, inst_t)
                        else:
                            assert v.name in inst
                            inst_v = inst[v.name]
                            if inst_t.is_comb() and inst_t.arg == inst_v and not find_term(inst_t.fun, inst_v):
                                inst_t = inst_t.fun
                            elif inst_v.is_var():
                                inst_t = Term.mk_abs(inst_v, inst_t)
                            else:
                                raise MatchException
                    inst[pat.head.name] = inst_t
            else:
                # If the head variable is already instantiated, apply the
                # instantiation onto the arguments, simplify using beta-conversion,
                # and match again.
                pat2 = inst[pat.head.name](*pat.args).beta_norm()
                match(pat2, t.beta_norm(), instsp, bd_vars)
        elif pat.ty != t.ty:
            # In all other cases, top-level structure of the term
            # must agree.
            raise MatchException
        elif pat.is_var() or pat.is_const():
            # The case where pat is a free variable, constant, or comes
            # from a bound variable.
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
            if is_pattern(pat.fun, [v.name for v in bd_vars] + list(instsp[1].keys())):
                match(pat.fun, t.fun, instsp, bd_vars)
                match(pat.arg, t.arg, instsp, bd_vars)
            else:
                match(pat.arg, t.arg, instsp, bd_vars)
                match(pat.fun, t.fun, instsp, bd_vars)
        elif pat.is_abs():
            # When pat is a lambda term, t must also be a lambda term.
            # Replace bound variable by a variable, then match the body.
            try:
                pat.var_T.match_incr(t.var_T, tyinst)
            except TypeMatchException:
                raise MatchException
            T = pat.var_T.subst(tyinst)
            var_names = [v.name for v in term.get_vars(pat.body) + term.get_vars(t.body)]
            nm = name.get_variant_name(pat.var_name, var_names)
            v = Var(nm, T)
            pat_body = pat.subst_type(tyinst).subst_bound(v)
            t_body = t.subst_bound(v)
            match(pat_body, t_body, instsp, bd_vars + [v])
        elif pat.is_bound():
            raise MatchException
        else:
            raise TypeError

    match(pat, t, instsp, [])

def first_order_match(pat, t):
    """First-order matching of pat with t. Return the instantiation
    or throws MatchException.

    """
    tyinst, inst = dict(), dict()
    first_order_match_incr(pat, t, (tyinst, inst))
    return tyinst, inst

def first_order_match_list_incr(pats, ts, instsp):
    """First-order matching of a list of pattern-term pairs."""
    if len(pats) == 0:
        return
    
    if len(pats) == 1:
        first_order_match_incr(pats[0], ts[0], instsp)
        return

    if is_pattern(pats[0], list(instsp[1].keys())):
        first_order_match_incr(pats[0], ts[0], instsp)
        first_order_match_list_incr(pats[1:], ts[1:], instsp)
        return
    else:
        first_order_match_list_incr(pats[1:], ts[1:], instsp)
        first_order_match_incr(pats[0], ts[0], instsp)
        return
