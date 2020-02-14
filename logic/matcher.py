# Author: Bohua Zhan

"""Matching between two terms.

By default, all variables in the pattern can be instantiated.

"""
from copy import copy

from kernel.type import TVar, TFun, TypeMatchException
from kernel.term import Term, Var, Const, Comb, Abs, Bound, Inst, Lambda
from kernel import term
from syntax import operator
from util import name
from util import typecheck


class MatchException(Exception):
    def __init__(self, trace):
        self.trace = trace

    def get_trace(self):
        pat, t = self.trace[-1]
        trace = '\n'.join("%s --- %s" % (pat, t) for pat, t in self.trace)
        return "When matching %s with %s\nTrace:\n%s" % (pat, t, trace)


def is_pattern(t, matched_vars, bd_vars=None):
    """Test whether t is a matchable pattern, given the current instantiations."""
    if bd_vars is None:
        bd_vars = []
    if t.is_abs():
        return is_pattern(t.body, matched_vars, bd_vars)
    else:
        if t.head.is_svar() and t.head.name not in matched_vars:
            return all(arg.is_bound() or \
                       arg.is_svar() and arg.name in matched_vars or \
                       arg.is_var() and arg.name in bd_vars for arg in t.args) and \
                   len(set(t.args)) == len(t.args)
        else:
            return is_pattern_list(t.args, matched_vars, bd_vars)

def is_pattern_list(ts, matched_vars, bd_vars=None):
    """Test whether a list of ts can be matched."""
    if len(ts) == 0:
        return True
    elif len(ts) == 1:
        return is_pattern(ts[0], matched_vars, bd_vars)
    else:
        if is_pattern(ts[0], matched_vars):
            all_vars = list(set(matched_vars + [v.name for v in ts[0].get_svars()]))
            return is_pattern_list(ts[1:], all_vars, bd_vars)
        else:
            if not is_pattern_list(ts[1:], matched_vars, bd_vars):
                return False
            all_vars = list(set(matched_vars + [v.name for v in term.get_svars(ts[1:])]))
            return is_pattern(ts[0], all_vars, bd_vars)

def find_term(t, sub_t):
    if t == sub_t:
        return True
    if t.is_comb():
        return find_term(t.fun, sub_t) or find_term(t.arg, sub_t)
    if t.is_abs():
        return find_term(t.body, sub_t)
    return False

def first_order_match_incr(pat, t, inst):
    """First-order matching of pat with t, where inst is the
    current partial instantiation for type and term variables. The
    instantiations are updated by the function.
    
    """
    typecheck.checkinstance('first_order_match_incr', pat, Term, t, Term, inst, Inst)
    assert len(t.get_svars()) == 0, "first_order_match_incr: t should not contain patterns."

    # Trace of pattern and term, for debugging
    trace = []

    def match(pat, t, inst, bd_vars):
        trace.append((pat, t))
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
                t_vars = t.get_vars()
                if any(v in t_vars and v not in pat.args for v in bd_vars):
                    heuristic_match = True

                if heuristic_match:
                    # Heuristic matching: just assign pat.fun to t.fun.
                    if pat.is_svar():
                        # t contains bound variables, so match fails
                        raise MatchException(trace)
                    elif t.is_comb():
                        try:
                            pat.head.T.match_incr(t.fun.get_type(), inst.tyinst)
                        except TypeMatchException:
                            raise MatchException(trace)
                        inst[pat.head.name] = t.fun
                        match(pat.arg, t.arg, inst, bd_vars)
                    else:
                        raise MatchException(trace)
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
                        pat.head.T.match_incr(TFun(*Tlist), inst.tyinst)
                    except TypeMatchException:
                        raise MatchException(trace)

                    # The instantiation of the head variable is computed by starting
                    # with t, then abstract each of the arguments.
                    inst_t = t
                    for v in reversed(pat.args):
                        if v in bd_vars:
                            if inst_t.is_comb() and inst_t.arg == v and v not in inst_t.fun.get_vars():
                                op_data = operator.get_info_for_fun(inst_t.head)
                                if inst_t.is_comb("IF", 3):
                                    inst_t = Lambda(v, inst_t) 
                                elif op_data is None:
                                    # inst_t is of the form f x, where x is the argument.
                                    # In this case, directly reduce to f.
                                    inst_t = inst_t.fun
                                elif op_data.arity == operator.BINARY and len(inst_t.args) == 2:
                                    inst_t = Lambda(v, inst_t)
                                else:
                                    inst_t = inst_t.fun
                            else:
                                # Otherwise, perform the abstraction.
                                inst_t = Lambda(v, inst_t)
                        else:
                            assert v.name in inst
                            inst_v = inst[v.name]
                            if inst_t.is_comb() and inst_t.arg == inst_v and not find_term(inst_t.fun, inst_v):
                                inst_t = inst_t.fun
                            elif inst_v.is_var():
                                inst_t = Lambda(inst_v, inst_t)
                            else:
                                raise MatchException(trace)
                    inst[pat.head.name] = inst_t
            else:
                # If the head variable is already instantiated, apply the
                # instantiation onto the arguments, simplify using beta-conversion,
                # and match again.
                pat2 = inst[pat.head.name](*pat.args).beta_norm()
                match(pat2, t.beta_norm(), inst, bd_vars)
        elif pat.is_var() or pat.is_const():
            # The case where pat is a free variable, constant, or comes
            # from a bound variable.
            if pat.ty != t.ty or pat.name != t.name:
                raise MatchException(trace)
            else:
                try:
                    pat.T.match_incr(t.T, inst.tyinst)
                except TypeMatchException:
                    raise MatchException(trace)
        elif pat.is_comb():
            # In the combination case (where the head is not a variable),
            # match fun and arg.
            if pat.ty != t.ty:
                raise MatchException(trace)
            if is_pattern(pat.fun, list(inst.keys()), bd_vars=[v.name for v in bd_vars]):
                match(pat.fun, t.fun, inst, bd_vars)
                match(pat.arg, t.arg, inst, bd_vars)
            else:
                match(pat.arg, t.arg, inst, bd_vars)
                match(pat.fun, t.fun, inst, bd_vars)
        elif pat.is_abs():
            # When pat is a lambda term, t must also be a lambda term.
            # Replace bound variable by a variable, then match the body.
            if t.is_abs():
                try:
                    pat.var_T.match_incr(t.var_T, inst.tyinst)
                except TypeMatchException:
                    raise MatchException(trace)
                T = pat.var_T.subst(inst.tyinst)

                var_names = [v.name for v in pat.body.get_vars() + t.body.get_vars()]
                nm = name.get_variant_name(pat.var_name, var_names)
                v = Var(nm, T)
                pat_body = pat.subst_type(inst.tyinst).subst_bound(v)
                t_body = t.subst_bound(v)
                match(pat_body, t_body, inst, bd_vars + [v])
            else:
                tT = t.get_type()
                if not tT.is_fun():
                    raise MatchException(trace)
                try:
                    pat.var_T.match_incr(tT.domain_type(), inst.tyinst)
                except TypeMatchException:
                    raise MatchException(trace)
                T = pat.var_T.subst(inst.tyinst)
                match(pat, Abs(pat.var_name, T, t(Bound(0))), inst, bd_vars)
        elif pat.is_bound():
            raise MatchException(trace)
        else:
            raise TypeError

        trace.pop()

    match(pat, t, inst, [])

def first_order_match(pat, t):
    """First-order matching of pat with t. Return the instantiation
    or throws MatchException.

    """
    inst = Inst()
    first_order_match_incr(pat, t, inst)
    return inst

def can_first_order_match_incr(pat, t, inst):
    inst = copy(inst)
    try:
        first_order_match_incr(pat, t, inst)
        return True
    except MatchException:
        return False

def first_order_match_list_incr(pats, ts, inst):
    """First-order matching of a list of pattern-term pairs."""
    if len(pats) == 0:
        return
    
    if len(pats) == 1:
        first_order_match_incr(pats[0], ts[0], inst)
        return

    if is_pattern(pats[0], list(inst.keys())):
        first_order_match_incr(pats[0], ts[0], inst)
        first_order_match_list_incr(pats[1:], ts[1:], inst)
        return
    else:
        first_order_match_list_incr(pats[1:], ts[1:], inst)
        first_order_match_incr(pats[0], ts[0], inst)
        return
