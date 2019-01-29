# Author: Bohua Zhan

from kernel.type import TFun, hol_bool
from kernel.term import Term, Const, Abs

"""Utility functions for logic."""

conj = Const("conj", TFun(hol_bool, hol_bool, hol_bool))
disj = Const("disj", TFun(hol_bool, hol_bool, hol_bool))
neg = Const("neg", TFun(hol_bool, hol_bool))
true = Const("true", hol_bool)
false = Const("false", hol_bool)
    
def is_conj(t):
    """Whether t is of the form A & B."""
    return t.is_binop() and t.get_head() == conj

def mk_conj(*args):
    """Construct the term s1 & ... & sn."""
    if args:
        assert isinstance(args[0], Term), "mk_conj: each argument must be a term"
        if len(args) > 1:
            return conj(args[0], mk_conj(*args[1:]))
        else:
            return args[0]
    else:
        return true

def strip_conj(t):
    """Given term of the form s1 & ... & sn, return the list
    [s1, ..., sn].

    """
    if is_conj(t):
        return [t.arg1] + strip_conj(t.arg)
    else:
        return [t]

def is_disj(t):
    """Whether t is of the form A | B."""
    return t.is_binop() and t.get_head() == disj

def mk_disj(*args):
    """Construct the term s1 | ... | sn."""
    if args:
        assert isinstance(args[0], Term), "mk_disj: each argument must be a term"
        if len(args) > 1:
            return disj(args[0], mk_disj(*args[1:]))
        else:
            return args[0]
    else:
        return false

def strip_disj(t):
    """Given term of the form s1 | ... | sn, return the list
    [s1, ..., sn].

    """
    if is_disj(t):
        return [t.arg1] + strip_disj(t.arg)
    else:
        return [t]

def is_neg(t):
    """Whether t is of the form ~ A."""
    return t.ty == Term.COMB and t.fun == neg

def is_exists(t):
    """Whether t is of the form ?x. P x."""
    return t.ty == Term.COMB and t.fun.ty == Term.CONST and \
        t.fun.name == "exists" and t.arg.ty == Term.ABS

def mk_exists(x, body, *, var_name = None, T = None):
    """Given a variable x and a term t possibly depending on x, return
    the term ?x. t.

    """
    if T is None:
        T = x.T

    exists_t = Const("exists", TFun(TFun(T, hol_bool), hol_bool))
    return exists_t(Term.mk_abs(x, body, var_name = var_name, T = T))

def beta_norm(t):
    """Normalize t using beta-conversion."""
    if t.ty == Term.VAR or t.ty == Term.CONST:
        return t
    elif t.ty == Term.COMB:
        f = beta_norm(t.fun)
        x = beta_norm(t.arg)
        if f.ty == Term.ABS:
            return f(x).beta_conv()
        else:
            return f(x)
    elif t.ty == Term.ABS:
        return Abs(t.var_name, t.T, beta_norm(t.body))
    elif t.ty == Term.BOUND:
        return t
    else:
        raise TypeError()

def subst_norm(t, inst):
    """Substitute using the given instantiation, then normalize with
    respect to beta-conversion.

    """
    return beta_norm(t.subst(inst))
