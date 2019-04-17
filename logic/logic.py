# Author: Bohua Zhan

from kernel.type import TVar, TFun, boolT
from kernel.term import Term, Var, Const, Abs
from logic.conv import Conv, then_conv, all_conv, arg_conv, binop_conv, rewr_conv
from logic.proofterm import ProofTerm, refl

"""Utility functions for logic."""


conj = Const("conj", TFun(boolT, boolT, boolT))
disj = Const("disj", TFun(boolT, boolT, boolT))
neg = Const("neg", TFun(boolT, boolT))
true = Const("true", boolT)
false = Const("false", boolT)
    
def is_conj(t):
    """Whether t is of the form A & B."""
    return t.is_binop() and t.head == conj

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
    return t.is_binop() and t.head == disj

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

def mk_exists(x, body):
    """Given a variable x and a term t possibly depending on x, return
    the term ?x. t.

    """
    exists_t = Const("exists", TFun(TFun(x.T, boolT), boolT))
    return exists_t(Term.mk_abs(x, body))

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
        return Abs(t.var_name, t.var_T, beta_norm(t.body))
    elif t.ty == Term.BOUND:
        return t
    else:
        raise TypeError()

def subst_norm(t, instsp):
    """Substitute using the given instantiation, then normalize with
    respect to beta-conversion.

    """
    tyinst, inst = instsp
    return beta_norm(t.subst_type(tyinst).subst(inst))

def if_t(T):
    return Const("IF", TFun(boolT, T, T, T))

def is_if(t):
    """Whether t is of the form if P then x else y."""
    f, args = t.strip_comb()
    return f.is_const_name("IF") and len(args) == 3

def mk_if(P, x, y):
    """Obtain the term if P then x else y."""
    return if_t(x.get_type())(P, x, y)

def strip_all_implies(t, names):
    """Given a term of the form

    !x_1 ... x_k. A_1 --> ... --> A_n --> C.

    Return the triple ([v_1, ..., v_k], [A_1, ... A_n], C), where
    v_1, ..., v_k are new variables with the given names, and
    A_1, ..., A_n, C are the body of the input term, with bound variables
    substituted for v_1, ..., v_k.

    """
    if Term.is_all(t):
        assert len(names) > 0, "strip_all_implies: not enough names input."
        v = Var(names[0], t.arg.var_T)
        vars, As, C = strip_all_implies(t.arg.subst_bound(v), names[1:])
        return ([v] + vars, As, C)
    else:
        assert len(names) == 0, "strip_all_implies: too many names input."
        As, C = t.strip_implies()
        return ([], As, C)


"""Normalization rules for logic."""

class norm_bool_expr(Conv):
    """Normalize a boolean expression."""
    def get_proof_term(self, thy, t):
        if is_neg(t):
            if t.arg == true:
                return rewr_conv("not_true").get_proof_term(thy, t)
            elif t.arg == false:
                return rewr_conv("not_false").get_proof_term(thy, t)
            else:
                return refl(t)
        else:
            return refl(t)

class norm_conj_assoc_clauses(Conv):
    """Normalize (A_1 & ... & A_n) & (B_1 & ... & B_n)."""
    def get_proof_term(self, thy, t):
        if is_conj(t.arg1):
            return then_conv(
                rewr_conv("conj_assoc", sym=True),
                arg_conv(norm_conj_assoc_clauses())
            ).get_proof_term(thy, t)
        else:
            return all_conv().get_proof_term(thy, t)

class norm_conj_assoc(Conv):
    """Normalize conjunction with respect to associativity."""
    def get_proof_term(self, thy, t):
        if is_conj(t):
            return then_conv(
                binop_conv(norm_conj_assoc()),
                norm_conj_assoc_clauses()
            ).get_proof_term(thy, t)
        else:
            return all_conv().get_proof_term(thy, t)
