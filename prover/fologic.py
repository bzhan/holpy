"""Utilities for first-order logic.

References:
Chapter 3, Handbook of Practical Logic and Automated Reasoning.
"""

from kernel import term
from kernel.term import Term, Var, Abs
from logic import logic

def has_bound0(fm):
    """Determine whether the bound variable of the given abstraction
    appears in the body.

    """
    def rec(t, n):
        if t.is_var() or t.is_const():
            return False
        elif t.is_comb():
            return rec(t.fun, n) or rec(t.arg, n)
        elif t.is_abs():
            return rec(t.body, n+1)
        elif t.is_bound():
            return t.n == n
        else:
            raise TypeError
    return rec(fm, 0)

def simplify1(fm):
    """Simplify formula for one step."""
    if logic.is_neg(fm):
        if fm.arg == logic.false:
            return logic.true
        elif fm.arg == logic.true:
            return logic.false
        elif logic.is_neg(fm.arg):
            return fm.arg.arg
        else:
            return fm
    elif logic.is_conj(fm):
        if fm.arg1 == logic.false or fm.arg == logic.false:
            return logic.false
        elif fm.arg1 == logic.true:
            return fm.arg
        elif fm.arg == logic.true:
            return fm.arg1
        else:
            return fm
    elif logic.is_disj(fm):
        if fm.arg1 == logic.true or fm.arg == logic.true:
            return logic.true
        elif fm.arg1 == logic.false:
            return fm.arg
        elif fm.arg == logic.false:
            return fm.arg1
        else:
            return fm
    elif Term.is_implies(fm):
        if fm.arg1 == logic.false or fm.arg == logic.true:
            return logic.true
        elif fm.arg1 == logic.true:
            return fm.arg
        elif fm.arg == logic.false:
            return logic.neg(fm.arg1)
        else:
            return fm
    elif Term.is_equals(fm):
        if fm.arg1 == logic.true:
            return fm.arg
        elif fm.arg == logic.true:
            return fm.arg1
        elif fm.arg1 == logic.false:
            return logic.neg(fm.arg)
        elif fm.arg == logic.false:
            return logic.neg(fm.arg1)
        else:
            return fm
    elif Term.is_all(fm) or logic.is_exists(fm):
        if has_bound0(fm.arg.body):
            return fm
        else:
            return fm.arg.subst_bound(Var("_u", fm.arg.var_T))
    else:
        return fm

def simplify(fm):
    """Simplify formula.
    
    Remove true, false, and vacuous forall/exists quantification.

    """
    if logic.is_neg(fm):
        return simplify1(logic.mk_neg(simplify(fm.arg)))
    elif logic.is_conj(fm) or logic.is_disj(fm) or Term.is_implies(fm) or Term.is_equals(fm):
        return simplify1(fm.head(simplify(fm.arg1), simplify(fm.arg)))
    elif Term.is_all(fm) or logic.is_exists(fm):
        assert fm.arg.is_abs()
        return simplify1(fm.fun(Abs(fm.arg.var_name, fm.arg.var_T, simplify(fm.arg.body))))
    else:
        return fm

def nnf(fm):
    """Negation normal form of a formula."""
    if logic.is_conj(fm):
        return logic.mk_conj(nnf(fm.arg1), nnf(fm.arg))
    elif logic.is_disj(fm):
        return logic.mk_disj(nnf(fm.arg1), nnf(fm.arg))
    elif Term.is_implies(fm):
        return logic.mk_disj(nnf(logic.neg(fm.arg1)), nnf(fm.arg))
    elif Term.is_equals(fm):
        return logic.mk_disj(logic.mk_conj(nnf(fm.arg1), nnf(fm.arg)),
                             logic.mk_conj(nnf(logic.neg(fm.arg1)), nnf(logic.neg(fm.arg))))
    elif logic.is_neg(fm):
        p = fm.arg
        if logic.is_neg(p):
            return nnf(p.arg)
        elif logic.is_conj(p):
            return logic.mk_disj(nnf(logic.neg(p.arg1)), nnf(logic.neg(p.arg)))
        elif logic.is_disj(p):
            return logic.mk_conj(nnf(logic.neg(p.arg1)), nnf(logic.neg(p.arg)))
        elif Term.is_implies(p):
            return logic.mk_conj(nnf(p.arg1), nnf(logic.neg(p.arg)))
        elif Term.is_equals(p):
            return logic.mk_disj(logic.mk_conj(nnf(p.arg1), nnf(logic.neg(p.arg))),
                                 logic.mk_conj(nnf(logic.neg(p.arg1)), nnf(p.arg)))
        elif Term.is_all(p):
            assert p.arg.is_abs()
            exists_t = logic.exists_t(p.arg.var_T)
            return exists_t(Abs(p.arg.var_name, p.arg.var_T, nnf(logic.neg(p.arg.body))))
        elif logic.is_exists(p):
            assert p.arg.is_abs()
            all_t = term.all_t(p.arg.var_T)
            return all_t(Abs(p.arg.var_name, p.arg.var_T, nnf(logic.neg(p.arg.body))))
        else:
            return fm
    elif Term.is_all(fm) or logic.is_exists(fm):
        assert fm.arg.is_abs()
        return fm.fun(Abs(fm.arg.var_name, fm.arg.var_T, nnf(fm.arg.body)))
    else:
        return fm
