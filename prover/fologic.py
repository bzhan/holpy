"""Utilities for first-order logic.

References:
Chapter 3, Handbook of Practical Logic and Automated Reasoning.
"""

from kernel.type import TFun
from kernel import term
from kernel.term import Term, Var, Abs
from logic import logic
from util import name

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
        return simplify1(logic.neg(simplify(fm.arg)))
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

def skolem(fm):
    """Skolemize the formula. Assume the formula is already in nnf."""
    var_names = [v.name for v in term.get_vars(fm)]

    def rec(t):
        if logic.is_exists(t):
            # Obtain the list of variables that t depends on, not
            # counting functions (including skolem functions).
            xs = [v for v in term.get_vars(t.arg.body) if not v.T.is_fun()]

            # Obtain the new skolem variable.
            nm = "c_" + t.arg.var_name if len(xs) == 0 else "f_" + t.arg.var_name
            nm = name.get_variant_name(nm, var_names)
            var_names.append(nm)

            # Obtain the concrete instantiation of the skolem variable.
            T = TFun(*([x.T for x in xs] + [t.arg.var_T]))
            f = Var(nm, T)(*xs)
            return rec(t.arg.subst_bound(f))
        elif Term.is_all(t):
            nm = name.get_variant_name(t.arg.var_name, var_names)
            var_names.append(nm)
            v = Var(nm, t.arg.var_T)
            body = t.arg.subst_bound(v)
            return Term.mk_all(v, rec(body))
        elif logic.is_conj(t) or logic.is_disj(t):
            return t.head(rec(t.arg1), rec(t.arg))
        else:
            return t

    return rec(fm)

def askolemize(fm):
    """Perform simplify, nnf, and skolem transformations."""
    return skolem(nnf(simplify(fm)))
