"""Utilities for first-order logic.

References:
Chapter 3, Handbook of Practical Logic and Automated Reasoning.
"""

from kernel.type import TFun
from kernel import term
from kernel.term import Term, Var, Abs, And, Or, Implies, Not, false, true
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
    if fm.is_not():
        if fm.arg == false:
            return true
        elif fm.arg == true:
            return false
        elif fm.arg.is_not():
            return fm.arg.arg
        else:
            return fm
    elif fm.is_conj():
        if fm.arg1 == false or fm.arg == false:
            return false
        elif fm.arg1 == true:
            return fm.arg
        elif fm.arg == true:
            return fm.arg1
        else:
            return fm
    elif fm.is_disj():
        if fm.arg1 == true or fm.arg == true:
            return true
        elif fm.arg1 == false:
            return fm.arg
        elif fm.arg == false:
            return fm.arg1
        else:
            return fm
    elif fm.is_implies():
        if fm.arg1 == false or fm.arg == true:
            return true
        elif fm.arg1 == true:
            return fm.arg
        elif fm.arg == false:
            return Not(fm.arg1)
        else:
            return fm
    elif fm.is_equals():
        if fm.arg1 == true:
            return fm.arg
        elif fm.arg == true:
            return fm.arg1
        elif fm.arg1 == false:
            return Not(fm.arg)
        elif fm.arg == false:
            return Not(fm.arg1)
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
    if fm.is_not():
        return simplify1(Not(simplify(fm.arg)))
    elif fm.is_conj() or fm.is_disj() or fm.is_implies() or fm.is_equals():
        return simplify1(fm.head(simplify(fm.arg1), simplify(fm.arg)))
    elif Term.is_all(fm) or logic.is_exists(fm):
        assert fm.arg.is_abs()
        return simplify1(fm.fun(Abs(fm.arg.var_name, fm.arg.var_T, simplify(fm.arg.body))))
    else:
        return fm

def nnf(fm):
    """Negation normal form of a formula."""
    if fm.is_conj():
        return And(nnf(fm.arg1), nnf(fm.arg))
    elif fm.is_disj():
        return Or(nnf(fm.arg1), nnf(fm.arg))
    elif fm.is_implies():
        return Or(nnf(Not(fm.arg1)), nnf(fm.arg))
    elif fm.is_equals():
        return Or(And(nnf(fm.arg1), nnf(fm.arg)),
                  And(nnf(Not(fm.arg1)), nnf(Not(fm.arg))))
    elif fm.is_not():
        p = fm.arg
        if p.is_not():
            return nnf(p.arg)
        elif p.is_conj():
            return Or(nnf(Not(p.arg1)), nnf(Not(p.arg)))
        elif p.is_disj():
            return And(nnf(Not(p.arg1)), nnf(Not(p.arg)))
        elif p.is_implies():
            return And(nnf(p.arg1), nnf(Not(p.arg)))
        elif p.is_equals():
            return Or(And(nnf(p.arg1), nnf(Not(p.arg))),
                      And(nnf(Not(p.arg1)), nnf(p.arg)))
        elif Term.is_all(p):
            assert p.arg.is_abs()
            exists_t = logic.exists_t(p.arg.var_T)
            return exists_t(Abs(p.arg.var_name, p.arg.var_T, nnf(Not(p.arg.body))))
        elif logic.is_exists(p):
            assert p.arg.is_abs()
            all_t = term.all_t(p.arg.var_T)
            return all_t(Abs(p.arg.var_name, p.arg.var_T, nnf(Not(p.arg.body))))
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
        elif t.is_conj() or t.is_disj():
            return t.head(rec(t.arg1), rec(t.arg))
        else:
            return t

    return rec(fm)

def askolemize(fm):
    """Perform simplify, nnf, and skolem transformations."""
    return skolem(nnf(simplify(fm)))
