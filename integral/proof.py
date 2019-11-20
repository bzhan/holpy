"""Proofs for differentiation and integration."""

from kernel import term
from kernel.term import Term, Var
from logic.logic import apply_theorem, conj_thms
from data import real
from data.integral import within, atreal
from util import name
from syntax import printer


def has_real_derivativeI(thy, f, x, S):
    """Prove a theorem of the form has_real_derivative f f' (within (atreal x) s).
    
    Here f is a function real => real of the form %x. f x, x is
    of type real, and S is of type real set.

    """
    net = within(atreal(x), S)

    if f.is_abs():
        var_names = [v.name for v in term.get_vars(f)]
        nm = name.get_variant_name(f.var_name, var_names)
        v = Var(nm, f.var_T)
        t = f.subst_bound(v)
        if t.is_binop():
            t1 = Term.mk_abs(v, t.arg1)
            t2 = Term.mk_abs(v, t.arg)
            pt1 = has_real_derivativeI(thy, t1, x, S)
            pt2 = has_real_derivativeI(thy, t2, x, S)
            if real.is_plus(t):
                return apply_theorem(thy, 'has_real_derivative_add', conj_thms(thy, pt1, pt2))
            elif real.is_minus(t):
                return apply_theorem(thy, 'has_real_derivative_sub', conj_thms(thy, pt1, pt2))
            elif real.is_times(t):
                return apply_theorem(thy, 'has_real_derivative_mul_within', conj_thms(thy, pt1, pt2))
            else:
                raise NotImplementedError
        elif t.is_comb() and t.arg.get_type() == real.realT:
            argt = Term.mk_abs(v, t.arg)
            pt = has_real_derivativeI(thy, argt, x, S)
            if real.is_uminus(t):
                return apply_theorem(thy, 'has_real_derivative_neg', pt)
            else:
                raise NotImplementedError
        elif t == v:
            return apply_theorem(thy, 'has_real_derivative_id', inst={'net': net})
        elif not t.occurs_var(v):
            return apply_theorem(thy, 'has_real_derivative_const', inst={'c': t, 'net': net})
        else:
            raise NotImplementedError
    else:
        raise NotImplementedError
