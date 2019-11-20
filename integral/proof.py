"""Proofs for differentiation and integration."""

from kernel import term
from kernel.term import Term, Var
from logic.conv import top_conv
from logic.logic import apply_theorem, conj_thms
from data import set
from data import nat
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
        if t.is_binop() and real.is_real(t.arg1) and real.is_real(t.arg):
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
        elif real.is_nat_power(t) and nat.is_binary_nat(t.arg) and nat.from_binary_nat(t.arg) > 0:
            t1 = Term.mk_abs(v, t.arg1)
            pt1 = has_real_derivativeI(thy, t1, x, S)
            return apply_theorem(thy, 'has_real_derivative_pow_within', pt1, inst={'n': t.arg})
        elif t.is_comb() and real.is_real(t.arg):
            argt = Term.mk_abs(v, t.arg)
            pt = has_real_derivativeI(thy, argt, x, S)
            if real.is_uminus(t):
                return apply_theorem(thy, 'has_real_derivative_neg', pt)
            elif t.fun in (real.exp, real.sin, real.cos):
                if t.fun == real.exp:
                    th_name = 'has_real_derivative_exp_within'
                elif t.fun == real.sin:
                    th_name = 'has_real_derivative_sin_within'
                else:
                    th_name = 'has_real_derivative_cos_within'
                f = Term.mk_abs(v, t.arg)
                pt1 = has_real_derivativeI(thy, f, x, S)
                pt2 = apply_theorem(thy, th_name, inst={'x': f(x), 's': set.mk_image(f, S)})
                return apply_theorem(thy, 'real_diff_chain_within', conj_thms(thy, pt1, pt2), inst={'f': f})
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
