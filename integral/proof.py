"""Proofs for differentiation and integration."""

from kernel import term
from kernel.type import TFun, boolT
from kernel.term import Term, Var, Const
from logic.conv import Conv, ConvException, top_conv, beta_conv, argn_conv, \
    arg_conv, arg1_conv, rewr_conv, binop_conv
from logic.logic import apply_theorem, conj_thms
from logic.proofterm import ProofTermDeriv, refl
from data import set
from data import nat
from data import real
from data.real import realT
from data.integral import netT, within, atreal
from util import name
from syntax import printer


def mk_has_real_derivative(f, g, x, S):
    """Construct the term has_real_derivative f g (within (atreal x) S)."""
    T = TFun(TFun(realT, realT), realT, netT(realT), boolT)
    return Const('has_real_derivative', T)(f, g, within(atreal(x), S))

def mk_has_real_integral(f, x, a, b):
    """Construct the term has_real_integral f x (real_closed_interval a b)."""
    T = TFun(TFun(realT, realT), realT, set.setT(realT), boolT)
    return Const('has_real_integral', T)(f, x, real.closed_interval(a, b))

def mk_real_continuous_on(f, a, b):
    """Construct the term real_continuous_on f (real_closed_interval a b)."""
    T = TFun(TFun(realT, realT), set.setT(realT), boolT)
    return Const('real_continuous_on', T)(f, real.closed_interval(a, b))

def mk_real_integrable_on(f, a, b):
    """Construct the term real_integrable_on f (real_closed_interval a b)."""
    T = TFun(TFun(realT, realT), set.setT(realT), boolT)
    return Const('real_integrable_on', T)(f, real.closed_interval(a, b))

def has_real_derivativeI(thy, f, x, S):
    """Prove a theorem of the form has_real_derivative f f' (within (atreal x) S).
    
    Here f is a function real => real of the form %x. f x, x is
    of type real, and S is of type real set.

    """
    net = within(atreal(x), S)

    if not f.is_abs():
        raise NotImplementedError

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
            return apply_theorem(thy, 'has_real_derivative_add', pt1, pt2)
        elif real.is_minus(t):
            return apply_theorem(thy, 'has_real_derivative_sub', pt1, pt2)
        elif real.is_times(t):
            return apply_theorem(thy, 'has_real_derivative_mul_within', pt1, pt2)
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
            pt1 = has_real_derivativeI(thy, argt, x, S)
            pt2 = apply_theorem(thy, th_name, inst={'x': argt(x), 's': set.mk_image(argt, S)})
            return apply_theorem(thy, 'real_diff_chain_within', pt1, pt2, inst={'f': argt})
        else:
            raise NotImplementedError
    elif t == v:
        return apply_theorem(thy, 'has_real_derivative_id', inst={'net': net})
    elif not t.occurs_var(v):
        return apply_theorem(thy, 'has_real_derivative_const', inst={'c': t, 'net': net})
    else:
        raise NotImplementedError

def has_real_derivative(thy, goal):
    """Prove goal of the form has_real_derivative f f' (within (atreal x) S).

    This is achieved by first using has_real_derivativeI to compute
    some g such that has_real_derivative f g (within (atreal x) S) holds,
    then attempts to derive equation f' = g.

    """
    assert goal.head.is_const_name('has_real_derivative')
    f, f2, net = goal.args
    assert net.head.is_const_name('within')
    atreal_x, S = net.args
    assert atreal_x.head.is_const_name('atreal')
    x = atreal_x.arg

    pt = has_real_derivativeI(thy, f, x, S)
    g = pt.prop.args[1]
    eq_goal = Term.mk_equals(g, f2)
    assert real.real_norm_macro().can_eval(thy, eq_goal), "has_real_derivative"

    eq_pt = ProofTermDeriv('real_norm', thy, eq_goal)
    return pt.on_prop(thy, argn_conv(1, rewr_conv(eq_pt)))

def real_continuous_onI(thy, f, a, b):
    """Prove a theorem of the form real_continuous_on f (real_closed_interval a b).
    
    Here f is a function real => real of the form %x. f x,
    a and b are real numbers. The function can do more if a and b are
    constants.

    """
    if not f.is_abs():
        raise NotImplementedError

    interval = real.closed_interval(a, b)

    var_names = [v.name for v in term.get_vars(f)]
    nm = name.get_variant_name(f.var_name, var_names)
    v = Var(nm, f.var_T)
    t = f.subst_bound(v)

    if t.is_binop() and real.is_real(t.arg1) and real.is_real(t.arg):
        t1 = Term.mk_abs(v, t.arg1)
        t2 = Term.mk_abs(v, t.arg)
        pt1 = real_continuous_onI(thy, t1, a, b)
        pt2 = real_continuous_onI(thy, t2, a, b)
        if real.is_plus(t):
            return apply_theorem(thy, 'real_continuous_on_add', pt1, pt2)
        elif real.is_minus(t):
            return apply_theorem(thy, 'real_continuous_on_sub', pt1, pt2)
        elif real.is_times(t):
            return apply_theorem(thy, 'real_continuous_on_mul', pt1, pt2)
        else:
            raise NotImplementedError
    elif real.is_nat_power(t) and not t.arg.occurs_var(v):
        t1 = Term.mk_abs(v, t.arg1)
        pt1 = real_continuous_onI(thy, t1, a, b)
        return apply_theorem(thy, 'real_continuous_on_pow', pt1, inst={'n': t.arg})
    elif t.is_comb() and real.is_real(t.arg):
        argt = Term.mk_abs(v, t.arg)
        pt = real_continuous_onI(thy, argt, a, b)
        if real.is_uminus(t):
            return apply_theorem(thy, 'real_continuous_on_neg', pt)
        elif t.fun in (real.exp, real.sin, real.cos):
            if t.fun == real.exp:
                th_name = 'real_continuous_on_exp'
            elif t.fun == real.sin:
                th_name = 'real_continuous_on_sin'
            else:
                th_name = 'real_continuous_on_cos'
            pt1 = real_continuous_onI(thy, argt, a, b)
            pt2 = apply_theorem(thy, th_name, inst={'s': set.mk_image(argt, interval)})
            return apply_theorem(thy, 'real_continuous_on_compose', pt1, pt2, inst={'f': argt})
        else:
            raise NotImplementedError
    elif t == v:
        return apply_theorem(thy, 'real_continuous_on_id', inst={'s': interval})
    elif not t.occurs_var(v):
        return apply_theorem(thy, 'real_continuous_on_const', inst={'c': t, 's': interval})
    else:
        raise NotImplementedError

def real_integrable_onI(thy, f, a, b):
    """Prove a theorem of the form real_integrable_on f (real_closed_interval a b).

    Currently, only prove this from continuity of f.

    """
    pt = real_continuous_onI(thy, f, a, b)
    return apply_theorem(thy, 'real_integrable_continuous', pt)

class linearity(Conv):
    """Apply linearity to an integral."""
    def get_proof_term(self, thy, expr):
        if not expr.head.is_const_name('real_integral'):
            raise ConvException

        S, f = expr.args
        if not S.head.is_const_name('real_closed_interval'):
            raise ConvException

        a, b = S.args
        pt = refl(expr)

        if not f.is_abs():
            raise ConvException

        var_names = [v.name for v in term.get_vars(f)]
        nm = name.get_variant_name(f.var_name, var_names)
        v = Var(nm, f.var_T)
        t = f.subst_bound(v)

        if t.is_binop() and real.is_real(t.arg1) and real.is_real(t.arg):
            t1 = Term.mk_abs(v, t.arg1)
            t2 = Term.mk_abs(v, t.arg)
            pt1 = real_integrable_onI(thy, t1, a, b)
            pt2 = real_integrable_onI(thy, t2, a, b)
            if real.is_plus(t):
                return pt.on_rhs(thy, rewr_conv('real_integral_add', conds=[pt1, pt2]), binop_conv(self))
            elif real.is_minus(t):
                return pt.on_rhs(thy, rewr_conv('real_integral_sub', conds=[pt1, pt2]), binop_conv(self))
            elif not t1.occurs_var(v):
                return pt.on_rhs(thy, rewr_conv('real_integral_lmul', conds=[pt2]), arg_conv(self))
            elif not t2.occurs_var(v):
                return pt.on_rhs(thy, rewr_conv('real_integral_rmul', conds=[pt1]), arg1_conv(self))
            else:
                return pt
        elif real.is_uminus(t):
            argt = Term.mk_abs(v, t.arg)
            pt1 = real_integrable_onI(thy, argt, a, b)
            return pt.on_rhs(thy, rewr_conv('real_integral_neg', conds=[pt1]), arg_conv(self))
        else:
            return pt


class common_integral(Conv):
    """Apply common integrals."""
    def get_proof_term(self, thy, expr):
        if not expr.head.is_const_name('real_integral'):
            raise ConvException

        S, f = expr.args
        if not S.head.is_const_name('real_closed_interval'):
            raise ConvException
        a, b = S.args
        pt = refl(expr)

        le_pt = real.real_less_eq(thy, a, b)
        if not f.is_abs():
            raise ConvException

        var_names = [v.name for v in term.get_vars(f)]
        nm = name.get_variant_name(f.var_name, var_names)
        v = Var(nm, f.var_T)
        t = f.subst_bound(v)

        if not t.occurs_var(v):
            return pt.on_rhs(thy, rewr_conv('real_integral_const_evalat', conds=[le_pt]))
        elif t == v:
            return pt.on_rhs(thy, rewr_conv('real_integral_id_evalat', conds=[le_pt]))
        elif real.is_nat_power(t) and not t.arg.occurs_var(v):
            return pt.on_rhs(thy, rewr_conv('real_integral_pow_evalat', conds=[le_pt]))
        elif t.is_comb():
            if t.fun == real.exp:
                return pt.on_rhs(thy, rewr_conv('real_integral_exp_evalat', conds=[le_pt]))
            elif t.fun == real.sin:
                return pt.on_rhs(thy, rewr_conv('real_integral_sin_evalat', conds=[le_pt]))
            elif t.fun == real.cos:
                return pt.on_rhs(thy, rewr_conv('real_integral_cos_evalat', conds=[le_pt]))
            else:
                return pt
        else:
            return pt


class simplify(Conv):
    """Simplify evalat as well as arithmetic."""
    def get_proof_term(self, thy, t):
        return refl(t).on_rhs(
            thy,
            top_conv(rewr_conv('evalat_def')),
            top_conv(beta_conv()),
            real.real_norm_conv())
