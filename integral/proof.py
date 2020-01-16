"""Proofs for differentiation and integration."""

import math

from kernel import term
from kernel.type import TFun, boolT
from kernel.term import Term, Var, Const
from kernel.thm import Thm
from kernel import macro
from logic.conv import Conv, ConvException, top_conv, beta_conv, beta_norm_conv, argn_conv, \
    arg_conv, arg1_conv, rewr_conv, binop_conv, abs_conv, every_conv, try_conv
from logic.logic import apply_theorem, conj_thms
from logic import auto
from logic import logic
from logic.proofterm import ProofTerm, ProofTermDeriv, ProofTermMacro, refl
from logic.context import Context
from data import set
from data import nat
from data import real
from data.real import realT
from data.integral import netT, within, atreal
from util import name
from prover import z3wrapper
from syntax import printer
from integral.expr import Expr, Location
import integral


evalat = Const('evalat', TFun(TFun(realT, realT), realT, realT, realT))

def mk_has_real_derivative(f, g, x, S):
    """Construct the term has_real_derivative f g (within (atreal x) S)."""
    T = TFun(TFun(realT, realT), realT, netT(realT), boolT)
    return Const('has_real_derivative', T)(f, g, within(atreal(x), S))

def mk_has_real_integral(f, x, a, b):
    """Construct the term has_real_integral f x (real_closed_interval a b)."""
    T = TFun(TFun(realT, realT), realT, set.setT(realT), boolT)
    return Const('has_real_integral', T)(f, x, real.closed_interval(a, b))

def mk_real_integral(f, a, b):
    T = TFun(set.setT(realT), TFun(realT, realT), realT)
    return Const('real_integral', T)(real.closed_interval(a, b), f)

def mk_real_continuous_on(f, a, b):
    """Construct the term real_continuous_on f (real_closed_interval a b)."""
    T = TFun(TFun(realT, realT), set.setT(realT), boolT)
    return Const('real_continuous_on', T)(f, real.closed_interval(a, b))

def mk_real_integrable_on(f, a, b):
    """Construct the term real_integrable_on f (real_closed_interval a b)."""
    T = TFun(TFun(realT, realT), set.setT(realT), boolT)
    return Const('real_integrable_on', T)(f, real.closed_interval(a, b))

def mk_real_increasing_on(f, a, b):
    """Construct the term real_increasing_on f (real_closed_interval a b)."""
    T = TFun(TFun(realT, realT), set.setT(realT), boolT)
    return Const('real_increasing_on', T)(f, real.closed_interval(a, b))
    
def mk_real_decreasing_on(f, a, b):
    """Construct the term real_decreasing_on f (real_closed_interval a b)."""
    T = TFun(TFun(realT, realT), set.setT(realT), boolT)
    return Const('real_decreasing_on', T)(f, real.closed_interval(a, b))

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
    if not t.occurs_var(v):
        return apply_theorem(thy, 'has_real_derivative_const', inst={'c': t, 'net': net})
    elif t.is_binop() and real.is_real(t.arg1) and real.is_real(t.arg):
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
            print(printer.print_term(thy, t))
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

# Introduction rules for real_continuous_on
auto.add_global_autos(
    Const('real_continuous_on', TFun(TFun(realT, realT), set.setT(realT), boolT)),
    auto.solve_rules([
        # Continuous everywhere
        "real_continuous_on_const",
        "real_continuous_on_id",
        "real_continuous_on_add",
        "real_continuous_on_neg",
        "real_continuous_on_sub",
        "real_continuous_on_mul",
        "real_continuous_on_pow",
        "real_continuous_on_exp",
        "real_continuous_on_exp_compose",
        "real_continuous_on_sin",
        "real_continuous_on_sin_compose",
        "real_continuous_on_cos",
        "real_continuous_on_cos_compose",
        "real_continuous_on_abs",

        # Continuous with conditions
        "real_continuous_on_div",
        "real_continuous_on_log",
        "real_continuous_on_log_compose",
        "real_continuous_on_sqrt",
        "real_continuous_on_sqrt_compose",

        # Real power (two options)
        "real_continuous_on_real_pow",
        "real_continuous_on_real_pow2",
    ])
)

auto.add_global_autos(
    Const('real_integrable_on', TFun(TFun(realT, realT), set.setT(realT), boolT)),
    auto.solve_rules([
        "real_integrable_continuous"
    ])
)

auto.add_global_autos_norm(
    real.sin,
    auto.norm_rules([
        'real_sin_0',
        'real_sin_pi6',
        'real_sin_pi4',
        'real_sin_pi3',
        'real_sin_pi2_alt',
        'real_sin_pi',
    ])
)

auto.add_global_autos_norm(
    real.cos,
    auto.norm_rules([
        'real_cos_0',
        'real_cos_pi6',
        'real_cos_pi4',
        'real_cos_pi3',
        'real_cos_pi2_alt',
        'real_cos_pi',
    ])
)

auto.add_global_autos_norm(
    real.exp,
    auto.norm_rules([
        'real_exp_0',
    ])
)

auto.add_global_autos_norm(
    real.abs,
    auto.norm_rules([
        'real_abs_pos_eq',
        'real_abs_neg_eq',
    ])
)

def real_integrable_onI(thy, f, a, b):
    """Prove a theorem of the form real_integrable_on f (real_closed_interval a b).

    Currently, only prove this from continuity of f.

    """
    return auto.auto_solve(thy, mk_real_integrable_on(f, a, b))

class real_ineq_on_interval_macro(ProofTermMacro):
    """Given a term t(x) and assumption of the form x : real_closed_interval a b,
    attempt to prove t(x) >= 0, t(x) <= 0, or t(x) != 0.
    
    """
    def __init__(self):
        self.level = 0  # proof term not implemented
        self.sig = Term
        self.limit = 'real_neg_0'

    def can_eval(self, thy, goal, pts):
        assert len(pts) == 1, "real_ineq_on_interval"
        pt = pts[0]
        assert pt.prop.head.is_const_name("member") and pt.prop.arg1.is_var(), "real_ineq_on_interval"
        var, interval = pt.prop.args
        assert interval.head.is_const_name("real_closed_interval"), "real_ineq_on_interval"
        a, b = interval.args

        approx_a, approx_b = real.real_approx_eval(a), real.real_approx_eval(b)
        if goal.head.is_const_name("greater_eq") and goal.arg == real.zero:
            f = goal.arg1
            if f == real.sin(var):
                if approx_a >= 0.0 and approx_b <= math.pi:
                    return True
                return False
            elif f == real.cos(var):
                if approx_a >= -math.pi / 2 and approx_b <= math.pi / 2:
                    return True
                return False
            else:
                return False
        elif goal.head.is_const_name("less_eq") and goal.arg == real.zero:
            f = goal.arg1
            if f == real.sin(var):
                if approx_a >= -math.pi and approx_b <= 0:
                    return True
                return False
            elif f == real.cos(var):
                if approx_a >= math.pi / 2 and approx_b <= 3 * math.pi / 2:
                    return True
                return False
            else:
                return False
        elif goal.head == logic.neg and goal.arg.is_equals() and goal.arg.arg == real.zero:
            f = goal.arg.arg1
            if f == real.sin(var):
                if approx_a > 0.0 and approx_b < math.pi:
                    return True
                return False
            else:
                return False
        else:
            raise NotImplementedError

        return True

    def eval(self, thy, goal, pts):
        assert len(pts) == 1, "real_nonneg_on_interval"
        assert self.can_eval(thy, goal, pts), "real_nonneg_on_interval"

        return Thm(pts[0].hyps, goal)


def real_increasing_onI(thy, f, a, b):
    """Prove a theorem of the form real_increasing_on f (real_closed_interval a b).

    Currently invokes the SMT solver.

    """
    var_names = [v.name for v in term.get_vars(f)]
    nm = name.get_variant_name(f.var_name, var_names)
    v = Var(nm, f.var_T)
    t = f.subst_bound(v)
    if t == real.sin(v) and a == real.zero and b == real.divides(real.pi, real.to_binary_real(2)):
        return apply_theorem(thy, 'real_increasing_on_sin')

    return z3wrapper.apply_z3(thy, mk_real_increasing_on(f, a, b))

def real_decreasing_onI(thy, f, a, b):
    """Prove a theorem of the form real_decreasing_on f (real_closed_interval a b).

    Currently invokes the SMT solver.

    """
    var_names = [v.name for v in term.get_vars(f)]
    nm = name.get_variant_name(f.var_name, var_names)
    v = Var(nm, f.var_T)
    t = f.subst_bound(v)
    if t == real.cos(v) and a == real.zero and b == real.divides(real.pi, real.to_binary_real(2)):
        return apply_theorem(thy, 'real_decreasing_on_cos_div2')
    elif t == real.cos(v) and a == real.zero and b == real.pi:
        return apply_theorem(thy, 'real_decreasing_on_cos')

    return z3wrapper.apply_z3(thy, mk_real_decreasing_on(f, a, b))

class linearity(Conv):
    """Apply linearity to an integral."""
    def get_proof_term(self, thy, expr):
        if not (expr.head.is_const_name('real_integral') and len(expr.args) == 2):
            raise ConvException("linearity")

        S, f = expr.args
        if not S.head.is_const_name('real_closed_interval'):
            raise ConvException("linearity")

        a, b = S.args
        pt = refl(expr)

        if not f.is_abs():
            raise ConvException("linearity")

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
            elif real.is_times(t) and not t1.occurs_var(v):
                return pt.on_rhs(thy, rewr_conv('real_integral_lmul', conds=[pt2]), arg_conv(self))
            elif real.is_times(t) and not t2.occurs_var(v):
                return pt.on_rhs(thy, rewr_conv('real_integral_rmul', conds=[pt1]), arg1_conv(self))
            elif real.is_divides(t) and real.is_binary_real(t.arg) and real.from_binary_real(t.arg) != 0:
                neq_zero = real.real_ineq(thy, t.arg, real.zero)
                return pt.on_rhs(thy, rewr_conv('real_integral_div', conds=[pt1, neq_zero]), arg_conv(self))
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
        if not (expr.head.is_const_name('real_integral') and len(expr.args) == 2):
            raise ConvException('common_integral')

        S, f = expr.args
        if not S.head.is_const_name('real_closed_interval'):
            raise ConvException('common_integral')
        a, b = S.args
        pt = refl(expr)

        le_pt = real.real_less_eq(thy, a, b)
        if not f.is_abs():
            raise ConvException('common_integral')

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
        elif real.is_divides(t) and real.is_nat_power(t.arg) and nat.from_binary_nat(t.arg.arg) > 1 and \
             real.is_const_less(thy, real.zero, a):
            return pt.on_rhs(thy, rewr_conv('real_integral_inverse_pow_evalat_pos',
                             conds=[le_pt, real.real_less(thy, real.zero, a), nat.nat_less(thy, nat.one, t.arg.arg)]))
        elif real.is_real_power(t) and real.is_binary_real(t.arg):
            if real.from_binary_real(t.arg) != -1:
                return pt.on_rhs(thy, rewr_conv('real_integral_real_pow_evalat',
                                 conds=[le_pt, real.real_ineq(thy, t.arg, real.to_binary_real(-1))]))
            elif real.is_binary_real(a) and real.from_binary_real(a) > 0:
                return pt.on_rhs(thy, rewr_conv('real_integral_inverse_pos_evalat',
                                 conds=[le_pt, real.real_less(thy, real.zero, a)]))
            elif real.is_binary_real(b) and real.from_binary_real(b) < 0:
                return pt.on_rhs(thy, rewr_conv('real_integral_inverse_neg_evalat',
                                 conds=[le_pt, real.real_less(thy, b, real.zero)]))
            else:
                return pt
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


class simplify_TR4(Conv):
    """Simplification of special angles."""
    def __init__(self):
        self.simplify_list = [
            'real_exp_0',
            'real_sin_0',
            'real_sin_pi6',
            'real_sin_pi4',
            'real_sin_pi3',
            'real_sin_pi2_alt',
            'real_sin_pi',
            'real_cos_0',
            'real_cos_pi6',
            'real_cos_pi4',
            'real_cos_pi3',
            'real_cos_pi2_alt',
            'real_cos_pi',
        ]

    def get_proof_term(self, thy, t):
        if not t.head in (real.sin, real.cos, real.exp):
            raise ConvException("simplify_TR4")

        pt = refl(t)
        pt = pt.on_rhs(thy, arg_conv(real.real_norm_conv()))
        for th_name in self.simplify_list:
            pt = pt.on_rhs(thy, try_conv(rewr_conv(th_name)))

        return pt

class simplify_body(Conv):
    """Simplify body of integral."""
    def get_proof_term(self, thy, expr):
        if not (expr.head.is_const_name('real_integral') and len(expr.args) == 2):
            raise ConvException("simplify_body")

        if not expr.arg.is_abs():
            raise ConvException("simplify_body")

        return arg_conv(abs_conv(real.real_norm_conv())).get_proof_term(thy, expr)

class simplify(Conv):
    """Simplify evalat as well as arithmetic."""
    def get_proof_term(self, thy, t):
        return refl(t).on_rhs(
            thy,
            top_conv(rewr_conv('evalat_def')),
            beta_norm_conv(),
            top_conv(simplify_TR4()),
            top_conv(rewr_conv('pow_2_sqrt_abs_alt')),
            real.real_norm_conv(),
            top_conv(simplify_body()))


class integrate_by_parts(Conv):
    """Evaluate using integration by parts.
    
    expr is of the form real_integral (real_closed_interval a b) (%x. u x * dv x),
    where a and b are constant real numbers.

    u and v are both real => real functions in abstraction form, such that the
    derivative of u is du, and the derivative of v is dv.

    The result is evalat (%x. u x * v x) a b - real_integral (real_closed_interval a b) (%x. u x * dv x).

    """
    def __init__(self, u, v):
        self.u = u
        self.v = v

    def get_proof_term(self, thy, expr):
        assert expr.head.is_const_name('real_integral')
        S, f = expr.args
        assert S.head.is_const_name('real_closed_interval')
        a, b = S.args

        le_pt = real.real_less_eq(thy, a, b)

        if not (f.is_abs() and self.u.is_abs() and self.v.is_abs()):
            raise NotImplementedError

        # Form the assumption: derivatives of u and v
        var_names = [v.name for v in term.get_vars(expr)]
        nm = name.get_variant_name(f.var_name, var_names)
        x = Var(nm, f.var_T)

        u_deriv = has_real_derivativeI(thy, self.u, x, S)
        u_deriv = u_deriv.on_prop(thy, argn_conv(1, real.real_norm_conv()))
        v_deriv = has_real_derivativeI(thy, self.v, x, S)
        v_deriv = v_deriv.on_prop(thy, argn_conv(1, real.real_norm_conv()))
        x_mem = set.mk_mem(x, S)
        cond_pt = ProofTerm.forall_intr(x, ProofTerm.implies_intr(x_mem, conj_thms(thy, u_deriv, v_deriv)))

        # Apply the theorem
        eq_pt = apply_theorem(thy, 'real_integration_by_parts_simple_evalat', le_pt, cond_pt)
        eq_pt = eq_pt.on_lhs(thy, arg_conv(abs_conv(real.real_norm_conv())))
        eq_pt = eq_pt.on_rhs(thy, arg_conv(arg_conv(abs_conv(real.real_norm_conv()))))

        pt = refl(expr)
        pt = pt.on_rhs(thy, arg_conv(abs_conv(real.real_norm_conv())))
        pt = pt.on_rhs(thy, rewr_conv(eq_pt))
        return pt


def apply_subst_thm(thy, f, g, a, b):
    """Apply the substitution theorem.

    The returned result is (in the increasing case)
    real_integral (real_closed_interval a b) (%x. f (g x) * dg x) =
    real_integral (real_closed_interval (g a) (g b)) f,

    where both f (g x) * dg x and f are normalized.

    """
    # Form the assumption: a <= b
    le_pt = real.real_less_eq(thy, a, b)

    # Form the assumption: f is continuous on [g(a), g(b)]
    cont_f_pt = auto.auto_solve(thy, mk_real_continuous_on(f, g(a).beta_conv(), g(b).beta_conv()))

    # Form the assumption: derivative of g
    x = Var(g.var_name, realT)

    S = real.closed_interval(a, b)
    g_deriv = has_real_derivativeI(thy, g, x, S)
    x_mem = set.mk_mem(x, S)
    dg_pt = ProofTerm.forall_intr(x, ProofTerm.implies_intr(x_mem, g_deriv))

    # Form the assumption: g is increasing or decreasing on [a, b],
    # then apply the theorem.
    if real.real_approx_eval(g(a).beta_conv()) <= real.real_approx_eval(g(b).beta_conv()):
        incr_pt = real_increasing_onI(thy, g, a, b)
        eq_pt = apply_theorem(thy, 'real_integral_substitution_simple_incr', cont_f_pt, dg_pt, le_pt, incr_pt)
        eq_pt = eq_pt.on_lhs(thy, arg_conv(abs_conv(real.real_norm_conv())))
        eq_pt = eq_pt.on_rhs(thy, arg_conv(abs_conv(real.real_norm_conv())),
                                    arg1_conv(binop_conv(real.real_norm_conv())))
        eq_pt = eq_pt.on_rhs(thy, arg1_conv(binop_conv(simplify())))
    else:
        decr_pt = real_decreasing_onI(thy, g, a, b)
        eq_pt = apply_theorem(thy, 'real_integral_substitution_simple_decr', cont_f_pt, dg_pt, le_pt, decr_pt)
        eq_pt = eq_pt.on_lhs(thy, arg_conv(abs_conv(real.real_norm_conv())))
        eq_pt = eq_pt.on_rhs(thy, arg_conv(arg_conv(abs_conv(real.real_norm_conv()))),
                                    arg_conv(arg1_conv(binop_conv(real.real_norm_conv()))))
        eq_pt = eq_pt.on_rhs(thy, arg_conv(arg1_conv(binop_conv(simplify()))))

    return eq_pt

class substitution(Conv):
    """Apply substitution rule.

    expr is of the form real_integral (real_closed_interval a b) (%x. f (g x) * dg x)

    Conditions include:

    -- f is continuous on [g(a), g(b)]
    -- g is an increasing function (so that a <= b implies g(a) <= g(b))

    The result is real_integral (real_closed_interval (g a) (g b)) (%u. f u).

    """
    def __init__(self, f, g):
        self.f = f
        self.g = g

    def get_proof_term(self, thy, expr):
        assert expr.head.is_const_name('real_integral')
        S, h = expr.args
        assert S.head.is_const_name('real_closed_interval')
        a, b = S.args

        if not (h.is_abs() and self.f.is_abs() and self.g.is_abs()):
            raise NotImplementedError

        # Make the equality theorem
        eq_pt = apply_subst_thm(thy, self.f, self.g, a, b)

        # Use the equality to rewrite expression.
        pt = refl(expr)
        pt = pt.on_rhs(thy, arg_conv(abs_conv(real.real_norm_conv())))
        pt = pt.on_rhs(thy, rewr_conv(eq_pt))

        return pt


class substitution_inverse(Conv):
    """Apply inverse substitution rule.

    expr is of the form real_integral (real_closed_interval (g a) (g b)) f

    Conditions include:

    -- f is continuous on [g(a), g(b)]
    -- g is an increasing function (so that a <= b implies g(a) <= g(b))

    The result is real_integral (real_closed_interval a b) (%u. f (g u) * dg u).
     
    """
    def __init__(self, g, a, b):
        self.g = g
        self.a = a
        self.b = b

    def get_proof_term(self, thy, expr):
        assert expr.head.is_const_name('real_integral')
        _, f = expr.args

        if not (f.is_abs() and self.g.is_abs()):
            raise NotImplementedError

        # Make the equality theorem
        eq_pt = apply_subst_thm(thy, f, self.g, self.a, self.b)

        # Use the equality to rewrite expression
        pt = refl(expr)
        pt = pt.on_rhs(thy, arg_conv(abs_conv(real.real_norm_conv())))
        pt = pt.on_rhs(thy, rewr_conv(eq_pt, sym=True))

        return pt

class simplify_rewr_conv(Conv):
    """Rewrite the term with a term with the same simplification."""
    def __init__(self, target):
        """Initialize with target of the rewrite."""
        self.target = target
        self.target_eq = None

    def get_proof_term(self, thy, t):
        if not self.target_eq:
            self.target_eq = simplify().get_proof_term(thy, self.target)

        t_eq = simplify().get_proof_term(thy, t)
        if self.target_eq.rhs != t_eq.rhs:
            raise ConvException("simplify_rewr_conv")

        return ProofTerm.transitive(t_eq, ProofTerm.symmetric(self.target_eq))


class trig_rewr_conv(Conv):
    """Apply trignometric rewrites."""
    def __init__(self, code):
        """Initialize with code of the trignometric rewrite in Fu's method."""
        assert isinstance(code, str)
        self.code = code

    def get_proof_term(self, thy, t):
        if self.code == 'TR5':
            # Substitution of sin square
            return rewr_conv('sin_circle2').get_proof_term(thy, t)
        elif self.code == 'TR5_inv':
            return rewr_conv('sin_circle2', sym=True).get_proof_term(thy, t)
        elif self.code == 'TR6':
            # Substitution of cos square
            return rewr_conv('sin_circle3').get_proof_term(thy, t)
        elif self.code == 'TR6_inv':
            return rewr_conv('sin_circle3', sym=True).get_proof_term(thy, t)
        elif self.code == 'TR7':
            # Lowering the degree of cos square
            return rewr_conv('cos_double_cos2').get_proof_term(thy, t)
        else:
            raise NotImplementedError


class real_abs_conv(Conv):
    """Eliminate absolute value on a given closed interval.
    
    cond -- a condition of the form x Mem closed_interval a b.

    """
    def __init__(self, cond):
        self.cond = cond

    def get_proof_term(self, thy, t):
        if not (t.head.is_const_name("abs") and t.get_type() == realT):
            raise ConvException('real_abs_conv')

        macro = real_ineq_on_interval_macro()
        t_ge_0 = real.greater_eq(t.arg, real.zero)
        t_le_0 = real.less_eq(t.arg, real.zero)
        if macro.can_eval(thy, t_ge_0, [self.cond]):
            pt = ProofTermDeriv('real_ineq_on_interval', thy, t_ge_0, [self.cond])
            return apply_theorem(thy, 'real_abs_pos_eq', pt)
        elif macro.can_eval(thy, t_le_0, [self.cond]):
            pt = ProofTermDeriv('real_ineq_on_interval', thy, t_le_0, [self.cond])
            return apply_theorem(thy, 'real_abs_neg_eq', pt)
        else:
            raise ConvException('real_abs_conv')

class elim_real_abs_conv(Conv):
    """Eliminate absolute value in a definite integral.
    
    t is of the form real_integral (real_closed_interval a b) f.

    Makes use of the theorem real_integral_eq:
    (!x. x Mem s --> f x = g x) --> real_integral s f = real_integral s g

    """
    def get_proof_term(self, thy, expr):
        assert expr.head.is_const_name('real_integral'), "elim_real_abs_conv"
        s, f = expr.args
        assert f.is_abs(), "elim_real_abs_conv"

        x = Var(f.var_name, realT)
        fx = f(x).beta_norm()
        cond = set.mk_mem(x, s)
        eq_pt = top_conv(real_abs_conv(ProofTerm.assume(cond))).get_proof_term(thy, fx)
        eq_pt = ProofTerm.implies_intr(cond, eq_pt)
        eq_pt = ProofTerm.forall_intr(x, eq_pt)
        return apply_theorem(thy, 'real_integral_eq', eq_pt)


class location_conv(Conv):
    """Apply conversion at the given location."""
    def __init__(self, loc, cv):
        if not isinstance(loc, Location):
            loc = Location(loc)
        assert isinstance(loc, Location) and isinstance(cv, Conv), "location_Conv"
        self.loc = loc
        self.cv = cv

    def get_proof_term(self, thy, t):
        if self.loc.is_empty():
            return self.cv.get_proof_term(thy, t)
        elif t.head.is_const_name("evalat"):
            # Term is of the form evalat f a b
            if self.loc.head == 0:
                return argn_conv(0, abs_conv(location_conv(self.loc.rest, self.cv))).get_proof_term(thy, t)
            else:
                raise NotImplementedError
        elif t.head.is_const_name("real_integral"):
            # Term is of the form real_integral (real_closed_interval a b) f
            if self.loc.head == 0:
                return arg_conv(abs_conv(location_conv(self.loc.rest, self.cv))).get_proof_term(thy, t)
            else:
                raise NotImplementedError
        else:
            return argn_conv(self.loc.head, location_conv(self.loc.rest, self.cv)).get_proof_term(thy, t)


def get_at_location(loc, t):
    if loc.is_empty():
        return t
    elif t.head.is_const_name("evalat"):
        if loc.head == 0:
            f = t.args[0]
            body = f.subst_bound(f.var_name, realT)
            return get_at_location(loc.rest, body)
        else:
            raise NotImplementedError
    elif t.head.is_const_name("real_integral"):
        if loc.head == 0:
            f = t.args[0]
            body = f.subst_bound(f.var_name, realT)
            return get_at_location(loc.rest, body)
        else:
            raise NotImplementedError
    else:
        return get_at_location(loc.rest, t.args[loc.head])

def expr_to_holpy(expr):
    """Convert an expression to holpy term."""
    assert isinstance(expr, Expr), "expr_to_holpy"
    if expr.is_var():
        return Var(expr.name, real.realT)
    elif expr.is_const():
        return real.to_binary_real(expr.val)
    elif expr.is_op():
        if expr.op == '-' and len(expr.args) == 1:
            return real.uminus(expr_to_holpy(expr.args[0]))

        if len(expr.args) != 2:
            raise NotImplementedError

        a, b = [expr_to_holpy(arg) for arg in expr.args]
        if expr.op == '+':
            return real.plus(a, b)
        elif expr.op == '-':
            return real.minus(a, b)
        elif expr.op == '*':
            return real.times(a, b)
        elif expr.op == '/':
            return real.divides(a, b)
        elif expr.op == '^':
            if expr.args[1].is_const() and isinstance(expr.args[1].val, int) and expr.args[1].val >= 0:
                return real.nat_power(a, nat.to_binary_nat(expr.args[1].val))
            else:
                return real.real_power(a, b)
        else:
            raise NotImplementedError
    elif expr.is_fun():
        if expr.func_name == 'pi':
            return real.pi
        
        if len(expr.args) != 1:
            raise NotImplementedError

        a = expr_to_holpy(expr.args[0])
        if expr.func_name == 'sin':
            return real.sin(a)
        elif expr.func_name == 'cos':
            return real.cos(a)
        elif expr.func_name == 'tan':
            return real.tan(a)
        elif expr.func_name == 'log':
            return real.log(a)
        elif expr.func_name == 'exp':
            return real.exp(a)
        elif expr.func_name == 'abs':
            return real.abs(a)
        elif expr.func_name == 'sqrt':
            return real.sqrt(a)
        else:
            raise NotImplementedError
    elif expr.is_deriv():
        raise NotImplementedError
    elif expr.is_integral():
        a, b = expr_to_holpy(expr.lower), expr_to_holpy(expr.upper)
        var = Var(expr.var, real.realT)
        f = Term.mk_abs(var, expr_to_holpy(expr.body))
        return mk_real_integral(f, a, b)
    elif expr.is_evalat():
        a, b = expr_to_holpy(expr.lower), expr_to_holpy(expr.upper)
        var = Var(expr.var, real.realT)
        f = Term.mk_abs(var, expr_to_holpy(expr.body))
        return evalat(f, a, b)
    else:
        raise NotImplementedError

def translate_item(item, target=None, *, debug=False):
    """Translate a calculation in json into holpy proof."""
    ctxt = Context('realintegral')
    thy = ctxt.thy

    problem = integral.parser.parse_expr(item['problem'])
    init = expr_to_holpy(problem)
    pt = refl(init)

    if debug:
        print("\n%s: %s" % (item['name'], printer.print_term(thy, pt.rhs)))

    for step in item['calc']:
        if 'location' in step:
            loc = Location(step['location'])
        else:
            loc = Location("")
        reason = step['reason']
        if reason == 'Linearity':
            cv = top_conv(linearity())
        elif reason == 'Common integrals':
            cv = top_conv(common_integral())
        elif reason == 'Simplification':
            cv = simplify()
        elif reason == 'Substitution':
            rewr_t = get_at_location(loc, pt.rhs)
            assert rewr_t.head.is_const_name("real_integral"), "translate_item: Substitution"
            f = integral.parser.parse_expr(step['params']['f'])
            g = integral.parser.parse_expr(step['params']['g'])
            ori_name = rewr_t.arg.var_name
            ori_var = Var(ori_name, realT)
            new_name = step['params']['var_name']
            new_var = Var(new_name, realT)
            f = Term.mk_abs(new_var, expr_to_holpy(f))
            g = Term.mk_abs(ori_var, expr_to_holpy(g))
            cv = substitution(f, g)
        elif reason == 'Substitution inverse':
            rewr_t = get_at_location(loc, pt.rhs)
            assert rewr_t.head.is_const_name("real_integral"), "translate_item: Substitution inverse"
            g = integral.parser.parse_expr(step['params']['g'])
            new_name = step['params']['var_name']
            new_var = Var(new_name, realT)
            g = Term.mk_abs(new_var, expr_to_holpy(g))
            a = expr_to_holpy(integral.parser.parse_expr(step['params']['a']))
            b = expr_to_holpy(integral.parser.parse_expr(step['params']['b']))
            cv = substitution_inverse(g, a, b)
        elif reason == 'Integrate by parts':
            rewr_t = get_at_location(loc, pt.rhs)
            assert rewr_t.head.is_const_name("real_integral"), "translate_item: Integrate by parts"
            u = integral.parser.parse_expr(step['params']['u'])
            v = integral.parser.parse_expr(step['params']['v'])
            ori_name = rewr_t.arg.var_name
            ori_var = Var(ori_name, realT)
            u = Term.mk_abs(ori_var, expr_to_holpy(u))
            v = Term.mk_abs(ori_var, expr_to_holpy(v))
            cv = integrate_by_parts(u, v)
        elif reason == 'Rewrite':
            rhs = integral.parser.parse_expr(step['params']['rhs'])
            rhs = expr_to_holpy(rhs)
            cv = simplify_rewr_conv(rhs)
        elif reason == 'Rewrite trigonometric':
            cv = trig_rewr_conv(step['params']['rule'])
        elif reason == 'Elim abs':
            cv = elim_real_abs_conv()
        else:
            raise NotImplementedError

        pt = pt.on_rhs(thy, location_conv(loc, cv))
        if debug:
            print("= %s" % printer.print_term(thy, pt.rhs))

    assert pt.lhs == init, "translate_item: wrong left side"
    if target is not None:
        target = expr_to_holpy(integral.parser.parse_expr(target))
        assert pt.rhs == target, "translate_item: wrong right side. Expected %s, got %s" % (
            printer.print_term(thy, target), printer.print_term(thy, pt.rhs)
        )
    else:
        print(printer.print_term(thy, pt.rhs))

    return pt


macro.global_macros.update({
    "real_ineq_on_interval": real_ineq_on_interval_macro(),
})
