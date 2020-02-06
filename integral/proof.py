"""Proofs for differentiation and integration."""

from fractions import Fraction

from kernel import term
from kernel.type import TFun, BoolType, RealType
from kernel.term import Term, Var, Const, Not, Eq, Lambda, Nat, Real, Inst
from kernel.thm import Thm
from logic.conv import Conv, ConvException, argn_conv, arg_conv, arg1_conv, top_conv, \
    rewr_conv, abs_conv, binop_conv, every_conv, try_conv
from logic.logic import apply_theorem
from logic import auto
from logic import logic
from kernel.proofterm import ProofTerm, refl
from logic.context import Context
from data import set
from data import nat
from data import real
from data.real import pi
from data.integral import netT
from integral.expr import Expr, Location
from integral.parser import parse_expr


evalat = Const('evalat', TFun(TFun(RealType, RealType), RealType, RealType, RealType))
real_derivative = Const('real_derivative', TFun(TFun(RealType, RealType), RealType, RealType))
real_integral = Const('real_integral', TFun(set.setT(RealType), TFun(RealType, RealType), RealType))


# Introduction rules for real_continuous_on
auto.add_global_autos(
    Const('real_continuous_on', TFun(TFun(RealType, RealType), set.setT(RealType), BoolType)),
    auto.solve_rules([
        # Continuous everywhere
        "real_continuous_on_const",
        "real_continuous_on_id",
        "real_continuous_on_add",
        "real_continuous_on_uminus",
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
        "real_continuous_on_abs_compose",
        "real_continuous_on_atn",
        "real_continuous_on_atn_compose",

        # Continuous with conditions
        "real_continuous_on_div",
        "real_continuous_on_log",
        "real_continuous_on_log_compose",
        "real_continuous_on_sqrt",
        "real_continuous_on_sqrt_compose",
        "real_continuous_on_tan",
        "real_continuous_on_tan_compose",
        "real_continuous_on_cot",
        "real_continuous_on_cot_compose",
        "real_continuous_on_sec",
        "real_continuous_on_sec_compose",
        "real_continuous_on_csc",
        "real_continuous_on_csc_compose",

        # Real power (three options)
        "real_continuous_on_real_pow",
        "real_continuous_on_real_pow2",
        "real_continuous_on_real_neg1_pow",
    ])
)

auto.add_global_autos(
    Const('real_integrable_on', TFun(TFun(RealType, RealType), set.setT(RealType), BoolType)),
    auto.solve_rules([
        "real_integrable_continuous"
    ])
)

auto.add_global_autos(
    Const('real_differentiable', TFun(TFun(RealType, RealType), netT(RealType), BoolType)),
    auto.solve_rules([
        # Differentiable everywhere
        "real_differentiable_const",
        "real_differentiable_id",
        "real_differentiable_add",
        "real_differentiable_uminus",
        "real_differentiable_neg",
        "real_differentiable_sub",
        "real_differentiable_mul_atreal",
        "real_differentiable_pow_atreal",
        "real_differentiable_at_exp",
        "real_differentiable_at_exp_compose",
        "real_differentiable_at_sin",
        "real_differentiable_at_sin_compose",
        "real_differentiable_at_cos",
        "real_differentiable_at_cos_compose",
        "real_differentiable_at_atn",
        "real_differentiable_at_atn_compose",

        # Differentiable with conditions
        "real_differentiable_div_atreal",
        "real_differentiable_at_log",
        "real_differentiable_at_log_compose",
        "real_differentiable_at_sqrt",
        "real_differentiable_at_sqrt_compose",
        "real_differentiable_at_tan",
        "real_differentiable_at_tan_compose",
        "real_differentiable_at_cot",
        "real_differentiable_at_cot_compose",
        "real_differentiable_at_sec",
        "real_differentiable_at_sec_compose",
        "real_differentiable_at_csc",
        "real_differentiable_at_csc_compose",

        # Real power
        "real_differentiable_real_pow_atreal",
    ])
)

auto.add_global_autos_norm(
    real.sin,
    auto.norm_rules([
        'real_sin_0',
        'real_sin_pi6',
        'real_sin_pi4',
        'real_sin_pi',
        'sin_neg',
        'sin_neg_alt',
        'sin_periodic_pi_div2',
    ])
)

auto.add_global_autos_norm(
    real.cos,
    auto.norm_rules([
        'real_cos_0',
        'real_cos_pi6',
        'real_cos_pi4',
        'real_cos_pi',
        'cos_neg',
        'cos_neg_alt',
        'cos_periodic_pi_div2',
    ])
)

class norm_sin_conv(Conv):
    """Normalization of an expression sin (r * pi)."""
    def get_proof_term(self, t):
        if not t.is_comb('sin', 1):
            raise ConvException('norm_sin_conv')

        if not (t.arg.is_times() and t.arg.arg == pi and t.arg.arg1.is_number()):
            raise ConvException('norm_sin_conv')

        r = t.arg.arg1.dest_number()
        if r >= 2:
            eq = auto.auto_solve(Eq((r-2) * pi + 2 * pi, r * pi))
            return refl(t).on_rhs(arg_conv(rewr_conv(eq, sym=True)), rewr_conv('sin_periodic'))

        if r >= 1:
            eq = auto.auto_solve(Eq((r-1) * pi + pi, r * pi))
            return refl(t).on_rhs(arg_conv(rewr_conv(eq, sym=True)), rewr_conv('sin_periodic_pi'))

        if r >= Fraction(1,2):
            eq = auto.auto_solve(Eq(Fraction(1,2) * pi + (r-Fraction(1,2)) * pi, r * pi))
            return refl(t).on_rhs(arg_conv(rewr_conv(eq, sym=True)), rewr_conv('sin_periodic_pi_div2'))

        if r > Fraction(1,4):
            eq = auto.auto_solve(Eq(pi / 2 - (Fraction(1,2) - r) * pi, r * pi))
            return refl(t).on_rhs(arg_conv(rewr_conv(eq, sym=True)), rewr_conv('cos_sin'))

        return refl(t)

auto.add_global_autos_norm(real.sin, norm_sin_conv())

class norm_cos_conv(Conv):
    """Normalization of an expression cos (r * pi)."""
    def get_proof_term(self, t):
        if not t.is_comb('cos', 1):
            raise ConvException('norm_cos_conv')

        if not (t.arg.is_times() and t.arg.arg == pi and t.arg.arg1.is_number()):
            raise ConvException('norm_cos_conv')

        r = t.arg.arg1.dest_number()
        if r >= 2:
            eq = auto.auto_solve(Eq((r-2) * pi + 2 * pi, r * pi))
            return refl(t).on_rhs(arg_conv(rewr_conv(eq, sym=True)), rewr_conv('cos_periodic'))

        if r >= 1:
            eq = auto.auto_solve(Eq((r-1) * pi + pi, r * pi))
            return refl(t).on_rhs(arg_conv(rewr_conv(eq, sym=True)), rewr_conv('cos_periodic_pi'))

        if r >= Fraction(1,2):
            eq = auto.auto_solve(Eq(Fraction(1,2) * pi + (r-Fraction(1,2)) * pi, r * pi))
            return refl(t).on_rhs(arg_conv(rewr_conv(eq, sym=True)), rewr_conv('cos_periodic_pi_div2'))

        if r > Fraction(1,4):
            eq = auto.auto_solve(Eq(pi / 2 - (Fraction(1,2) - r) * pi, r * pi))
            return refl(t).on_rhs(arg_conv(rewr_conv(eq, sym=True)), rewr_conv('sin_cos'))

        return refl(t)

auto.add_global_autos_norm(real.cos, norm_cos_conv())

auto.add_global_autos_norm(
    real.tan,
    auto.norm_rules([
        'tan_def'
    ])
)

auto.add_global_autos_norm(
    real.cot,
    auto.norm_rules([
        'cot_def'
    ])
)

auto.add_global_autos_norm(
    real.sec,
    auto.norm_rules([
        'sec_def'
    ])
)

auto.add_global_autos_norm(
    real.csc,
    auto.norm_rules([
        'csc_def'
    ])
)

auto.add_global_autos_norm(
    real.exp,
    auto.norm_rules([
        'real_exp_0',
        'exp_log',
    ])
)

auto.add_global_autos_norm(
    real.log,
    auto.norm_rules([
        'log_1',
        'log_exp',
        'log_pow',
        'log_div',
    ])
)

auto.add_global_autos_norm(
    real.abs,
    auto.norm_rules([
        'real_abs_pos_eq',
        'real_abs_neg_eq',
    ])
)

auto.add_global_autos_norm(
    real.atn,
    auto.norm_rules([
        'atn_0',
        'atn_1',
        'atn_sqrt_3',
        'atn_inv_sqrt_3',
        'atn_neg',
        'atn_neg_alt',
    ])
)

auto.add_global_autos_norm(
    real_derivative,
    auto.norm_rules([
        # Differentiable everywhere
        "real_derivative_const",
        "real_derivative_id",
        "real_derivative_add",
        "real_derivative_uminus",
        "real_derivative_neg",
        "real_derivative_sub",
        "real_derivative_mul",
        "real_derivative_pow",
        "real_derivative_exp",
        "real_derivative_exp_compose",
        "real_derivative_sin",
        "real_derivative_sin_compose",
        "real_derivative_cos",
        "real_derivative_cos_compose",
        "real_derivative_atn",
        "real_derivative_atn_compose",

        # Differentiable with conditions
        "real_derivative_div_atreal",
        "real_derivative_log",
        "real_derivative_log_compose",
        "real_derivative_sqrt",
        "real_derivative_sqrt_compose",
        "real_derivative_tan",
        "real_derivative_tan_compose",
        "real_derivative_cot",
        "real_derivative_cot_compose",
        "real_derivative_sec",
        "real_derivative_sec_compose",
        "real_derivative_csc",
        "real_derivative_csc_compose",

        # Real power
        "real_derivative_rpow",
        "real_derivative_rpow_right",
    ])
)

auto.add_global_autos_norm(
    evalat,
    auto.norm_rules([
        'evalat_def'
    ])
)

auto.add_global_autos_norm(
    real_integral,
    auto.norm_rules([
        # Linearity rules
        "real_integral_add",
        "real_integral_neg",
        "real_integral_sub",
        "real_integral_lmul",
        "real_integral_lmul2",
        "real_integral_lmul3",

        # Common integrals
        "real_integral_0",
        "real_integral_const_evalat",
        "real_integral_id_evalat",
        "real_integral_pow_evalat",
        "real_integral_inverse_pow_evalat_pos",
        "real_integral_real_pow_evalat",
        "real_integral_inverse_pos_evalat",
        "real_integral_inverse_neg_evalat",
        "real_integral_sin_evalat",
        "real_integral_cos_evalat",
        "real_integral_exp_evalat",

        # Special trigonometric functions
        "real_integral_to_tan_evalat",
        "real_integral_to_cot_evalat",
        "real_integral_to_atn_evalat",
    ])
)

class real_integral_cong(Conv):
    """Apply auto to the body of an integral."""
    def get_proof_term(self, expr):
        assert expr.is_comb('real_integral', 2), 'real_integral_cong'
        S, f = expr.args
        
        if not S.is_comb('real_closed_interval', 2):
            raise ConvException
        a, b = S.args
        le_pt = auto.auto_solve(a <= b)

        interval = real.open_interval(a, b)
        if f.is_const():
            v = Var('x', RealType)
            cond = set.mk_mem(v, interval)
            body = f(v)
        else:
            v = Var(f.var_name, RealType)
            cond = set.mk_mem(v, interval)
            body = f.subst_bound(v)

        cv = auto.auto_conv(conds=[ProofTerm.assume(cond)])
        eq_pt = cv.get_proof_term(body)
        eq_pt = eq_pt.implies_intr(cond).forall_intr(v)
        return apply_theorem('real_integral_eq_closed_interval', le_pt, eq_pt)

auto.add_global_autos_norm(real_integral, real_integral_cong())


class simplify_rewr_conv(Conv):
    """Rewrite the term with a term with the same simplification."""
    def __init__(self, target):
        """Initialize with target of the rewrite."""
        self.target = target

    def get_proof_term(self, t, conds=None):
        if conds is None:
            conds = []

        if t == self.target:
            return refl(t)

        t_eq = refl(t).on_rhs(auto.auto_conv(conds=conds))
        target_eq = refl(self.target).on_rhs(auto.auto_conv(conds=conds))

        if target_eq.rhs != t_eq.rhs:
            raise ConvException("simplify_rewr_conv: %s != %s" % (target_eq.rhs, t_eq.rhs))

        return t_eq.transitive(target_eq.symmetric())


class combine_fraction(Conv):
    """Combine sum or differences of rational functions."""
    def __init__(self, conds=None):
        if conds is None:
            conds = []
        self.conds = conds

    def get_proof_term(self, t):
        pt = refl(t)
        if t.is_divides():
            return pt
        elif t.is_plus():
            pt = pt.on_rhs(binop_conv(self))
            assert pt.rhs.arg1.is_divides() and pt.rhs.arg.is_divides()
            b = pt.rhs.arg1.arg
            d = pt.rhs.arg.arg
            if b == d:
                b_neq_0 = auto.auto_solve(Not(Eq(b, 0)), self.conds)
                return pt.on_rhs(rewr_conv('real_divide_add_same', conds=[b_neq_0]),
                                 arg1_conv(auto.auto_conv(self.conds)))
            else:
                b_neq_0 = auto.auto_solve(Not(Eq(b, 0)), self.conds)
                d_neq_0 = auto.auto_solve(Not(Eq(d, 0)), self.conds)
                return pt.on_rhs(rewr_conv('real_divide_add', conds=[b_neq_0, d_neq_0]),
                                 arg1_conv(auto.auto_conv(self.conds)),
                                 arg_conv(try_conv(rewr_conv('real_mul_lid'))),
                                 arg_conv(try_conv(rewr_conv('real_mul_rid'))))
        elif t.is_minus():
            return pt.on_rhs(rewr_conv('real_poly_neg2'), self)
        elif t.is_real_power() and t.arg.is_number():
            p = t.arg.dest_number()
            if p == -1:
                return pt.on_rhs(rewr_conv('rpow_neg_one', sym=True),
                                 rewr_conv('real_inverse_divide'))
            elif p < 0:
                pt = pt.on_rhs(rewr_conv('rpow_neg'), rewr_conv('real_inverse_divide'))
                if isinstance(p, int):
                    pt = pt.on_rhs(arg_conv(rewr_conv('rpow_pow')),
                                   arg_conv(arg_conv(rewr_conv('nat_of_nat_def', sym=True))))
                return pt
            else:
                return pt.on_rhs(rewr_conv('real_divide_1'))
        elif t.is_times():
            pt = pt.on_rhs(binop_conv(self))
            assert pt.rhs.arg1.is_divides() and pt.rhs.arg.is_divides()
            b = pt.rhs.arg1.arg
            d = pt.rhs.arg.arg
            b_neq_0 = auto.auto_solve(Not(Eq(b, 0)), self.conds)
            d_neq_0 = auto.auto_solve(Not(Eq(d, 0)), self.conds)
            return pt.on_rhs(rewr_conv('real_divide_mult', conds=[b_neq_0, d_neq_0]),
                             arg1_conv(auto.auto_conv(self.conds)),
                             arg_conv(try_conv(rewr_conv('real_mul_lid'))),
                             arg_conv(try_conv(rewr_conv('real_mul_rid'))))
        else:
            return pt.on_rhs(rewr_conv('real_divide_1'))


class fraction_rewr_conv(Conv):
    """Rewrite two fractions that should be equal after multiplying
    by some denominator.

    The starting term should be an integral.

    """
    def __init__(self, target):
        """Initialize with denominator and target of the rewrite."""
        self.target = target

    def get_proof_term(self, expr, conds=None):
        if conds is None:
            conds = []

        cv = auto.auto_conv(conds=conds)

        lhs_eq = refl(expr).on_rhs(auto.auto_conv(conds))
        rhs_eq = refl(self.target).on_rhs(auto.auto_conv(conds))
        if lhs_eq.rhs == rhs_eq.rhs:
            return lhs_eq.transitive(rhs_eq.symmetric())

        lhs_eq = lhs_eq.on_rhs(combine_fraction(conds))
        rhs_eq = rhs_eq.on_rhs(combine_fraction(conds))

        assert lhs_eq.rhs.is_divides() and rhs_eq.rhs.is_divides()

        a, b = lhs_eq.rhs.args
        c, d = rhs_eq.rhs.args
        b_neq_0 = auto.auto_solve(Not(Eq(b, 0)), conds)
        d_neq_0 = auto.auto_solve(Not(Eq(d, 0)), conds)
        cross_eq = auto.auto_solve(Eq(a * d, b * c), conds)
        pt = apply_theorem('real_divide_eq', b_neq_0, d_neq_0, cross_eq)

        return lhs_eq.transitive(pt, rhs_eq.symmetric())


def fraction_rewr_integral(expr, target):
    """Given two integrals over the same closed range, try to make
    them equal by rewriting the integrands.

    """
    if expr == target:
        return refl(expr)

    assert expr.is_comb('real_integral', 2), 'fraction_rewr_integral'
    assert target.is_comb('real_integral', 2), 'fraction_rewr_integral'

    # First normalize the domain of integration
    expr_pt = refl(expr).on_rhs(arg1_conv(auto.auto_conv()))
    target_pt = refl(target).on_rhs(arg1_conv(auto.auto_conv()))

    S, f = expr_pt.rhs.args
    assert S.is_comb('real_closed_interval', 2), 'fraction_rewr_integral'
    a, b = S.args
    le_pt = auto.auto_solve(real.less_eq(a, b))

    # The domains of integration should now be equal
    target_S, target_f = target_pt.rhs.args
    assert S == target_S, 'fraction_rewr_integral: %s != %s' % (S, target_S)

    # Take variable x and assumption x in the domain of integration
    interval = real.open_interval(a, b)
    v = Var(f.var_name, RealType)
    cond = set.mk_mem(v, interval)
    body = f.subst_bound(v)
    target_body = target_f.subst_bound(v)

    # Now apply fraction_rewr_conv and then use congruence theorem
    eq_pt = fraction_rewr_conv(target_body).get_proof_term(body, [ProofTerm.assume(cond)])
    eq_pt = eq_pt.implies_intr(cond).forall_intr(v)
    eq_pt = apply_theorem('real_integral_eq_closed_interval', le_pt, eq_pt)

    # Link all theorems together
    return expr_pt.transitive(eq_pt, target_pt.symmetric())

def apply_subst_thm(f, g, a, b):
    """Apply the substitution theorem.

    The returned result is (in the increasing case)
    real_integral (real_closed_interval a b) (%x. f (g x) * dg x) =
    real_integral (real_closed_interval (g a) (g b)) f,

    where both f (g x) * dg x and f are normalized.

    """
    # Form the assumption: g is increasing or decreasing on [a, b],
    # then apply the theorem.
    try:
        auto.auto_solve(real.less_eq(g(a).beta_conv(), g(b).beta_conv()))
        is_le = True
    except logic.TacticException:
        is_le = False

    if is_le:
        eq_pt = apply_theorem('real_integral_substitution_simple_incr', inst=Inst(a=a, b=b, f=f, g=g))

        for A in eq_pt.assums:
            eq_pt = eq_pt.implies_elim(auto.auto_solve(A))
    else:
        eq_pt = apply_theorem('real_integral_substitution_simple_decr', inst=Inst(a=a, b=b, f=f, g=g))

        for A in eq_pt.assums:
            eq_pt = eq_pt.implies_elim(auto.auto_solve(A))

    return eq_pt


class substitution(Conv):
    """Apply substitution rule.

    expr is of the form real_integral (real_closed_interval a b) (%x. f (g x) * dg x)

    Conditions include:

    -- f is continuous on [g(a), g(b)]
    -- g is an increasing function (so that a <= b implies g(a) <= g(b))

    The result is real_integral (real_closed_interval (g a) (g b)) (%u. f u).

    """
    def __init__(self, f, g, target):
        self.f = f
        self.g = g
        self.target = target

    def get_proof_term(self, expr):
        assert expr.is_comb('real_integral', 2)
        S, h = expr.args
        assert S.is_comb('real_closed_interval', 2)
        a, b = S.args

        if not (h.is_abs() and self.f.is_abs() and self.g.is_abs()):
            raise NotImplementedError

        # Make the equality theorem
        eq_pt = apply_subst_thm(self.f, self.g, a, b)

        # Use the equality to rewrite expression.
        eq_pt2 = fraction_rewr_integral(eq_pt.lhs, expr)
        pt = eq_pt2.symmetric().transitive(eq_pt)

        eq_pt3 = fraction_rewr_integral(pt.rhs, self.target)
        pt = pt.transitive(eq_pt3)

        return pt


class substitution_inverse(Conv):
    """Apply inverse substitution rule.

    expr is of the form real_integral (real_closed_interval (g a) (g b)) f

    Conditions include:

    -- f is continuous on [g(a), g(b)]
    -- g is an increasing function (so that a <= b implies g(a) <= g(b))

    The result is real_integral (real_closed_interval a b) (%u. f (g u) * dg u).
     
    """
    def __init__(self, g, a, b, target):
        self.g = g
        self.a = a
        self.b = b
        self.target = target

    def get_proof_term(self, expr):
        assert expr.is_comb('real_integral', 2)
        _, f = expr.args

        if not (f.is_abs() and self.g.is_abs()):
            raise NotImplementedError

        # Make the equality theorem
        eq_pt = apply_subst_thm(f, self.g, self.a, self.b)

        # Use the equality to rewrite expression.
        eq_pt2 = fraction_rewr_integral(expr, eq_pt.rhs)
        pt = eq_pt2.transitive(eq_pt.symmetric())

        eq_pt3 = fraction_rewr_integral(pt.rhs, self.target)
        pt = pt.transitive(eq_pt3)

        return pt


class integrate_by_parts(Conv):
    """Evaluate using integration by parts.
    
    expr is of the form real_integral (real_closed_interval a b) (%x. u x * dv x),
    where a and b are constant real numbers.

    u and v are both real => real functions in abstraction form, such that the
    derivative of u is du, and the derivative of v is dv.

    The result is evalat (%x. u x * v x) a b - real_integral (real_closed_interval a b) (%x. u x * dv x).

    """
    def __init__(self, u, v, target):
        self.u = u
        self.v = v
        self.target = target

    def get_proof_term(self, expr):
        assert expr.is_comb('real_integral', 2)
        S, f = expr.args
        assert S.is_comb('real_closed_interval', 2)
        a, b = S.args

        if not (f.is_abs() and self.u.is_abs() and self.v.is_abs()):
            raise NotImplementedError

        eq_pt = apply_theorem('real_integration_by_parts_simple_evalat',
                              inst=Inst(a=a, b=b, u=self.u, v=self.v))

        for A in eq_pt.assums:
            eq_pt = eq_pt.implies_elim(auto.auto_solve(A))

        # Use the equality to rewrite expression.
        eq_pt2 = fraction_rewr_integral(expr, eq_pt.lhs)
        pt = eq_pt2.transitive(eq_pt)

        # Rewrite to agree with target
        assert pt.rhs.is_minus() and self.target.is_minus()
        eq_pt3 = fraction_rewr_integral(pt.rhs.arg, self.target.arg)
        pt = pt.on_rhs(arg_conv(rewr_conv(eq_pt3)))
        pt = pt.on_rhs(arg1_conv(simplify_rewr_conv(self.target.arg1)))
        return pt


class trig_rewr_conv(Conv):
    """Apply trignometric rewrites."""
    def __init__(self, code, target):
        """Initialize with code of the trignometric rewrite in Fu's method."""
        assert isinstance(code, str)
        self.code = code
        self.target = target

    def get_proof_term(self, t, conds=None):
        # Obtain the only variable in t
        if self.code == 'TR0':
            # (sin x) ^ 2 + (cos x) ^ 2 = 1
            return refl(self.target).on_rhs(rewr_conv('sin_circle')).symmetric()
        elif self.code == 'TR1':
            # Definition of sec and csc
            # Handled by normalization
            pt = refl(t)
        elif self.code == 'TR2':
            # Definition of tan and cot
            # Handled by normalization
            pt = refl(t)
        elif self.code == 'TR5':
            # (sin x) ^ 2 = 1 - (cos x) ^ 2
            pt = refl(t).on_rhs(top_conv(rewr_conv('sin_circle2')))
        elif self.code == 'TR6':
            # (cos x) ^ 2 = 1 - (sin x) ^ 2
            pt = refl(t).on_rhs(top_conv(rewr_conv('sin_circle3')))
        elif self.code == 'TR7':
            # (cos x) ^ 2 = (1 + cos (2 * x)) / 2
            pt = refl(t).on_rhs(top_conv(rewr_conv('cos_lower_degree')))
        elif self.code == 'TR8':
            rewr_ths = [
                'sin_lower_degree',  # (sin x) ^ 2 = (1 - cos (2 * x)) / 2
                'real_mul_sin_cos',  # sin x * cos y = 1/2 * (sin (x + y) + sin (x - y))
                'real_mul_cos_sin',  # cos x * sin y = 1/2 * (sin (x + y) - sin (x - y))
                'real_mul_cos_cos',  # cos x * cos y = 1/2 * (cos (x + y) + cos (x - y))
                'real_mul_sin_sin',  # sin x * sin y = -1/2 * (cos (x + y) - cos (x - y))
            ]
            pt = refl(t)
            for rewr_th in rewr_ths:
                pt = pt.on_rhs(top_conv(rewr_conv(rewr_th)))
        elif self.code == 'TR9':
            rewr_ths = [
                'real_add_sin',  # sin x + sin y = 2 * sin ((x + y) / 2) * cos ((x - y) / 2)
                'real_sub_sin',  # sin x - sin y = 2 * sin ((x - y) / 2) * cos ((x + y) / 2)
                'real_add_cos',  # cos x + cos y = 2 * cos ((x + y) / 2) * cos ((x - y) / 2)
                'real_sub_cos',  # cos x - cos y = 2 * sin ((x + y) / 2) * sin ((y - x) / 2)
            ]
            pt = refl(t)
            for rewr_th in rewr_ths:
                pt = pt.on_rhs(top_conv(rewr_conv(rewr_th)))
        elif self.code == 'TR10i':
            rewr_ths = [
                'sin_cos_combine',   # sin x + cos x = sqrt 2 * sin (x + pi / 4)
                'sin_cos_combine2',  # sin x - cos x = -(sqrt 2) * cos (x + pi / 4)
            ]
            pt = refl(t)
            for rewr_th in rewr_ths:
                pt = pt.on_rhs(top_conv(rewr_conv(rewr_th)))
        elif self.code == 'TR11':
            rewr_ths = [
                'sin_double',  # sin (2 * x) = 2 * sin x * cos x
                'cos_double',  # cos (2 * x) = cos x ^ 2 - sin x ^ 2
            ]
            pt = refl(t)
            for rewr_th in rewr_ths:
                pt = pt.on_rhs(top_conv(rewr_conv(rewr_th)))
        elif self.code == 'TR111':
            # Reverse of definition of sec and csc
            # Handled by normalization
            pt = refl(t)
        elif self.code == 'TR22':
            if t.is_plus() and t.arg.is_nat_power() and t.arg.arg1.is_comb('tan', 1):
                cos_neq0 = Not(Eq(real.cos(t.arg.arg1.arg), 0))
                cos_neq0_pt = auto.auto_solve(cos_neq0, conds)
                pt = refl(t).on_rhs(rewr_conv('tan_sec', conds=[cos_neq0_pt]))
            elif t.is_nat_power() and t.arg1.is_comb('tan', 1):
                cos_neq0 = Not(Eq(real.cos(t.arg1.arg), 0))
                cos_neq0_pt = auto.auto_solve(cos_neq0, conds)
                pt = refl(t).on_rhs(rewr_conv('tan_sec_alt', conds=[cos_neq0_pt]))
            elif t.is_nat_power() and t.arg1.is_comb('cot', 1):
                sin_neq0 = Not(Eq(real.sin(t.arg1.arg), 0))
                sin_neq0_pt = auto.auto_solve(sin_neq0, conds)
                pt = refl(t).on_rhs(rewr_conv('cot_csc_alt', conds=[sin_neq0_pt]))
            else:
                pt = refl(t)
        else:
            raise NotImplementedError

        eq_pt = simplify_rewr_conv(self.target).get_proof_term(pt.rhs, conds)
        return pt.transitive(eq_pt)


class split_region_conv(Conv):
    """Split region of integral into two parts."""
    def __init__(self, c):
        self.c = c

    def get_proof_term(self, expr):
        if not expr.is_comb('real_integral', 2):
            raise ConvException('split_region')
        S, f = expr.args
        
        if not S.is_comb('real_closed_interval', 2):
            raise ConvException('split_region')
        a, b = S.args

        eq_pt = apply_theorem('real_integral_combine', inst=Inst(a=a, b=b, c=self.c, f=f))

        for A in eq_pt.assums:
            eq_pt = eq_pt.implies_elim(auto.auto_solve(A))

        return eq_pt.symmetric()


class location_conv(Conv):
    """Apply conversion at the given location."""
    def __init__(self, loc, cv, conds=None):
        if not isinstance(loc, Location):
            loc = Location(loc)
        assert isinstance(loc, Location) and isinstance(cv, Conv), "location_Conv"
        self.loc = loc
        self.cv = cv
        if conds is None:
            conds = []
        self.conds = conds

    def get_proof_term(self, t):
        if self.loc.is_empty():
            if self.conds and not isinstance(self.cv, rewr_conv):
                return self.cv.get_proof_term(t, conds=self.conds)
            else:
                return self.cv.get_proof_term(t)
        elif t.is_comb("evalat", 3):
            # Term is of the form evalat f a b
            if self.loc.head == 0:
                return argn_conv(0, abs_conv(location_conv(self.loc.rest, self.cv, self.conds))).get_proof_term(t)
            else:
                raise NotImplementedError
        elif t.is_comb("real_integral", 2):
            # Term is of the form real_integral (real_closed_interval a b) f
            if self.loc.head == 0:
                # Apply congruence rule
                S, f = t.args
                if not S.is_comb('real_closed_interval', 2):
                    raise ConvException
                a, b = S.args
                le_pt = auto.auto_solve(a <= b)

                interval = real.open_interval(a, b)
                v = Var(f.var_name, RealType)
                cond = set.mk_mem(v, interval)
                body = f.subst_bound(v)

                cv = location_conv(self.loc.rest, self.cv, self.conds + [ProofTerm.assume(cond)])
                eq_pt = cv.get_proof_term(body)
                eq_pt = eq_pt.implies_intr(cond).forall_intr(v)
                return apply_theorem('real_integral_eq_closed_interval', le_pt, eq_pt)
            else:
                raise NotImplementedError
        else:
            return argn_conv(self.loc.head, location_conv(self.loc.rest, self.cv, self.conds)).get_proof_term(t)


def get_at_location(loc, t):
    if loc.is_empty():
        return t
    elif t.is_comb("evalat", 3):
        if loc.head == 0:
            f = t.args[0]
            body = f.subst_bound(Var(f.var_name, RealType))
            return get_at_location(loc.rest, body)
        else:
            raise NotImplementedError
    elif t.is_comb("real_integral", 2):
        if loc.head == 0:
            f = t.args[1]
            body = f.subst_bound(Var(f.var_name, RealType))
            return get_at_location(loc.rest, body)
        else:
            raise NotImplementedError
    else:
        return get_at_location(loc.rest, t.args[loc.head])

def expr_to_holpy(expr):
    """Convert an expression to holpy term."""
    assert isinstance(expr, Expr), "expr_to_holpy"
    if expr.is_var():
        return Var(expr.name, RealType)
    elif expr.is_const():
        return Real(expr.val)
    elif expr.is_op():
        if expr.op == '-' and len(expr.args) == 1:
            return -(expr_to_holpy(expr.args[0]))

        if len(expr.args) != 2:
            raise NotImplementedError

        a, b = [expr_to_holpy(arg) for arg in expr.args]
        if expr.op == '+':
            return a + b
        elif expr.op == '-':
            return a - b
        elif expr.op == '*':
            return a * b
        elif expr.op == '/':
            return a / b
        elif expr.op == '^':
            if expr.args[1].is_const() and isinstance(expr.args[1].val, int) and expr.args[1].val >= 0:
                return a ** Nat(expr.args[1].val)
            else:
                return a ** b
        else:
            raise NotImplementedError
    elif expr.is_fun():
        if expr.func_name == 'pi':
            return pi
        
        if len(expr.args) != 1:
            raise NotImplementedError

        a = expr_to_holpy(expr.args[0])
        if expr.func_name == 'sin':
            return real.sin(a)
        elif expr.func_name == 'cos':
            return real.cos(a)
        elif expr.func_name == 'tan':
            return real.tan(a)
        elif expr.func_name == 'cot':
            return real.cot(a)
        elif expr.func_name == 'sec':
            return real.sec(a)
        elif expr.func_name == 'csc':
            return real.csc(a)
        elif expr.func_name == 'log':
            return real.log(a)
        elif expr.func_name == 'exp':
            return real.exp(a)
        elif expr.func_name == 'abs':
            return real.abs(a)
        elif expr.func_name == 'sqrt':
            return real.sqrt(a)
        elif expr.func_name == 'atan':
            return real.atn(a)
        else:
            raise NotImplementedError
    elif expr.is_deriv():
        raise NotImplementedError
    elif expr.is_integral():
        a, b = expr_to_holpy(expr.lower), expr_to_holpy(expr.upper)
        var = Var(expr.var, RealType)
        f = Lambda(var, expr_to_holpy(expr.body))
        return real_integral(real.closed_interval(a, b), f)
    elif expr.is_evalat():
        a, b = expr_to_holpy(expr.lower), expr_to_holpy(expr.upper)
        var = Var(expr.var, RealType)
        f = Lambda(var, expr_to_holpy(expr.body))
        return evalat(f, a, b)
    else:
        raise NotImplementedError

def translate_item(item, target=None, *, debug=False):
    """Translate a calculation in json into holpy proof."""
    problem = parse_expr(item['problem'])
    init = expr_to_holpy(problem)
    pt = refl(init)

    prev_pts = [pt]

    if debug:
        print("\n%s: %s" % (item['name'], pt.rhs))

    for step in item['calc']:
        if 'location' in step:
            loc = Location(step['location'])
        else:
            loc = Location("")
        reason = step['reason']
        expected = expr_to_holpy(parse_expr(step['text']))

        rewr_loc = get_at_location(loc, pt.rhs)
        expected_loc = get_at_location(loc, expected)

        if reason == 'Initial':
            continue

        elif reason == 'Simplification':
            # Simplify the expression
            cv = simplify_rewr_conv(expected_loc)

        elif reason == 'Substitution':
            # Perform substitution u = g(x)
            assert rewr_loc.is_comb("real_integral", 2), "translate_item: Substitution"
            f = expr_to_holpy(parse_expr(step['params']['f']))
            g = expr_to_holpy(parse_expr(step['params']['g']))
            ori_var = term.get_vars(g)[0]
            new_name = step['params']['var_name']
            new_var = Var(new_name, RealType)
            f = Lambda(new_var, f)
            g = Lambda(ori_var, g)
            cv = substitution(f, g, expected_loc)

        elif reason == 'Substitution inverse':
            # Perform substitution x = g(u)
            assert rewr_loc.is_comb("real_integral", 2), "translate_item: Substitution inverse"
            g = parse_expr(step['params']['g'])
            new_name = step['params']['var_name']
            new_var = Var(new_name, RealType)
            g = Lambda(new_var, expr_to_holpy(g))
            a = expr_to_holpy(parse_expr(step['params']['a']))
            b = expr_to_holpy(parse_expr(step['params']['b']))
            cv = substitution_inverse(g, a, b, expected_loc)

        elif reason == 'Integrate by parts':
            # Integration by parts using u and v
            assert rewr_loc.is_comb("real_integral", 2), "translate_item: Integrate by parts"
            u = expr_to_holpy(parse_expr(step['params']['parts_u']))
            v = expr_to_holpy(parse_expr(step['params']['parts_v']))
            ori_var = term.get_vars([u, v])[0]
            u = Lambda(ori_var, u)
            v = Lambda(ori_var, v)
            cv = integrate_by_parts(u, v, expected_loc)

        elif reason == 'Rewrite':
            # Rewrite to another expression
            rhs = parse_expr(step['params']['rhs'])
            rhs = expr_to_holpy(rhs)
            cv = simplify_rewr_conv(rhs)

        elif reason == 'Rewrite fraction':
            # Rewrite by multiplying a denominator
            rhs = parse_expr(step['params']['rhs'])
            rhs = expr_to_holpy(rhs)
            cv = fraction_rewr_conv(rhs)

        elif reason == 'Rewrite trigonometric':
            # Rewrite using a trigonometric identity
            cv = trig_rewr_conv(step['params']['rule'], expected_loc)

        elif reason == 'Unfold power':
            # Rewrite x ^ 2 to x * x.
            cv = rewr_conv('real_pow_2')

        elif reason == 'Split region':
            # Split region of integration
            c = parse_expr(step['params']['c'])
            c = expr_to_holpy(c)
            cv = split_region_conv(c)

        elif reason == 'Solve equation':
            # Solving equation
            factor = int(step['params']['factor'])
            prev_id = int(step['params']['prev_id'])
            prev_pt = prev_pts[prev_id]

            t1 = Fraction(1, factor+1) * (prev_pt.rhs + factor * prev_pt.rhs)
            t1_pt = auto.auto_solve(Eq(prev_pt.rhs, t1))
            t1_pt = t1_pt.on_rhs(arg_conv(arg1_conv(rewr_conv(prev_pt, sym=True))),
                                 arg_conv(arg1_conv(rewr_conv(pt))), auto.auto_conv())
            pt = prev_pt.transitive(t1_pt)
        else:
            raise NotImplementedError

        # Obtain result on proof side
        if reason != 'Solve equation':
            pt = pt.on_rhs(location_conv(loc, cv))

        if reason not in ('Unfold power', 'Split region', 'Solve equation'):
            assert pt.rhs == expected, "translate_item: unexpected rhs"

        if pt.rhs != expected:
            eq_pt1 = refl(expected).on_rhs(auto.auto_conv())
            eq_pt2 = refl(pt.rhs).on_rhs(auto.auto_conv())
            if eq_pt1.rhs != eq_pt2.rhs:
                print("Unequal right side.\nExpected: %s\nGot:      %s" % (eq_pt1.rhs, eq_pt2.rhs))
                raise AssertionError
            else:
                pt = pt.transitive(eq_pt2, eq_pt1.symmetric())

        pt = ProofTerm("transitive", None, [pt, ProofTerm.reflexive(expected)])

        if debug:
            print("= %s" % pt.rhs)
        prev_pts.append(pt)

    assert pt.lhs == init, "translate_item: wrong left side."
    if target is not None:
        target = expr_to_holpy(parse_expr(target))
        assert pt.rhs == target, "translate_item. Expected %s, got %s" % (target, pt.rhs)
    elif not debug:
        print(pt.rhs)

    return pt
