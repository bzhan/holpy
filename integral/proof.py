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
real_derivative = Const('real_derivative', TFun(TFun(realT, realT), realT, realT))
real_integral = Const('real_integral', TFun(set.setT(realT), TFun(realT, realT), realT))


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

auto.add_global_autos(
    Const('real_differentiable_on', TFun(TFun(realT, realT), set.setT(realT), boolT)),
    auto.solve_rules([
        # Differentiable everywhere
        "real_differentiable_on_const",
        "real_differentiable_on_id",
        "real_differentiable_on_add",
        "real_differentiable_on_neg",
        "real_differentiable_on_sub",
        "real_differentiable_on_mul",
        "real_differentiable_on_pow",
        "real_differentiable_on_exp",
        "real_differentiable_on_exp_compose",
        "real_differentiable_on_sin",
        "real_differentiable_on_sin_compose",
        "real_differentiable_on_cos",
        "real_differentiable_on_cos_compose",

        # Differentiable with conditions
        "real_differentiable_on_div",
        "real_differentiable_on_log",
        "real_differentiable_on_log_compose",
        "real_differentiable_on_sqrt",
        "real_differentiable_on_sqrt_compose",

        # Real power
        "real_differentiable_on_real_pow",
    ])
)

auto.add_global_autos(
    Const('real_differentiable', TFun(TFun(realT, realT), netT(realT), boolT)),
    auto.solve_rules([
        # Differentiable everywhere
        "real_differentiable_const",
        "real_differentiable_id",
        "real_differentiable_add",
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

        # Differentiable with conditions
        "real_differentiable_div_atreal",
        "real_differentiable_at_log",
        "real_differentiable_at_log_compose",
        "real_differentiable_at_sqrt",
        "real_differentiable_at_sqrt_compose",

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
        'real_sin_pi3',
        'real_sin_pi2_alt',
        'real_sin_pi',
        'real_sin_minus_pi4',
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

auto.add_global_autos_norm(
    real_derivative,
    auto.norm_rules([
        # Differentiable everywhere
        "real_derivative_const",
        "real_derivative_id",
        "real_derivative_add",
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

        # Differentiable with conditions
        "real_derivative_div_atreal",
        "real_derivative_log",
        "real_derivative_log_compose",
        "real_derivative_sqrt",
        "real_derivative_sqrt_compose",

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
        "real_integral_lmul",
        "real_integral_div",
        "real_integral_neg",
        "real_integral_sub",

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
    ])
)

class real_integral_cong(Conv):
    """Apply auto to the body of an integral."""
    def get_proof_term(self, thy, expr):
        assert expr.head.is_const_name('real_integral'), 'real_integral_cong'
        S, f = expr.args
        
        if not S.head.is_const_name('real_closed_interval'):
            raise ConvException
        a, b = S.args
        le_pt = auto.auto_solve(thy, real.less_eq(a, b))

        interval = real.open_interval(a, b)
        v = Var(f.var_name, realT)
        cond = set.mk_mem(v, interval)
        body = f.subst_bound(v)

        cv = auto.auto_conv(conds=[ProofTerm.assume(cond)])
        eq_pt = cv.get_proof_term(thy, body)
        eq_pt = ProofTerm.implies_intr(cond, eq_pt)
        eq_pt = ProofTerm.forall_intr(v, eq_pt)
        return apply_theorem(thy, 'real_integral_eq_closed_interval', le_pt, eq_pt)

auto.add_global_autos_norm(real_integral, real_integral_cong())


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

        if not (f.is_abs() and self.u.is_abs() and self.v.is_abs()):
            raise NotImplementedError

        eq_pt = apply_theorem(thy, 'real_integration_by_parts_simple_evalat',
            inst={'a': a, 'b': b, 'u': self.u, 'v': self.v})

        As, _ = eq_pt.prop.strip_implies()
        for A in As:
            A_pt = auto.auto_solve(thy, A)
            eq_pt = ProofTerm.implies_elim(eq_pt, A_pt)

        eq_pt = eq_pt.on_lhs(thy, arg_conv(abs_conv(auto.auto_conv())))
        eq_pt = eq_pt.on_rhs(thy, arg_conv(arg_conv(abs_conv(auto.auto_conv()))))

        pt = refl(expr)
        pt = pt.on_rhs(thy, arg_conv(abs_conv(auto.auto_conv())))
        pt = pt.on_rhs(thy, rewr_conv(eq_pt))
        return pt


def apply_subst_thm(thy, f, g, a, b):
    """Apply the substitution theorem.

    The returned result is (in the increasing case)
    real_integral (real_closed_interval a b) (%x. f (g x) * dg x) =
    real_integral (real_closed_interval (g a) (g b)) f,

    where both f (g x) * dg x and f are normalized.

    """
    # Form the assumption: g is increasing or decreasing on [a, b],
    # then apply the theorem.
    if real.real_approx_eval(g(a).beta_conv()) <= real.real_approx_eval(g(b).beta_conv()):
        eq_pt = apply_theorem(thy, 'real_integral_substitution_simple_incr',
            inst={'a': a, 'b': b, 'f': f, 'g': g})
        
        As, _ = eq_pt.prop.strip_implies()
        for A in As:
            A_pt = auto.auto_solve(thy, A)
            eq_pt = ProofTerm.implies_elim(eq_pt, A_pt)
    else:
        eq_pt = apply_theorem(thy, 'real_integral_substitution_simple_decr',
            inst={'a': a, 'b': b, 'f': f, 'g': g})
        
        As, _ = eq_pt.prop.strip_implies()
        for A in As:
            A_pt = auto.auto_solve(thy, A)
            eq_pt = ProofTerm.implies_elim(eq_pt, A_pt)

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
        pt = refl(expr).on_rhs(thy, auto.auto_conv())
        pt = pt.on_rhs(thy, rewr_conv(eq_pt.on_lhs(thy, auto.auto_conv())))
        pt = pt.on_rhs(thy, arg1_conv(auto.auto_conv()))

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
        pt = refl(expr).on_rhs(thy, auto.auto_conv())
        eq_pt = eq_pt.on_rhs(thy, auto.auto_conv())
        if eq_pt.rhs != pt.rhs:
            raise ConvException("Substitution inverse: %s != %s" % (
                printer.print_term(thy, eq_pt.rhs), printer.print_term(thy, pt.rhs)))
        pt = ProofTerm.transitive(pt, ProofTerm.symmetric(eq_pt))
        pt = pt.on_rhs(thy, auto.auto_conv())

        return pt


class simplify_rewr_conv(Conv):
    """Rewrite the term with a term with the same simplification."""
    def __init__(self, target):
        """Initialize with target of the rewrite."""
        self.target = target
        self.target_eq = None

    def get_proof_term(self, thy, t):
        if not self.target_eq:
            self.target_eq = refl(self.target).on_rhs(thy, auto.auto_conv())

        t_eq = refl(t).on_rhs(thy, auto.auto_conv())
        if self.target_eq.rhs != t_eq.rhs:
            raise ConvException("simplify_rewr_conv: %s != %s" % (
                printer.print_term(thy, self.target_eq.rhs), printer.print_term(thy, t_eq.rhs)))

        return ProofTerm.transitive(t_eq, ProofTerm.symmetric(self.target_eq))


class trig_rewr_conv(Conv):
    """Apply trignometric rewrites."""
    def __init__(self, code):
        """Initialize with code of the trignometric rewrite in Fu's method."""
        assert isinstance(code, str)
        self.code = code

    def get_proof_term(self, thy, t):
        # Obtain the only variable in t
        xs = term.get_vars(t)
        assert len(xs) == 1, "trig_rewr_conv"
        x = xs[0]

        if self.code == 'TR5':
            # Substitution (sin x) ^ 2 = 1 - (cos x) ^ 2
            return refl(t).on_rhs(thy, rewr_conv('sin_circle2'))
        elif self.code == 'TR5_inv':
            # Substitution 1 - (cos x) ^ 2 = (sin x) ^ 2
            eq_pt = apply_theorem(thy, 'sin_circle2', inst={'x': x})
            eq_pt = ProofTerm.symmetric(eq_pt)
            eq_pt = eq_pt.on_lhs(thy, auto.auto_conv())
            return refl(t).on_rhs(thy, auto.auto_conv(), rewr_conv(eq_pt))
        elif self.code == 'TR6':
            # Substitution (cos x) ^ 2 = 1 - (sin x) ^ 2
            return refl(t).on_rhs(thy, rewr_conv('sin_circle3'))
        elif self.code == 'TR6_inv':
            # Substitution 1 - (sin x) ^ 2 = (cos x) ^ 2
            eq_pt = apply_theorem(thy, 'sin_circle3', inst={'x': x})
            eq_pt = ProofTerm.symmetric(eq_pt)
            eq_pt = eq_pt.on_lhs(thy, auto.auto_conv())
            return refl(t).on_rhs(thy, auto.auto_conv(), rewr_conv(eq_pt))
        elif self.code == 'TR7':
            # Lowering the degree of cos square
            return rewr_conv('cos_double_cos2').get_proof_term(thy, t)
        else:
            raise NotImplementedError


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
            body = f.subst_bound(Var(f.var_name, realT))
            return get_at_location(loc.rest, body)
        else:
            raise NotImplementedError
    elif t.head.is_const_name("real_integral"):
        if loc.head == 0:
            f = t.args[1]
            body = f.subst_bound(Var(f.var_name, realT))
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
        return real_integral(real.closed_interval(a, b), f)
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

        if reason == 'Simplification':
            # Simplify the expression
            cv = auto.auto_conv()

        elif reason == 'Substitution':
            # Perform substitution u = g(x)
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
            # Perform substitution x = g(u)
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
            # Integration by parts using u and v
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
            # Rewrite to another expression
            rhs = integral.parser.parse_expr(step['params']['rhs'])
            rhs = expr_to_holpy(rhs)
            cv = simplify_rewr_conv(rhs)

        elif reason == 'Rewrite trigonometric':
            # Rewrite using a trigonometric identity
            cv = trig_rewr_conv(step['params']['rule'])

        else:
            raise NotImplementedError

        pt = pt.on_rhs(thy, location_conv(loc, cv))
        if debug:
            print("= %s" % printer.print_term(thy, pt.rhs))

    assert pt.lhs == init, "translate_item: wrong left side."
    if target is not None:
        target = expr_to_holpy(integral.parser.parse_expr(target))
        assert pt.rhs == target, "translate_item. Expected %s, got %s" % (
            printer.print_term(thy, target), printer.print_term(thy, pt.rhs)
        )
    elif not debug:
        print(printer.print_term(thy, pt.rhs))

    return pt
