"""Rules for integration."""

import fractions
from decimal import Decimal
from typing import Optional, Dict
import sympy
import functools

from integral import expr
from integral.expr import Var, Const, Fun, EvalAt, Op, Integral, Symbol, Expr, \
    OP, CONST, VAR, sin, cos, FUN, decompose_expr_factor, \
    Deriv, Inf, Limit, NEG_INF, POS_INF, IndefiniteIntegral, log, Summation
from integral import parser
from sympy import expand_multinomial, apart
from fractions import Fraction
from integral.solve import solve_equation, solve_for_term
from integral.conditions import Conditions
from integral import latex
from integral import limits
from integral.context import Context


class Rule:
    """
    Represents a rule for integration. It takes an integral
    to be evaluated (as an expression), then outputs a new
    expression that it is equal to.

    """

    def eval(self, e: Expr, ctx: Context) -> Expr:
        """Evaluation of the rule on the given expression. Returns
        a new expression.

        """
        raise NotImplementedError

    def export(self):
        """Returns the JSON representation of the rule."""
        raise NotImplementedError
    
    def get_substs(self) -> Dict[str, Expr]:
        """Return dictionary of variable substitutions produced by the rule."""
        return dict()


class Simplify(Rule):
    """Perform algebraic simplification. This treats the
    expression as a polynomial, and normalizes the polynomial.

    """

    def __init__(self):
        self.name = "Simplify"

    def __str__(self):
        return "simplify"

    def export(self):
        return {
            "name": self.name,
            "str": str(self)
        }

    def eval(self, e: Expr, ctx: Context) -> Expr:
        res = e.normalize()
        return res


class Linearity(Rule):
    """Applies linearity rules:

    INT (a + b) = INT a + INT b,
    INT (c * a) = c * INT a      (where c is a constant).
    INT (c / a) = c * INT 1 / a  (where c is a constant).

    """

    def __init__(self):
        self.name = "Linearity"

    def __str__(self):
        return "linearity"

    def export(self):
        return {
            "name": self.name,
            "str": str(self)
        }

    def eval(self, e: Expr, ctx: Context) -> Expr:
        def rec(e):
            if e.is_integral():
                if e.body.is_plus():
                    return rec(expr.Integral(e.var, e.lower, e.upper, e.body.args[0])) + \
                        rec(expr.Integral(e.var, e.lower, e.upper, e.body.args[1]))
                elif e.body.is_uminus():
                    return -rec(expr.Integral(e.var, e.lower, e.upper, e.body.args[0]))
                elif e.body.is_minus():
                    return rec(expr.Integral(e.var, e.lower, e.upper, e.body.args[0])) - \
                        rec(expr.Integral(e.var, e.lower, e.upper, e.body.args[1]))
                elif e.body.is_times():
                    factors = decompose_expr_factor(e.body)
                    b, c = Const(1), Const(1)
                    for f in factors:
                        if not f.contains_var(e.var):
                            c = c * f
                        else:
                            b = b * f
                    c = c.normalize()
                    b = b.normalize()
                    return c * Integral(e.var, e.lower, e.upper, b)
                elif e.body.is_constant() and e.body != Const(1):
                    return e.body * expr.Integral(e.var, e.lower, e.upper, Const(1))
                else:
                    return e
            elif e.is_indefinite_integral():
                if e.body.is_times():
                    factors = decompose_expr_factor(e.body)
                    b, c = Const(1), Const(1)
                    for f in factors:
                        if not f.contains_var(e.var):
                            c = c * f
                        else:
                            b = b * f
                    c = c.normalize()
                    b = b.normalize()
                    return c * IndefiniteIntegral(e.var, b, e.skolem_args)
                elif e.body.is_uminus():
                    return -IndefiniteIntegral(e.var, e.body.args[0], e.skolem_args)
                elif e.body.is_divides():
                    return e
                else:
                    return e
            elif e.is_limit():
                if e.body.is_uminus():
                    return -Limit(e.var, e.lim, e.body.args[0])
                elif e.body.is_times():
                    factors = decompose_expr_factor(e.body)
                    if not factors[0].contains_var(e.var):
                        return factors[0] * rec(expr.Limit(
                            e.var, e.lim,
                            functools.reduce(lambda x, y: x * y, factors[2:], factors[1])))
                    else:
                        return e
                else:
                    return e
            elif e.is_summation():
                v, l, u, body = e.index_var, e.lower, e.upper, e.body
                if e.body.is_minus():
                    return Summation(v, l, u, body.args[0]) - Summation(v, l,u,body.args[1])
                factors = decompose_expr_factor(e.body)
                b, c = Const(1), Const(1)
                for f in factors:
                    if not f.contains_var(e.index_var):
                        c = c * f
                    else:
                        b = b * f
                c = c.normalize()
                b = b.normalize()
                return (c * Summation(e.index_var, e.lower, e.upper, b)).normalize()
            else:
                return e
        return rec(e)


class CommonIntegral(Rule):
    """Applies common integrals:

    INT c = c * x,
    INT x ^ n = x ^ (n + 1) / (n + 1),  (where n != -1)
    INT 1 / x ^ n = (-n) / x ^ (n + 1), (where n != 1)
    INT sqrt(x) = 2/3 * x ^ (3/2)
    INT sin(x) = -cos(x),
    INT cos(x) = sin(x),
    INT 1 / x = log(|x|)
    INT e^x = e^x
    INT 1 / (x^2 + 1) = arctan(x)
    INT sec(x)^2 = tan(x)
    INT csc(x)^2 = -cot(x)

    """

    def __init__(self):
        self.name = "CommonIntegral"

    def __str__(self):
        return "common integrals"

    def export(self):
        return {
            "name": self.name,
            "str": str(self)
        }

    def eval(self, e: Expr, ctx: Context) -> Expr:
        if e.ty != expr.INTEGRAL:
            return e
        if isinstance(e.body, Deriv) and e.body.var == e.var:
            return EvalAt(e.var, e.lower, e.upper, e.body.body)
        if e.var not in e.body.get_vars() and e.body != Const(1):
            return EvalAt(e.var, e.lower, e.upper, e.body * Var(e.var))

        x = Var(e.var)
        c = Symbol('c', [CONST, VAR, OP])
        rules = [
            (Const(1), None, Var(e.var)),
            (c, lambda m: isinstance(m[c.name], Const) or isinstance(m[c.name], Var) and m[c.name] != x, c * Var(e.var)),
            (x, None, (x ^ 2) / 2),
            (x ^ c, lambda m: isinstance(m[c.name], Const) and m[c.name].val != -1 or isinstance(m[c.name], Var)
                              or isinstance(m[c.name], Op) and not m[c.name].has_var(x),
             lambda m: (x ^ ((m[c.name] + 1).normalize())) / (m[c.name] + 1).normalize()),
            (Const(1) / x ^ c, lambda m: isinstance(m[c.name], Const) and m[c.name].val != 1, (-c) / (x ^ (c + 1))),
            (expr.sqrt(x), None, Fraction(2, 3) * (x ^ Fraction(3, 2))),
            (sin(x), None, -cos(x)),
            (cos(x), None, sin(x)),
            (expr.exp(x), None, expr.exp(x)),
            (Const(1) / x, None, expr.log(expr.Fun('abs', x))),
            (x ^ Const(-1), None, expr.log(expr.Fun('abs', x))),
            (((x ^ Const(2)) + 1) ^ Const(-1), None, expr.arctan(x)),
            (expr.sec(x) ^ Const(2), None, expr.tan(x)),
            (expr.csc(x) ^ Const(2), None, -expr.cot(x)),
        ]

        for pat, cond, pat_res in rules:
            mapping = expr.match(e.body, pat)
            if mapping is not None and (cond is None or cond(mapping)):
                if isinstance(pat_res, expr.Expr):
                    integral = pat_res.inst_pat(mapping)
                else:
                    integral = pat_res(mapping)
                return EvalAt(e.var, e.lower, e.upper, integral)

        return e


class ApplyIdentity(Rule):
    """Apply identities (trigonometric, etc) to the current term.
    
    The term that is rewritten to is always supplied, because there may
    be multiple options.

    """
    def __init__(self, target: Expr):
        self.name = "ApplyIdentity"
        self.target = target

    def __str__(self):
        return "rewrite to %s using identity" % self.target

    def export(self):
        return {
            "name": self.name,
            "str": str(self),
            "target": str(self.target),
            "latex_str": "rewrite to \\(%s\\) using identity" % latex.convert_expr(self.target)
        }

    def eval(self, e: Expr, ctx: Context) -> Expr:
        for identity in ctx.get_other_identities():
            inst = expr.match(e, identity.lhs)
            if inst is None:
                continue
            expected_rhs = identity.rhs.inst_pat(inst)
            if expected_rhs.normalize() == self.target.normalize():
                return self.target
            else:
                continue
        
        raise AssertionError("ApplyIdentity: no matching identity for %s" % e)


class DefiniteIntegralIdentity(Rule):
    """Apply definite integral identity in current theory."""
    def __init__(self):
        self.name = "DefiniteIntegralIdentity"

    def __str__(self):
        return "apply definite integral"

    def export(self):
        return {
            "name": self.name,
            "str": str(self)
        }

    def eval(self, e: Expr, ctx: Context) -> Expr:
        if not e.is_integral():
            return e

        # First, look for indefinite integrals identities
        for identity in ctx.get_indefinite_integrals():
            inst = expr.match(IndefiniteIntegral(e.var, e.body, skolem_args=tuple()), identity.lhs)
            if inst is None:
                continue

            inst[identity.lhs.var] = Var(e.var)
            pat_rhs = identity.rhs.args[0]  # remove Skolem constant C
            return EvalAt(e.var, e.lower, e.upper, pat_rhs.inst_pat(inst))

        # Look for definite integral identities
        for identity in ctx.get_definite_integrals():
            inst = expr.match(e, identity.lhs)
            if inst is None:
                continue

            return identity.rhs.inst_pat(inst)

        # No matching identity found
        return e


class SeriesExpansionIdentity(Rule):
    """Apply series expansion in the current theory."""
    def __init__(self, index_var: str = 'n'):
        self.name = "SeriesExpansionIdentity"
        self.index_var = index_var

    def __str__(self):
        return "apply series expansion"

    def export(self):
        return {
            "name": self.name,
            "str": str(self),
            "index_var": self.index_var
        }

    def eval(self, e: Expr, ctx: Context) -> Expr:
        for identity in ctx.get_series_expansions():
            inst = expr.match(e, identity.lhs)
            if inst is None:
                continue

            res = identity.rhs.inst_pat(inst)
            assert res.is_summation()
            res = res.alpha_convert(self.index_var)
            return res

        # No matching identity found
        return e


class SeriesEvaluationIdentity(Rule):
    """Apply series evaluation in the current theory."""
    def __init__(self):
        self.name = "SeriesEvaluationIdentity"

    def __str__(self):
        return "apply series evaluation"

    def export(self):
        return {
            "name": self.name,
            "str": str(self)
        }

    def eval(self, e: Expr, ctx: Context) -> Expr:
        for identity in ctx.get_series_evaluations():
            inst = expr.match(e, identity.lhs)
            if inst is None:
                continue

            return identity.rhs.inst_pat(inst)

        # No matching identity found
        return e


class IndefiniteIntegralIdentity(Rule):
    """Apply indefinite integral identity in current theory."""
    def __init__(self):
        self.name = "IndefiniteIntegralIdentity"

    def __str__(self):
        return "apply indefinite integral"
    
    def export(self):
        return {
            "name": self.name,
            "str": str(self)
        }

    def eval(self, e: Expr, ctx: Context) -> Expr:
        """Apply indefinite integral identity to expression."""

        def apply(e: Expr):
            for indef in ctx.get_indefinite_integrals():
                inst = expr.match(e, indef.lhs)
                if inst is None:
                    continue

                inst['x'] = Var(e.var)
                assert indef.rhs.is_plus() and indef.rhs.args[1].is_symbol() and \
                    indef.rhs.args[1].name == "C"
                return indef.rhs.args[0].inst_pat(inst)

            # No matching identity found
            return e

        integrals = e.separate_integral()
        skolem_args = set()
        for sub_e, loc in integrals:
            new_e = apply(sub_e)
            if new_e != sub_e:
                e = e.replace_expr(loc, new_e)
                skolem_args = skolem_args.union(set(sub_e.skolem_args))
        
        if e.is_plus() and e.args[1].is_skolem_func():
            # If already has Skolem variable at right
            skolem_args = skolem_args.union(set(arg.name for arg in e.args[1].dependent_vars))
            e = e.args[0] + expr.SkolemFunc(e.args[1].name, tuple(Var(arg) for arg in skolem_args))
        else:
            # If no Skolem variable at right
            e = e + expr.SkolemFunc("C", tuple(Var(arg) for arg in skolem_args))

        return e


class ReplaceSubstitution(Rule):
    """Replace previously performed substitution"""
    def __init__(self):
        self.name = "ReplaceSubstitution"

    def __str__(self):
        return "replace substitution"

    def export(self):
        return {
            "name": self.name,
            "str": str(self)
        }

    def eval(self, e: Expr, ctx: Context) -> Expr:
        for var, expr in ctx.get_substs().items():
            e = e.subst(var, expr)
        return e


class DerivativeSimplify(Rule):
    """Simplify the derivative of an expression"""

    def __init__(self):
        self.name = "DerivativeSimplify"

    def __str__(self):
        return "simplify derivative"

    def export(self):
        return {
            "name": self.name,
            "str": str(self)
        }

    def eval(self, e: Expr, ctx: Context) -> Expr:
        if not isinstance(e, Deriv):
            return e
        return expr.deriv(e.var, e.body)


class TrigSimplify(Rule):
    """Simplifications in trigonometry."""

    def __init__(self):
        self.name = "TrigSimplify"

    def __str__(self):
        return "trigonometric simplification"

    def export(self):
        return {
            "name": self.name,
            "str": str(self)
        }

    def eval(self, e: Expr, ctx: Context) -> Expr:
        u = Symbol('u', [VAR, CONST, OP, FUN])
        rules = [
            (sin(Const(Fraction(1 / 2)) * expr.pi - u), cos(u)),
            (cos(Const(Fraction(1 / 2)) * expr.pi - u), sin(u)),
            (sin(expr.pi - u), sin(u)),
            (cos(expr.pi - u), -cos(u)),
        ]

        for pat, pat_res in rules:
            mapping = expr.match(e, pat)
            if mapping is not None:
                e = pat_res.inst_pat(mapping)
        return e


class OnSubterm(Rule):
    """Apply given rule on subterms.

    The traversal order is similar to bottom-conv: first traverse each subterm
    of the term recursively, then apply the rule to the term itself.

    """

    def __init__(self, rule: Rule):
        assert isinstance(rule, Rule)
        self.rule = rule

    def __str__(self):
        return "%s on subterms" % self.rule

    def export(self):
        res = self.rule.export()
        res['str'] += ' on subterms'
        res['loc'] = 'subterms'
        if 'latex_str' in res:
            res['latex_str'] += ' on subterms'
        return res

    def get_substs(self):
        return self.rule.get_substs()

    def eval(self, e: Expr, ctx: Context) -> Expr:
        rule = self.rule
        if e.is_var() or e.is_const() or e.is_inf() or e.is_skolem_func():
            return rule.eval(e, ctx)
        elif e.is_op():
            args = [self.eval(arg, ctx) for arg in e.args]
            return rule.eval(expr.Op(e.op, *args), ctx)
        elif e.is_fun():
            args = [self.eval(arg, ctx) for arg in e.args]
            return rule.eval(expr.Fun(e.func_name, *args), ctx)
        elif e.is_deriv():
            return rule.eval(expr.Deriv(e.var, self.eval(e.body, ctx)), ctx)
        elif e.is_integral():
            # When evaluating the body, add interval constraint to context
            ctx2 = Context(ctx)
            ctx2.add_condition(expr.Op(">", Var(e.var), e.lower))
            ctx2.add_condition(expr.Op("<", Var(e.var), e.upper))
            lower = self.eval(e.lower, ctx)
            upper = self.eval(e.upper, ctx)
            body = self.eval(e.body, ctx2)
            return rule.eval(expr.Integral(e.var, lower, upper, body), ctx)
        elif e.is_evalat():
            return rule.eval(expr.EvalAt(
                e.var, self.eval(e.lower, ctx), self.eval(e.upper, ctx),
                self.eval(e.body, ctx)), ctx)
        elif e.is_limit():
            return rule.eval(expr.Limit(e.var, e.lim, self.eval(e.body, ctx)), ctx)
        elif e.is_indefinite_integral():
            return rule.eval(expr.IndefiniteIntegral(e.var, self.eval(e.body, ctx), e.skolem_args), ctx)
        elif e.is_summation():
            return rule.eval(
                expr.Summation(e.index_var, self.eval(e.lower, ctx), self.eval(e.upper, ctx),
                               self.eval(e.body, ctx)), ctx)
        else:
            raise NotImplementedError


class OnLocation(Rule):
    """Apply given rule on subterm specified by given location."""

    def __init__(self, rule: Rule, loc):
        assert isinstance(rule, Rule)
        self.name = "OnLocation"
        self.rule = rule
        self.loc = expr.Location(loc)

    def __str__(self):
        return "%s at %s" % (self.rule, self.loc)

    def export(self):
        res = self.rule.export()
        res['str'] += ' at ' + str(self.loc)
        res['loc'] = str(self.loc)
        if 'latex_str' in res:
            res['latex_str'] += ' at ' + str(self.loc)
        return res

    def get_substs(self):
        return self.rule.get_substs()

    def eval(self, e: Expr, ctx: Context) -> Expr:
        def rec(cur_e, loc):
            if loc.is_empty():
                return self.rule.eval(cur_e, ctx)
            elif cur_e.is_var() or cur_e.is_const():
                raise AssertionError("OnLocation: invalid location")
            elif cur_e.is_op():
                assert loc.head < len(cur_e.args), "OnLocation: invalid location"
                if len(cur_e.args) == 1:
                    return Op(cur_e.op, rec(cur_e.args[0], loc.rest))
                elif len(cur_e.args) == 2:
                    if loc.head == 0:
                        return Op(cur_e.op, rec(cur_e.args[0], loc.rest), cur_e.args[1])
                    elif loc.head == 1:
                        return Op(cur_e.op, cur_e.args[0], rec(cur_e.args[1], loc.rest))
                    else:
                        raise AssertionError("OnLocation: invalid location")
                else:
                    raise NotImplementedError
            elif cur_e.is_fun():
                assert loc.head < len(cur_e.args), "OnLocation: invalid location"
                new_args = list(cur_e.args)
                new_args[loc.head] = rec(cur_e.args[loc.head], loc.rest)
                return Fun(cur_e.func_name, *tuple(new_args))
            elif cur_e.is_integral():
                if loc.head == 0:
                    return Integral(cur_e.var, cur_e.lower, cur_e.upper, rec(cur_e.body, loc.rest))
                elif loc.head == 1:
                    return Integral(cur_e.var, rec(cur_e.lower, loc.rest), cur_e.upper, cur_e.body)
                elif loc.head == 2:
                    return Integral(cur_e.var, cur_e.lower, rec(cur_e.upper, loc.rest), cur_e.body)
                else:
                    raise AssertionError("OnLocation: invalid location")
            elif cur_e.is_evalat():
                if loc.head == 0:
                    return EvalAt(cur_e.var, cur_e.lower, cur_e.upper, rec(cur_e.body, loc.rest))
                elif loc.head == 1:
                    return EvalAt(cur_e.var, rec(cur_e.lower, loc.rest), cur_e.upper, cur_e.body)
                elif loc.head == 2:
                    return EvalAt(cur_e.var, cur_e.lower, rec(cur_e.upper, loc.rest), cur_e.body)
                else:
                    raise AssertionError("OnLocation: invalid location")
            elif cur_e.is_deriv():
                assert loc.head == 0, "OnLocation: invalid location"
                return Deriv(cur_e.var, rec(cur_e.body, loc.rest))
            elif cur_e.is_limit():
                if loc.head == 0:
                    return Limit(cur_e.var, cur_e.lim, rec(cur_e.body, loc.rest), drt=cur_e.drt)
                elif loc.head == 1:
                    return Limit(cur_e.var, rec(cur_e.lim, loc.rest), cur_e.body, drt=cur_e.drt)
                else:
                    raise AssertionError("OnLocation: invalid location")
            elif cur_e.is_indefinite_integral():
                assert loc.head == 0, "OnLocation: invalid location"
                return IndefiniteIntegral(cur_e.var, rec(cur_e.body, loc.rest), cur_e.skolem_args)
            elif cur_e.is_summation():
                if loc.head == 0:
                    return Summation(cur_e.index_var, cur_e.lower, cur_e.upper, rec(cur_e.body, loc.rest))
                elif loc.head == 1:
                    return Summation(cur_e.index_var, rec(cur_e.lower, loc.rest), cur_e.upper, cur_e.body)
                elif loc.head == 2:
                    return Summation(cur_e.index_var, cur_e.lower, rec(cur_e.upper, loc.rest), cur_e.body)
                else:
                    raise AssertionError("OnLocation: invalid location")
            else:
                raise NotImplementedError

        return rec(e, self.loc)


class SimplifyPower(Rule):
    """Apply the following simplifications on powers:

    1. Collect repeated powers
        x ^ a ^ b => x ^ (a * b).

    2. Separate constants in the exponent if base is also a constant
        c1 ^ (a + c2) => c1 ^ c2 * c1 ^ a

    3. In the expression (-a) ^ n, separate out -1.
        (-a) ^ n = (-1) ^ n * a ^ n
        (-a + -b) ^ n = (-1) ^ n * (a + b) ^ n

    4. 0 ^ m = 0 where m is a positive number
    """

    def __init__(self):
        self.name = "SimplifyPower"

    def __str__(self):
        return "simplify powers"

    def export(self):
        return {
            "name": self.name,
            "str": str(self)
        }

    def eval(self, e: Expr, ctx: Context) -> Expr:
        if not e.is_power() and not (e.is_fun() and e.func_name == 'exp'):
            return e
        if e.is_fun() and e.func_name == 'exp':
            arg = e.args[0]
            if arg.is_times():
                a, b = arg.args
                if b.is_fun() and b.func_name == 'log':
                    return b.args[0] ^ a
            return e
        elif e.args[0].is_power():
            # x ^ a ^ b => x ^ (a * b)
            return e.args[0].args[0] ^ (e.args[0].args[1] * e.args[1])
        elif e.args[1].is_plus() and e.args[0].is_const() and e.args[1].args[1].is_const():
            # c1 ^ (a + c2) => c1 ^ c2 * c1 ^ a
            return (e.args[0] ^ e.args[1].args[1]) * (e.args[0] ^ e.args[1].args[0])
        elif e.args[1].is_minus() and e.args[0].is_const() and e.args[1].args[1].is_const():
            # c1 ^ (a - c2) => c1 ^ -c2 * c1 ^ a
            return (e.args[0] ^ e.args[1].args[0]) * (e.args[0] ^ (-(e.args[1].args[1])))
        elif e.args[0].is_uminus() and e.args[1].is_const():
            # (-a) ^ n = (-1) ^ n * a ^ n
            return (Const(-1) ^ e.args[1]) * (e.args[0].args[0] ^ e.args[1])
        elif e.args[0].is_minus() and e.args[0].args[0].is_uminus() and e.args[1].is_const():
            # (-a - b) ^ n = (-1) ^ n * (a + b) ^ n
            nega, negb = e.args[0].args
            return (Const(-1) ^ e.args[1]) * ((nega.args[0] + negb) ^ e.args[1])
        elif e.args[0].is_const() and e.args[0].val == 0 and ctx.get_conds().is_positive(e.args[1]):
            # 0 ^ n = 0
            return Const(0)
        elif e.args[0].is_const() and e.args[0].val == 1:
            return Const(1)
        else:
            return e


class ReduceInfLimit(Rule):
    """Reduce limit to infinity using asymptotic growth compuations."""

    def __init__(self):
        self.name = "ReduceInfLimit"

    def __str__(self):
        return "reduce infinite limits"

    def export(self):
        return {
            "name": self.name,
            "str": str(self)
        }

    def eval(self, e: Expr, ctx: Context) -> Expr:
        if e.is_limit() and e.lim == POS_INF:
            return limits.reduce_inf_limit(e.body, e.var, conds=ctx.get_conds())
        else:
            return e


class ReduceTrivLimit(Rule):
    """Reduce limits that do not involve zeros or infinities."""

    def __init__(self):
        self.name = "ReduceTrivLimit"

    def __str__(self):
        return "reduce trivial limits"

    def export(self):
        return {
            "name": self.name,
            "str": str(self)
        }

    def eval(self, e: Expr, ctx: Context) -> Expr:
        if not e.is_limit():
            return e
        if e.var not in e.body.get_vars():
            return e.body
        if e.lim in (POS_INF, NEG_INF):
            return e

        try:
            if e.is_indeterminate_form():
                return e
            # inteternimate form
            # 1. 0 * INF
            # 2. INF / INF or 0 / 0
            # if body is not indeterminate form
            body = e.body.subst(e.var, e.lim)
            return body.normalize()
        except ZeroDivisionError:
            return e

class FullSimplify(Rule):
    """Perform simplification by applying the following rules repeatedly:

    - Simplify
    - CommonIntegral
    - Linearity
    - DerivativeSimplify
    - SimplifyPower
    - ReduceInfLimit

    """

    def __init__(self):
        self.name = "FullSimplify"

    def __str__(self):
        return "full simplify"

    def export(self):
        return {
            "name": self.name,
            "str": str(self)
        }

    def eval(self, e: Expr, ctx: Context) -> Expr:
        counter = 0
        current = e
        while True:
            s = OnSubterm(Linearity()).eval(current, ctx)
            if ctx != None:
                for b in ctx.get_conds().data:
                    if b.is_v_equals():
                        s = s.subst(str(b.args[0]), b.args[1])
            s = OnSubterm(CommonIntegral()).eval(s, ctx)
            s = Simplify().eval(s, ctx)
            s = OnSubterm(DerivativeSimplify()).eval(s, ctx)
            s = OnSubterm(SimplifyPower()).eval(s, ctx)
            s = OnSubterm(SimplifyAbs()).eval(s, ctx)
            s = OnSubterm(ReduceInfLimit()).eval(s, ctx)
            s = OnSubterm(ReduceTrivLimit()).eval(s, ctx)
            s = OnSubterm(TrigSimplify()).eval(s, ctx)
            s = OnSubterm(SummationSimplify()).eval(s, ctx)
            if s == current:
                break
            current = s
            counter += 1
            if counter > 5:
                raise AssertionError("Loop in FullSimplify")
        return current


class ApplyEquation(Rule):
    """Apply the given equation for rewriting."""
    def __init__(self, eq: Expr):
        self.name = "ApplyEquation"
        self.eq = eq

    def __str__(self):
        return "apply equation: " + str(self.eq)

    def latex_str(self):
        return "apply equation \\(%s\\)" % latex.convert_expr(self.eq)

    def export(self):
        return {
            "name": self.name,
            "eq": str(self.eq),
            "str": str(self),
            "latex_str": self.latex_str()
        }

    def eval(self, e: Expr, ctx: Context) -> Expr:
        found = False
        for identity in ctx.get_lemmas():
            if self.eq == Op("=", identity.lhs, identity.rhs):
                found = True
        assert found, "ApplyEquation: lemma %s not found" % self.eq

        # First try to match the current term with left or right side.
        pat = expr.expr_to_pattern(self.eq)
        inst_lhs = expr.match(e, pat.lhs)
        inst_rhs = expr.match(e, pat.rhs)
        if inst_lhs is not None:
            tmp = pat.rhs.inst_pat(inst_lhs)
            if not tmp.has_symbol():
                return tmp
            else:
                tmp_inst_rhs = expr.match(self.eq.rhs, pat.rhs)
                return tmp.inst_pat(tmp_inst_rhs)

        if inst_rhs is not None:
            tmp = pat.lhs.inst_pat(inst_rhs)
            if not tmp.has_symbol():
                return tmp
            else:
                tmp_inst_lhs = expr.match(self.eq.lhs, pat.lhs)
                return tmp.inst_pat(tmp_inst_lhs)

        # Finally, try to solve for e in the equation.
        res = solve_for_term(self.eq, e)
        if res is not None:
            return res
        else:
            return e


class ApplyInductHyp(Rule):
    """Apply induction hypothesis."""

    def __init__(self):
        self.name = "ApplyInductHyp"

    def __str__(self):
        return "apply induction hypothesis"

    def export(self):
        return {
            "name": self.name,
            "str": str(self)
        }

    def eval(self, e: Expr, ctx: Context) -> Expr:
        for eq in ctx.get_induct_hyps():
            if e == eq.lhs:
                return eq.rhs

        # Not found
        return e


class Substitution(Rule):
    """Apply substitution u = g(x).

    var_name - str: name of the new variable.
    var_subst - Expr: expression in the original integral to be substituted.

    The identity to be applied is:

    INT x:[a, b]. f(g(x)) * g(x)' = INT u:[g(a), g(b)]. f(u)

    """

    def __init__(self, var_name: str, var_subst: Expr):
        assert isinstance(var_name, str) and isinstance(var_subst, Expr)
        self.name = "Substitution"
        self.var_name = var_name
        self.var_subst = var_subst
        self.f = None  # After application, record f here

    def __str__(self):
        return "substitute %s for %s" % (self.var_name, self.var_subst)

    def export(self):
        return {
            "name": self.name,
            "var_name": self.var_name,
            "var_subst": str(self.var_subst),
            "str": str(self),
            "latex_str": "substitute \\(%s\\) for \\(%s\\)" % \
                         (self.var_name, latex.convert_expr(self.var_subst))
        }
    
    def get_substs(self):
        return {self.var_name: self.var_subst}

    def eval(self, e: Expr, ctx: Context) -> Expr:
        """
        Parameters:
        e: Expr, the integral on which to perform substitution.

        Returns:
        The new integral e', and stores in self.f the parameter used to
        specify the substitution.

        """
        if not (e.is_integral() or e.is_indefinite_integral()):
            sep_ints = e.separate_integral()
            if len(sep_ints) == 0:
                return e
            else:
                return OnLocation(self, sep_ints[0][1]).eval(e, ctx)

        # Variable to be substituted in the integral
        var_name = parser.parse_expr(self.var_name)

        # Expression used for substitution
        var_subst = self.var_subst

        dfx = expr.deriv(e.var, var_subst)
        body = (e.body / dfx).normalize()
        body_subst = body.replace(var_subst, var_name)
        if e.var not in body_subst.get_vars():
            # Substitution is able to clear all x in original integrand
            self.f = body_subst
        else:
            # Substitution is unable to clear x, need to solve for x
            gu = solve_equation(var_subst, var_name, e.var)
            if gu is None:
                print('Solve %s = %s for %s' % (var_subst, var_name, e.var))
                raise AssertionError("Substitution: unable to solve equation")

            gu = gu.normalize()
            c = e.body.replace(parser.parse_expr(e.var), gu)
            new_problem_body = c * expr.deriv(str(var_name), gu)
            self.f = new_problem_body

        if e.is_integral():
            if e.lower == expr.NEG_INF:
                lower = limits.reduce_inf_limit(var_subst.subst(e.var, -Var(e.var)), e.var, ctx.get_conds())
            else:
                lower = var_subst.subst(e.var, e.lower).normalize()
            if e.upper == expr.POS_INF:
                upper = limits.reduce_inf_limit(var_subst, e.var, ctx.get_conds())
            else:
                upper = var_subst.subst(e.var, e.upper).normalize()
            if lower.is_evaluable() and upper.is_evaluable() and expr.eval_expr(lower) > expr.eval_expr(upper):
                return Integral(self.var_name, upper, lower, Op("-", self.f)).normalize()
            else:
                return Integral(self.var_name, lower, upper, self.f).normalize()
        elif e.is_indefinite_integral():
            return IndefiniteIntegral(self.var_name, self.f, e.skolem_args).normalize()
        else:
            raise TypeError


class SubstitutionInverse(Rule):
    """Apply substitution x = f(u).

    var_name - str: name of the new variable u.
    var_subst - Expr: expression containing the new variable.

    """

    def __init__(self, var_name: str, var_subst: Expr):
        self.name = "SubstitutionInverse"
        self.var_name = var_name
        self.var_subst = var_subst

    def __str__(self):
        return "inverse substitution for %s" % self.var_subst

    def export(self):
        return {
            "name": self.name,
            "var_name": self.var_name,
            "var_subst": str(self.var_subst),
            "str": str(self),
            "latex_str": "inverse substitution for \\(%s\\)" % latex.convert_expr(self.var_subst)
        }

    def eval(self, e: Expr, ctx: Context) -> Expr:
        if not e.is_integral():
            sep_ints = e.separate_integral()
            if len(sep_ints) == 0:
                return e
            else:
                return OnLocation(self, sep_ints[0][1]).eval(e, ctx)

        # dx = f'(u) * du
        subst_deriv = expr.deriv(self.var_name, self.var_subst)

        # Replace x with f(u)
        new_e_body = e.body.replace(Var(e.var), self.var_subst)

        # g(x) = g(x(u)) * f'(u)
        new_e_body = new_e_body * subst_deriv

        # Solve the equations lower = f(u) and upper = f(u) for u.
        lower = solve_equation(self.var_subst, e.lower, self.var_name)
        upper = solve_equation(self.var_subst, e.upper, self.var_name)

        if lower is None or upper is None:
            raise AssertionError("SubstitutionInverse: cannot solve")

        lower = lower.normalize()
        upper = upper.normalize()
        if lower.is_evaluable() and upper.is_evaluable() and expr.eval_expr(lower) > expr.eval_expr(upper):
            return -expr.Integral(self.var_name, upper, lower, new_e_body)
        else:
            return expr.Integral(self.var_name, lower, upper, new_e_body)


class ExpandPolynomial(Rule):
    """Expand multiplication and power."""

    def __init__(self):
        self.name = "ExpandPolynomial"

    def __str__(self):
        return "expand polynomial"

    def export(self):
        return {
            "name": self.name,
            "str": str(self)
        }

    def eval(self, e: Expr, ctx: Context) -> Expr:
        if e.is_power() and e.args[1].is_const() and e.args[1].val > 1 and \
                int(e.args[1].val) == e.args[1].val:
            n = int(e.args[1].val)
            base = self.eval(e.args[0], ctx).to_poly()
            res = base
            for i in range(n - 1):
                res = res * base
            return expr.from_poly(res)
        elif e.is_times():
            s1, s2 = self.eval(e.args[0], ctx), self.eval(e.args[1], ctx)
            return expr.from_poly(s1.to_poly() * s2.to_poly())
        elif e.is_integral():
            return expr.Integral(e.var, e.lower, e.upper, self.eval(e.body, ctx))
        else:
            return e


class Equation(Rule):
    """Apply substitution for equal expressions"""

    def __init__(self, new_expr: Expr, denom=None, old_expr: Optional[Expr] = None):
        self.name = "Equation"
        assert isinstance(new_expr, Expr)
        self.new_expr = new_expr
        self.denom = denom
        self.old_expr = old_expr

    def __str__(self):
        if self.old_expr is None:
            return "rewriting to %s" % self.new_expr
        else:
            return "rewriting %s to %s" % (self.old_expr, self.new_expr)

    def export(self):
        if self.old_expr is None:
            latex_str = "rewriting to \\(%s\\)" % latex.convert_expr(self.new_expr)
        else:
            latex_str = "rewriting \\(%s\\) to \\(%s\\)" % \
                (latex.convert_expr(self.old_expr), latex.convert_expr(self.new_expr))
        res = {
            "name": self.name,
            "new_expr": str(self.new_expr),
            "str": str(self),
            "latex_str": latex_str
        }
        if self.old_expr:
            res['old_expr'] = str(self.old_expr)
        return res

    def eval(self, e: Expr, ctx: Context) -> Expr:
        # If old_expr is given, try to find it within e
        old_expr = self.old_expr
        if old_expr is not None and old_expr != e:
            find_res = e.find_subexpr(old_expr)
            if len(find_res) == 0:
                raise AssertionError("Equation: old expression not found")
            loc = find_res[0]
            return OnLocation(self, loc).eval(e, ctx)

        if old_expr == e:
            r = FullSimplify()
            if r.eval(e, ctx) == r.eval(self.new_expr, ctx):
                return self.new_expr
            a = Symbol('a', [VAR, CONST, OP, FUN])
            b = Symbol('b', [VAR, CONST, OP, FUN])
            c = Symbol('c', [VAR, CONST, OP, FUN])
            rules = [
                (log(a ^ b), b * log(a)),
                ((a * b) ^ c, (a ^ c) * (b ^ c)),
                ((a ^ c) * (b ^ c), (a * b) ^ c),
            ]
            for pat, pat_res in rules:
                pos = expr.find_pattern(e, pat)
                if len(pos) >= 1:
                    mapped_expr, loc, mapping = pos[0]
                    if mapped_expr == e:
                        if r.eval(pat_res.inst_pat(mapping), ctx) == r.eval(self.new_expr, ctx):
                            return self.new_expr
            def rec(se):
                return rec(se.expand()) if (se.expand() != se) else se



            if expand_multinomial(rec(rec(expr.sympy_style(self.new_expr)).simplify())) != \
                    expand_multinomial(rec(rec(expr.sympy_style(self.old_expr)).simplify())):
                raise AssertionError("Rewriting by equation failed")
            return self.new_expr
        # Currently rewrite using SymPy.
        # TODO: change to own implementation.
        if expand_multinomial(expr.sympy_style(self.new_expr.normalize()).simplify()) != \
                expand_multinomial(expr.sympy_style(e.normalize()).simplify()):
            raise AssertionError("Rewriting by equation failed")

        # if self.denom is None:
        #     if self.new_expr.normalize() != e.normalize():
        #         raise AssertionError("Rewriting by equation failed")
        # else:
        #     if (self.new_expr * self.denom).normalize() != (e * self.denom).normalize():
        #         raise AssertionError("Rewriting by equation failed")
        return self.new_expr


class IntegrationByParts(Rule):
    """Apply integration by parts.

    The arguments u and v should satisfy u * dv equals the integrand.

    """
    def __init__(self, u: Expr, v: Expr):
        self.name = "IntegrationByParts"
        assert isinstance(u, Expr) and isinstance(v, Expr)
        self.u = u
        self.v = v

    def __str__(self):
        return "integrate by parts u -> %s, v -> %s" % (self.u, self.v)

    def export(self):
        return {
            "name": self.name,
            "u": str(self.u),
            "v": str(self.v),
            "str": str(self),
            "latex_str": "integrate by parts \\(u \\to %s, v \\to %s\\)" % \
                         (latex.convert_expr(self.u), latex.convert_expr(self.v))
        }

    def eval(self, e: Expr, ctx: Context) -> Expr:
        if not (e.is_integral() or e.is_indefinite_integral()):
            sep_ints = e.separate_integral()
            if len(sep_ints) == 0:
                return e
            else:
                return OnLocation(self, sep_ints[0][1]).eval(e, ctx)

        e.body = e.body.normalize()
        du = expr.deriv(e.var, self.u)
        dv = expr.deriv(e.var, self.v)
        udv = (self.u * dv).normalize()
        se = expr.sympy_style(udv).simplify()
        udv = expr.holpy_style(se).normalize()

        if udv == e.body:
            if e.is_integral():
                return expr.EvalAt(e.var, e.lower, e.upper, (self.u * self.v).normalize()) - \
                       expr.Integral(e.var, e.lower, e.upper, (self.v * du).normalize())
            elif e.is_indefinite_integral():
                return (self.u * self.v).normalize() - \
                       expr.IndefiniteIntegral(e.var, (self.v * du).normalize(), e.skolem_args)
        else:
            print("%s != %s" % (str(udv), str(e.body)))
            raise NotImplementedError("%s != %s" % (str(udv), str(e.body)))


class PolynomialDivision(Rule):
    """Simplify the representation of polynomial divided by polynomial.
    """

    def __init__(self):
        self.name = "PolynomialDivision"

    def __str__(self):
        return "polynomial division"

    def export(self):
        return {
            "name": self.name,
            "str": str(self)
        }

    def eval(self, e: Expr, ctx: Context) -> Expr:
        if not e.is_integral():
            sep_ints = e.separate_integral()
            if len(sep_ints) == 0:
                return e
            else:
                return OnLocation(self, sep_ints[0][1]).eval(e, ctx)

        result = apart(expr.sympy_style(e.body))
        new_expr = expr.holpy_style(result)
        return expr.Integral(e.var, e.lower, e.upper, new_expr)


class RewriteTrigonometric(Rule):
    """Rewrite using one of Fu's rules."""

    def __init__(self, rule_name: str, rewrite_term: Optional[Expr] = None):
        self.name = "RewriteTrigonometric"
        self.rule_name = rule_name
        self.rewrite_term = rewrite_term

    def __str__(self):
        if self.rewrite_term is None:
            return "rewrite trigonometric"
        else:
            return "rewrite trigonometric on %s" % self.rewrite_term

    def export(self):
        res = {
            "name": self.name,
            "rule_name": self.rule_name,
            "str": str(self)
        }
        if self.rewrite_term is not None:
            res['rewrite_term'] = str(self.rewrite_term)
            res['latex_str'] = "rewrite trigonometric on \\(%s\\)" % \
                               latex.convert_expr(self.rewrite_term)
        return res

    def eval(self, e: Expr, ctx: Context) -> Expr:
        # Rewrite on a subterm
        if self.rewrite_term is not None and self.rewrite_term != e:
            find_res = e.find_subexpr(self.rewrite_term)
            if len(find_res) == 0:
                raise AssertionError("RewriteTrigonometric: rewrite term not found")
            loc = find_res[0]
            return OnLocation(self, loc).eval(e, ctx)

        # Select one of Fu's rules
        rule_fun, _ = expr.trigFun[self.rule_name]
        sympy_result = rule_fun(expr.sympy_style(e))
        result = expr.holpy_style(sympy_result)
        return result


class SplitRegion(Rule):
    """Split integral into two parts at a point."""

    def __init__(self, c: Expr):
        self.name = "SplitRegion"
        self.c = c

    def __str__(self):
        return "split region at %s" % self.c

    def export(self):
        return {
            "name": self.name,
            "c": str(self.c),
            "str": str(self)
        }

    def eval(self, e: Expr, ctx: Context) -> Expr:
        if not e.is_integral():
            sep_ints = e.separate_integral()
            if len(sep_ints) == 0:
                return e
            else:
                return OnLocation(self, sep_ints[0][1]).eval(e, ctx)

        return expr.Integral(e.var, e.lower, self.c, e.body) + \
               expr.Integral(e.var, self.c, e.upper, e.body)


class IntegrateByEquation(Rule):
    """When the initial integral occurs in the steps."""

    def __init__(self, lhs: Expr):
        self.name = "IntegrateByEquation"
        self.lhs = lhs.normalize()
        self.coeff = None

    def __str__(self):
        return "integrate by equation"

    def export(self):
        return {
            "name": self.name,
            "lhs": str(self.lhs),
            "str": str(self)
        }

    def validate(self, e: Expr) -> bool:
        """Determine whether the lhs exists in e."""
        integrals = e.separate_integral()
        if not integrals:
            return False
        for i, j in integrals:
            if i.normalize() == self.lhs:
                return True
        return False

    def eval(self, e: Expr, ctx: Context) -> Expr:
        """Eliminate the lhs's integral in rhs by solving equation."""
        norm_e = e.normalize()
        rhs_var = None

        def get_coeff(t: Expr):
            nonlocal rhs_var
            if t == self.lhs:
                if t.is_integral():
                    rhs_var = t.var
                return Const(1)

            if t.is_plus():
                return get_coeff(t.args[0]) + get_coeff(t.args[1])
            elif t.is_minus():
                return get_coeff(t.args[0]) - get_coeff(t.args[1])
            elif t.is_uminus():
                return -get_coeff(t.args[0])
            elif t.is_times():
                return t.args[0] * get_coeff(t.args[1])
            else:
                return Const(0)

        coeff = get_coeff(norm_e).normalize()
        if coeff == Const(0):
            return e

        if rhs_var != None:
            new_rhs = (norm_e + ((-coeff) * self.lhs.alpha_convert(rhs_var))).normalize()
        else:
            new_rhs = (norm_e + ((-coeff) * self.lhs)).normalize()
        self.coeff = (-(coeff)).normalize()
        return (new_rhs / ((Const(1) - coeff))).normalize()


class ElimInfInterval(Rule):
    """Convert improper integral with infinite upper or lower limits to
    a limit expression.

    If both upper and lower limits are infinity, a split point need to be
    provided.

    """
    def __init__(self, a=Const(0), new_var='t'):
        self.name = "ElimInfInterval"
        self.a = a
        self.new_var = new_var

    def __str__(self):
        return "eliminate improper integral"

    def export(self):
        return {
            "name": self.name,
            "a": str(self.a),
            "str": str(self)
        }

    def eval(self, e: Expr, ctx: Context) -> Expr:
        def gen_lim_expr(new_var, lim, lower, upper, drt=None):
            return expr.Limit(new_var, lim, expr.Integral(e.var, lower, upper, e.body), drt)

        if not e.is_integral():
            sep_ints = e.separate_integral()
            if len(sep_ints) == 0:
                return e
            else:
                return OnLocation(self, sep_ints[0][1]).eval(e, ctx)

        inf = Inf(Decimal('inf'))
        neg_inf = Inf(Decimal('-inf'))
        upper, lower = e.upper, e.lower
        new_var = self.new_var

        if upper == inf and lower != neg_inf and lower != inf:
            # INT x:[a,oo]. body => lim t->oo. INT x:[a,t]. body
            return gen_lim_expr(new_var, inf, lower, Var(new_var))
        elif upper == neg_inf and lower != neg_inf and lower != inf:
            return gen_lim_expr(new_var, inf, lower, Var(new_var))
        elif upper != inf and upper != neg_inf and lower == neg_inf:
            # INT x:[-oo,a]. body => lim t->-oo. INT x:[t,a]. body
            return gen_lim_expr(new_var, neg_inf, Var(new_var), upper)
        elif upper != inf and upper != neg_inf and lower == inf:
            return gen_lim_expr(new_var, inf, Var(new_var), upper)
        elif upper == inf and lower == neg_inf:
            # INT x:[-oo,oo]. body =>
            # lim t->-oo. INT x:[t,a]. body + lim t->oo. INT x:[a,t]. body
            assert self.a is not None, "No split point provided"
            lim1 = gen_lim_expr(new_var, neg_inf, Var(new_var), self.a)
            lim2 = gen_lim_expr(new_var, inf, self.a, Var(new_var))
            return Op('+', lim1, lim2)
        elif upper == neg_inf and lower == inf:
            assert self.a is not None, "No split point provided"
            lim1 = gen_lim_expr(new_var, inf, Var(new_var), self.a)
            lim2 = gen_lim_expr(new_var, neg_inf, self.a, Var(new_var))
            return Op('+', lim1, lim2)
        else:
            raise NotImplementedError


class LHopital(Rule):
    """Apply L'Hoptial rule."""

    def __init__(self):
        self.name = "LHopital"

    def __str__(self):
        return "l'Hopital's rule"

    def export(self):
        return {
            "name": self.name,
            "str": str(self)
        }

    def eval(self, e: Expr, ctx: Context) -> Expr:
        if not isinstance(e, expr.Limit):
            return e

        if not (isinstance(e.body, expr.Op) and e.body.op == '/'):
            return e
        # if not e.is_indeterminate_form():
        #     return e
        numerator, denominator = e.body.args
        rule = DerivativeSimplify()
        return expr.Limit(e.var, e.lim, Op('/', rule.eval(Deriv(e.var, numerator), ctx),
                                           rule.eval(Deriv(e.var, denominator), ctx)), e.drt)


def check_item(item, target=None, *, debug=False):
    """Check application of rules in the item."""
    problem = parser.parse_expr(item['problem'])

    if debug:
        print("\n%s: %s" % (item['name'], problem))

    current = problem
    prev_steps = []
    ctx = Context()

    for step in item['calc']:
        reason = step['reason']
        expected = parser.parse_expr(step['text'])

        if reason == 'Initial':
            result = current

        elif reason == 'Simplification':
            if "location" in step:
                result = OnLocation(FullSimplify(), step["location"]).eval(current, ctx)
            else:
                result = FullSimplify().eval(current, ctx)

        elif reason == 'Substitution':
            var_name = step['params']['var_name']
            f = parser.parse_expr(step['params']['f'])
            g = parser.parse_expr(step['params']['g'])
            rule = Substitution(var_name, g)
            if 'location' in step:
                result = OnLocation(rule, step['location']).eval(current, ctx)
            else:
                result = rule.eval(current, ctx)
            rule.f = parser.parse_expr(str(rule.f))  # trick to eliminate difference in printing
            if rule.f != f:
                print("Expected f: %s" % f)
                print("Actual f: %s" % rule.f)
                raise AssertionError("Unexpected value of f in substitution")

        elif reason == 'Integrate by parts':
            u = parser.parse_expr(step['params']['parts_u'])
            v = parser.parse_expr(step['params']['parts_v'])
            rule = IntegrationByParts(u, v)
            if 'location' in step:
                result = OnLocation(rule, step['location']).eval(current, ctx)
            else:
                result = rule.eval(current, ctx)

        elif reason == 'Rewrite fraction':
            rule = PolynomialDivision()
            if 'location' in step:
                result = OnLocation(rule, step['location']).eval(current, ctx)
            else:
                result = rule.eval(current, ctx)

        elif reason == 'Rewrite':
            rhs = parser.parse_expr(step['params']['rhs'])
            if 'denom' in step['params']:
                rule = Equation(rhs, parser.parse_expr(step['params']['denom']))
            else:
                rule = Equation(rhs)
            if 'location' in step:
                result = OnLocation(rule, step['location']).eval(current, ctx)
            else:
                result = rule.eval(current, ctx)

        elif reason == 'Rewrite trigonometric':
            rule = RewriteTrigonometric(step['params']['rule'])
            if 'location' in step:
                result = OnLocation(rule, step['location']).eval(current, ctx)
            else:
                result = rule.eval(current, ctx)

        elif reason == 'Substitution inverse':
            var_name = step['params']['var_name']
            g = parser.parse_expr(step['params']['g'])
            rule = SubstitutionInverse(var_name, g)
            if 'location' in step:
                result = OnLocation(rule, step['location']).eval(current, ctx)
            else:
                result = rule.eval(current, ctx)

        elif reason == 'Split region':
            c = parser.parse_expr(step['params']['c'])
            rule = SplitRegion(c)
            if 'location' in step:
                result = OnLocation(rule, step['location']).eval(current, ctx)
            else:
                result = rule.eval(current, ctx)

        elif reason == 'Unfold power':
            rule = UnfoldPower()
            if 'location' in step:
                result = OnLocation(rule, step['location']).eval(current, ctx)
            else:
                result = rule.eval(current, ctx)

        elif reason == 'Solve equation':
            prev_id = int(step['params']['prev_id'])
            rule = IntegrateByEquation(prev_steps[prev_id])
            result = rule.eval(current, ctx)

        else:
            print("Reason: %s" % reason)
            raise NotImplementedError

        if result != expected:
            print("Expected: %s" % expected)
            print("Result: %s" % result)
            raise AssertionError("Error on intermediate step (%s)" % reason)

        current = result
        prev_steps.append(current)

    if target is not None:
        target = parser.parse_expr(target)
        if current != target:
            print("Target: %s" % target)
            print("Result: %s" % current)
            raise AssertionError("Error on final answer")


class DerivIntExchange(Rule):
    """Exchanging derivative and integral"""

    def __init__(self):
        self.name = "DerivIntExchange"

    def __str__(self):
        return "exchange derivative and integral"

    def export(self):
        return {
            "name": self.name,
            "str": str(self)
        }

    def eval(self, e: Expr, ctx: Context) -> Expr:
        if e.is_deriv() and e.body.is_integral():
            v1, v2 = e.var, e.body.var
            return Integral(v2, e.body.lower, e.body.upper, Deriv(v1, e.body.body))
        elif e.is_deriv() and e.body.is_indefinite_integral():
            return IndefiniteIntegral(e.var, Deriv(e.var, e.body.body), e.skolem_args)
        elif e.is_indefinite_integral() and e.body.is_deriv():
            return Deriv(e.var, IndefiniteIntegral(e.var, e.body.body, e.skolem_args))
        else:
            raise NotImplementedError


class ExpandDefinition(Rule):
    """Expand a definition"""

    def __init__(self, func_name: str):
        self.name = "ExpandDefinition"
        assert isinstance(func_name, str)
        self.func_name: str = func_name

    def __str__(self):
        return "expand definition"

    def export(self):
        return {
            "name": self.name,
            "func_name": self.func_name,
            "str": str(self)
        }

    def eval(self, e: Expr, ctx: Context) -> Expr:
        if e.is_fun() and e.func_name == self.func_name:
            for identity in ctx.get_definitions():
                if identity.lhs.is_fun() and identity.lhs.func_name == self.func_name:
                    inst = expr.match(e, identity.lhs)
                    return identity.rhs.inst_pat(inst).normalize()
        if e.is_var() and e.name == self.func_name:
            for identity in ctx.get_definitions():
                if identity.lhs.is_symbol() and identity.lhs.name == self.func_name:
                    return identity.rhs

        # Not found
        return e


class RootFractionReWrite(Rule):
    """Rewrite nth root fraction

        a^(1/n) / b^(1/m)  ->  (a^(x) / b^(y))^(1/z), where
        z = lcm(n,m), x = z/n, y = z/m

    """
    def __init__(self):
        self.name = "RootFractionReWrite"

    def __str__(self):
        return "rewrite root fraction"

    def export(self):
        return {
            "name": self.name,
            "str": str(self)
        }

    def eval(self, e: Expr, ctx: Context) -> Expr:
        if e.ty != OP and e.op != '/':
            return e

        a, b = e.args
        if a.ty == FUN and a.func_name == 'sqrt':
            n = 2
            a = a.args[0]
        elif a.ty == OP and a.op == '^':
            c = a.args[1]
            if c.ty == CONST:
                c = Fraction(c.val)
            if isinstance(c, Fraction) and c.numerator == 1 and isinstance(c.denominator, int):
                n = c.denominator
                a = a.args[0]
            else:
                raise NotImplementedError
        else:
            n = 1

        if b.ty == FUN and b.func_name == 'sqrt':
            m = 2
            b = b.args[0]
        elif b.ty == OP and b.op == '^':
            c = b.args[1]
            if c.ty == CONST:
                c = Fraction(c.val)
            if isinstance(c, Fraction) and c.numerator == 1 and isinstance(c.denominator, int):
                m = c.denominator
                b = b.args[0]
            else:
                raise NotImplementedError
        else:
            m = 1
        l = int(sympy.lcm(n, m))
        return ((a ^ fractions.Fraction(l, n)) / (b ^ fractions.Fraction(l, m))) ^ Fraction(1, l);


class ExtractFromRoot(Rule):
    """Extract a expression u from root expression e

        e = sqrt(x*x + x)
        u = x and x<0
        e -> -x * sqrt(x*x / x^2 + x/x^2)

    """
    # sign : positive is 1, negative is -1
    def __init__(self, u: Expr):
        self.name = "ExtractFromRoot"
        self.u = u

    def __str__(self):
        return "extraction from root"

    def export(self):
        return {
            "name": self.name,
            "u": str(self.u),
            "str": str(self)
        }

    def eval(self, e: Expr, ctx: Context) -> Expr:
        if not isinstance(e, Expr):
            raise AssertionError("ExtractFromRoot: wrong form for e.")
        if e.ty == FUN and e.func_name == 'sqrt':
            if self.sign == -1:
                return -self.u * expr.Fun('sqrt', e.args[0] / (self.u ^ 2))
        else:
            raise NotImplementedError


class SimplifyAbs(Rule):
    def __init__(self):
        self.name = "SimplifyAbs"

    def __str__(self):
        return "SimplifyAbs"

    def export(self):
        return {
            "name": self.name,
            "str": str(self)
        }

    def eval(self, e: Expr, ctx: Context) -> Expr:
        if e.is_fun() and e.func_name == "abs":
            if ctx.get_conds().is_not_negative(e.args[0]):
                return e.args[0]
            elif ctx.get_conds().is_not_positive(e.args[0]):
                return -e.args[0]
            else:
                return e
        else:
            return e


class IntegralEquation(Rule):
    """Integrate an equation where the left side is a derivative.

    Convert (D a. f(a)) = g(a) into f(a) = INT a. g(a). The right side
    can then be evaluated to produce a Skolem constant.

    """
    def __init__(self):
        self.name = "IntegrateBothSide"

    def eval(self, e: Expr, ctx: Context):
        assert e.is_equals() and e.lhs.is_deriv()

        # Variable to differentiate, this will also be the variable
        # of integration.
        var = e.lhs.var

        # List of Skolem arguments is the free variables on the left side
        skolem_args = e.lhs.get_vars()

        # Return f(a) = INT a. g(a)
        return Op("=", e.lhs.body, IndefiniteIntegral(var, e.rhs, skolem_args))

    def __str__(self):
        return "integrate both side"

    def export(self):
        return {
            "name": self.name,
            "str": str(self),
        }


class LimitEquation(Rule):
    """Apply limit to both sides of the equation.
    
        A = B -> LIM {x -> a}. A = LIM {x -> a}. B

    """
    def __init__(self, var: str, lim: Expr):
        self.name = "LimitEquation"
        self.var: str = var
        self.lim: Expr = lim

    def __str__(self):
        return "apply limit %s -> %s to equation" % (self.var, self.lim)

    def eval(self, e: Expr, ctx: Context):
        v, lim = self.var, self.lim
        lim1 = Limit(v, lim, e.lhs)
        lim2 = Limit(v, lim, e.rhs)
        return Op('=', lim1, lim2)

    def export(self):
        return {
            "name": self.name,
            "str": str(self),
            "var": self.var,
            "lim": str(self.lim),
            "latex_str": "apply limit \\(%s \\to %s\\) to equation" %
                (self.var, latex.convert_expr(self.lim))
        }


class IntSumExchange(Rule):
    """Exchange integral and summation"""

    def __init__(self):
        self.name = "IntSumExchange"

    def __str__(self):
        return "exchange integral and sum"

    def eval(self, e: Expr, ctx: Context):
        if e.is_integral() and e.body.is_summation():
            s = e.body
            return Summation(s.index_var, s.lower, s.upper, Integral(e.var, e.lower, e.upper, e.body.body))
        else:
            return e

    def export(self):
        return {
            "name": self.name,
            "str": str(self)
        }


class VarSubsOfEquation(Rule):
    """Substitute variable for any expression in an equation.
    """

    def __init__(self, var: str, var_subs: Expr):
        self.name = "VarSubsOfEquation"
        self.var = var
        self.var_subs = var_subs

    def __str__(self):
        return "substitute " + str(self.var) + " for " + str(self.var_subs) + " in equation"

    def export(self):
        return {
            "name": self.name,
            "str": str(self),
            "var": self.var,
            "var_subs": str(self.var_subs),
            "latex_str": "substitute \\(%s\\) for \\(%s\\) in equation" % (self.var, latex.convert_expr(self.var_subs))
        }

    def eval(self, e: Expr, ctx: Context) -> Expr:
        if e.is_equals():
            return e.subst(self.var, self.var_subs)
        else:
            return e


class MergeSummation(Rule):
    "SUM(u,0,oo, body1) + SUM(k,0,oo,body2) = SUM(u, 0, oo, body1+body2)"
    def __init__(self):
        self.name = "MergeSummation"

    def __str__(self):
        return "merge summation"

    def export(self):
        return {
            "name": self.name,
            "str": str(self)
        }

    def eval(self, e: Expr, ctx: Context) -> Expr:
        if not(e.ty == OP and e.op in ('+', '-') and all([isinstance(arg, Summation) for arg in e.args])):
            return e
        a, b = e.args
        if not(a.lower == b.lower and a.upper == b.upper):
            return e
        if a.index_var != b.index_var:
            b = b.alpha_convert(a.index_var)
        return Summation(a.index_var, a.lower, a.upper, Op(e.op, a.body, b.body))


class SummationSimplify(Rule):
    """Replace (-1)^(2x) by 1 in the body of summation.
    
    TODO: replace with more robust tactic.
    
    """
    def __init__(self):
        self.name = "SummationSimplify"

    def __str__(self):
        return "summation simplify"

    def export(self):
        return {
            "name": self.name,
            "str": str(self)
        }

    def eval(self, e: Expr, ctx: Context) -> Expr:
        if not e.is_summation():
            return e
        e = e.replace((Const(-1))^(Const(2)*Var(e.index_var)), Const(1))
        return e


class DerivEquation(Rule):
    """Differentiate both sides with respect to some variable."""

    def __init__(self, var: str):
        self.name = "DerivEquation"
        self.var: str = var

    def __str__(self):
        return "derivate both sides"

    def export(self):
        return {
            "name": self.name,
            "str": str(self),
            "var": self.var
        }

    def eval(self, e: Expr, ctx: Context) -> Expr:
        if not e.is_equals():
            return e
        return Op('=', Deriv(self.var, e.lhs), Deriv(self.var, e.rhs))


class RewriteMulPower(Rule):
    """Merge expression into a power expression.

        a * sqrt(b) -> sqrt(a^2 * b) if be_merged_idx = 0
        (x+3)^(-2) * y -> ((x+3) * y^(-1/2))^(-2) if be_merged_idx = 1

    """
    def __init__(self, be_merged_idx: int):
        assert be_merged_idx in (0, 1)
        self.be_merged_idx = be_merged_idx
        self.name = "RewriteMulPower"

    def __str__(self):
        return "rewrite expression multiplied a power expression"

    def eval(self, e: Expr, ctx: Context):
        if not isinstance(e, Op) or not e.op == '*':
            return e
        idx = self.be_merged_idx
        res = e
        r = ExpandPolynomial()
        if e.args[1 - idx].is_fun() and e.args[1 - idx].func_name == 'sqrt':
            res = Fun('sqrt', r.eval(((e.args[idx] ^ 2) * e.args[1 - idx].args[0]).normalize()))
        elif e.args[1 - idx].is_power():
            res = Op('^', r.eval(((e.args[idx] ^ (1 / e.args[1 - idx].args[1])) * e.args[1 - idx].args[0]).normalize(), ctx),
                     e.args[1 - idx].args[1])
        return res

    def export(self):
        return {
            "name": self.name,
            "str": str(self),
            "merged_idx": self.be_merged_idx
        }


class SolveEquation(Rule):
    """Solve equation for the given expression."""
    def __init__(self, be_solved_expr: Expr):
        self.be_solved_expr = be_solved_expr
        self.name = "SolveEquation"

    def eval(self, e: Expr, ctx: Context):
        assert e.is_equals()

        res = solve_for_term(e, self.be_solved_expr)
        if not res:
            raise AssertionError("SolveEquation: cannot solve")
        return Op("=", self.be_solved_expr, res.normalize())

    def __str__(self):
        return "solve equation for %s" % str(self.be_solved_expr)

    def export(self):
        return {
            "name": self.name,
            "str": str(self),
            "solve_for": str(self.be_solved_expr),
            "latex_str": "solve equation for \\(%s\\)" % latex.convert_expr(self.be_solved_expr)
        }
