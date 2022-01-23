"""Rules for integration."""

from integral import expr
from integral import poly
from integral.expr import Var, Const, Fun, EvalAt, Op, Integral, Symbol, Expr, trig_identity, \
        sympy_style, holpy_style, OP, CONST, INTEGRAL, VAR, sin, cos, FUN, decompose_expr_factor
import functools, operator
from integral import parser
from sympy import Interval, expand_multinomial, apart
from sympy.solvers import solvers, solveset
from integral import parser
from fractions import Fraction
import copy
import random
import string

class Rule:
    """Represents a rule for integration. It takes an integral
    to be evaluated (as an expression), then outputs a new
    expression that it is equal to.
    
    """
    def eval(self, e):
        """Evaluation of the rule on the given expression. Returns
        a new expression.

        """
        raise NotImplementedError

class Simplify(Rule):
    """Perform algebraic simplification. This treats the
    expression as a polynomial, and normalizes the polynomial.

    """
    def __init__(self):
        self.name = "Simplify"
    
    def eval(self, e):
        if isinstance(e, str):
            e = parser.parse_expr(e)
        res = e.normalize()
        if res.is_inf():
            raise ValueError
        else:
            return res

class Linearity(Rule):
    """Applies linearity rules:
    
    INT (a + b) = INT a + INT b,
    INT (c * a) = c * INT a  (where c is a constant).
    INT (c / a) = c * INT 1 / a (where c is a contant)
    """
    def __init__(self):
        self.name = "Linearity"
    
    def eval(self, e):
        if isinstance(e, str):
            e = parser.parse_expr(e)

        if e.ty != expr.INTEGRAL:
            return e

        rec = Linearity().eval

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
            if factors[0].is_constant():
                return factors[0] * rec(expr.Integral(e.var, e.lower, e.upper, 
                            functools.reduce(lambda x, y: x * y, factors[2:], factors[1])))
            else:
                return e
        elif e.body.is_constant() and e.body != Const(1):
            return e.body * expr.Integral(e.var, e.lower, e.upper, Const(1))
        else:
            return e

class CommonIntegral(Rule):
    """Applies common integrals:

    INT c = c * x,
    INT x ^ n = x ^ (n + 1) / (n + 1),  (where n != -1, c is a constant)
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

    def eval(self, e):
        if isinstance(e, str):
            e = parser.parse_expr(e)
        if e.ty != expr.INTEGRAL:
            return e

        if e.body.is_constant() and e.body != Const(1):
            return EvalAt(e.var, e.lower, e.upper, e.body * Var(e.var))

        x = Var(e.var)
        c = Symbol('c', [CONST])
        rules = [
            (Const(1), None, Var(e.var)),
            (c, None, c * Var(e.var)),
            (x, None, (x ^ 2) / 2),
            (x ^ c, lambda m: m[c].val != -1, lambda m: (x ^ Const(m[c].val + 1)) / (Const(m[c].val + 1))),
            (Const(1) / x ^ c, lambda m: m[c].val != 1, (-c) / (x ^ (c + 1))),
            (expr.sqrt(x), None, Fraction(2,3) * (x ^ Fraction(3,2))),
            (sin(x), None, -cos(x)),
            (cos(x), None, sin(x)),
            (expr.exp(x), None, expr.exp(x)),
            (Const(1) / x, None, expr.log(expr.Fun('abs', x))),
            (x ^ Const(-1), None, expr.log(expr.Fun('abs', x))),
            ((1 + (x ^ Const(2))) ^ Const(-1), None, expr.arctan(x)),
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


class CommonDeriv(Rule):
    """Common rules for evaluating a derivative."""

    def eval(self, e):
        if isinstance(e, str):
            e = parser.parse_expr(e)

        if e.ty == expr.DERIV:
            return expr.deriv(e.var, e.body)
        else:
            return e

class OnSubterm(Rule):
    """Apply given rule on subterms."""
    def __init__(self, rule):
        assert isinstance(rule, Rule)
        self.rule = rule

    def eval(self, e):
        rule = self.rule
        if e.ty in (expr.VAR, expr.CONST):
            return rule.eval(e)
        elif e.ty == expr.OP:
            args = [self.eval(arg) for arg in e.args]
            return rule.eval(expr.Op(e.op, *args))
        elif e.ty == expr.FUN:
            args = [self.eval(arg) for arg in e.args]
            return rule.eval(expr.Fun(e.func_name, *args))
        elif e.ty == expr.DERIV:
            return rule.eval(expr.Deriv(e.var, self.eval(e.body)))
        elif e.ty == expr.INTEGRAL:
            return rule.eval(expr.Integral(e.var, self.eval(e.lower), self.eval(e.upper), self.eval(e.body)))
        elif e.ty == expr.EVAL_AT:
            return rule.eval(expr.EvalAt(e.var, self.eval(e.lower), self.eval(e.upper), self.eval(e.body)))
        elif e.ty == expr.LIMIT:
            return rule.eval(expr.Limit(e.var, self.eval(e.lim), self.eval(e.body)))
        else:
            raise NotImplementedError

class OnLocation(Rule):
    """Apply given rule on subterm specified by given location."""
    def __init__(self, rule, loc):
        assert isinstance(rule, Rule)
        self.rule = rule
        self.loc = expr.Location(loc)

    def eval(self, e):
        def rec(cur_e, loc):
            if loc.is_empty():
                return self.rule.eval(cur_e)
            elif cur_e.ty == VAR or cur_e.ty == CONST:
                raise AssertionError("OnLocation: invalid location")
            elif cur_e.ty == OP:
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
            elif cur_e.ty == FUN:
                assert loc.head < len(cur_e.args), "OnLocation: invalid location"
                return Fun(cur_e.func_name, rec(cur_e.args[0], loc.rest))
            elif cur_e.ty == INTEGRAL:
                if loc.head == 0:
                    return Integral(cur_e.var, cur_e.lower, cur_e.upper, rec(cur_e.body, loc.rest))
                elif loc.head == 1:
                    return Integral(cur_e.var, rec(cur_e.lower, loc.rest), cur_e.upper, cur_e.body)
                elif loc.head == 2:
                    return Integral(cur_e.var, cur_e.lower, rec(cur_e.upper, loc.rest), cur_e.body)
                else:
                    raise AssertionError("OnLocation: invalid location")
            elif cur_e.ty == EVAL_AT:
                if loc.head == 0:
                    return EvalAt(cur_e.var, cur_e.lower, cur_e.upper, rec(cur_e.body, loc.rest))
                elif loc.head == 1:
                    return EvalAt(cur_e.var, rec(cur_e.lower, loc.rest), cur_e.upper, cur_e.body)
                elif loc.head == 2:
                    return EvalAt(cur_e.var, cur_e.lower, rec(cur_e.upper, loc.rest), cur_e.body)
                else:
                    raise AssertionError("OnLocation: invalid location")
            elif cur_e.ty == DERIV:
                assert loc.head == 0, "OnLocation: invalid location"
                return Deriv(cur_e.var, rec(cur_e.body, loc.rest))
            else:
                raise NotImplementedError

        return rec(e, self.loc)
            

class FullSimplify(Rule):
    """Perform full simplification using CommonIntegral, Linearity, and Simplify."""
    def __init__(self):
        self.name = "FullSimplify"

    def eval(self, e):
        if isinstance(e, str):
            e = parser.parse_expr(e)

        counter = 0
        current = e
        while True:
            s1 = OnSubterm(Linearity()).eval(current)
            s2 = OnSubterm(CommonIntegral()).eval(s1)
            s3 = Simplify().eval(s2)
            if s3 == current:
                break
            current = s3
            counter += 1
            if counter > 5:
                raise AssertionError("Loop in FullSimplify")
        return current

class Substitution1(Rule):
    """Apply substitution u = g(x) x = y(u)  f(x) = x+5  u=>x+1   (x+1)+4 """
    """INT x:[a, b]. f(g(x))*g(x)' = INT u:[g(a), g(b)].f(u)"""
    def __init__(self, var_name, var_subst):
        """
        var_name: string, name of the new variable.
        var_subst: Expr, expression in the original integral to be substituted.
    
        """
        self.name = "Substitution"
        self.var_name = var_name
        self.var_subst = var_subst
        self.f = None  # After application, record f here

    def eval(self, e):
        """
        Parameters:
        e: Expr, the integral on which to perform substitution.

        Returns:
        The new integral e', and stores in self.f the parameter used to
        specify the substitution.

        """
        if isinstance(e, str):
            e = parser.parse_expr(e)


        var_name = parser.parse_expr(self.var_name)
        var_subst = self.var_subst
        dfx = expr.deriv(e.var, var_subst)
        body = holpy_style(sympy_style(e.body/dfx))
        body_subst = body.replace_trig(var_subst, var_name)
        if body_subst == body:
            body_subst = body.replace_trig(var_subst, var_name)
        lower = var_subst.subst(e.var, e.lower).normalize()
        upper = var_subst.subst(e.var, e.upper).normalize()
        if parser.parse_expr(e.var) not in body_subst.findVar():
            # Substitution is able to clear all x in original integrand
            print('Substitution: case 1')
            self.f = body_subst
            if sympy_style(lower) <= sympy_style(upper):
                return Integral(self.var_name, lower, upper, body_subst).normalize()
            else:
                return Integral(self.var_name, upper, lower, Op("-", body_subst)).normalize()
        else:
            # Substitution is unable to clear x, need to solve for x
            print('Substitution: case 2')
            gu = solvers.solve(expr.sympy_style(var_subst - var_name), expr.sympy_style(e.var))
            if gu == []:  # sympy can't solve the equation
                return e
            gu = gu[-1] if isinstance(gu, list) else gu
            gu = expr.holpy_style(gu)
            c = e.body.replace_trig(parser.parse_expr(e.var), gu)
            new_problem_body = (e.body.replace_trig(parser.parse_expr(e.var), gu)*expr.deriv(str(var_name), gu))
            lower = holpy_style(sympy_style(var_subst).subs(sympy_style(e.var), sympy_style(e.lower)))
            upper = holpy_style(sympy_style(var_subst).subs(sympy_style(e.var), sympy_style(e.upper)))
            self.f = new_problem_body
            if sympy_style(lower) < sympy_style(upper):
                return Integral(self.var_name, lower, upper, new_problem_body).normalize()
            else:
                return Integral(self.var_name, upper, lower, Op("-", new_problem_body)).normalize()

class Substitution2(Rule):
    """Apply substitution x = f(u)"""
    def __init__(self, var_name, var_subst):
        #such as var_name: "u" var_subst: "sin(u)"
        self.var_name = var_name
        self.var_subst = var_subst
        self.name = "Substitution inverse"

    def eval(self, e):
        if isinstance(e, str):
            e = parser.parse_expr(e)

        subst_deriv = expr.deriv(self.var_name, self.var_subst) #dx = d(x(u)) = x'(u) *du
        new_e_body = e.body.replace_trig(expr.holpy_style(str(e.var)), self.var_subst) #replace all x with x(u)
        new_e_body = expr.Op("*", new_e_body, subst_deriv) # g(x) = g(x(u)) * x'(u)
        lower = solvers.solve(expr.sympy_style(self.var_subst - e.lower))[0]
        upper = solvers.solve(expr.sympy_style(self.var_subst - e.upper))[0]
        return expr.Integral(self.var_name, expr.holpy_style(lower), expr.holpy_style(upper), new_e_body)
        

class UnfoldPower(Rule):
    """Unfold power"""
    def __init__(self):
        self.name = "Unfold power"

    def eval(self, e):
        if isinstance(e, str):
            e = parser.parse_expr(e)

        if e.ty == expr.INTEGRAL:
            return Integral(e.var, e.lower, e.upper, e.body.expand())
        else:
            return e.expand()


class Equation(Rule):
    """Apply substitution for equal expressions"""
    def __init__(self, new_expr, denom=None):
        assert isinstance(new_expr, Expr)
        self.new_expr = new_expr
        self.name = "Equation"
        self.denom = denom
    
    def eval(self, e):
        if isinstance(e, str):
            e = parser.parse_expr(e)

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
    """Apply integration by parts."""
    def __init__(self, u, v):
        assert isinstance(u, expr.Expr) and isinstance(v, expr.Expr)
        self.u = u
        self.v = v
        self.name = "Integrate by parts"

    def eval(self, e):
        if isinstance(e, str):
            e = parser.parse_expr(e)

        if e.ty != expr.INTEGRAL:
            return e
        e.body = e.body.normalize()
        du = expr.deriv(e.var, self.u)
        dv = expr.deriv(e.var, self.v)
        udv = (self.u * dv).normalize()
        if udv == e.body:
            return expr.EvalAt(e.var, e.lower, e.upper, (self.u * self.v).normalize()) - \
                   expr.Integral(e.var, e.lower, e.upper, (self.v * du).normalize())
        else:
            print("%s != %s" % (str(udv), str(e.body)))
            raise NotImplementedError("%s != %s" % (str(udv), str(e.body)))

class PolynomialDivision(Rule):
    """Simplify the representation of polynomial divided by polynomial.
    """
    def __init__(self):
        self.name = "Fraction Division"

    def eval(self, e):
        if isinstance(e, str):
            e = parser.parse_expr(e)


        if e.ty == OP and e.op != "/" and not (e.ty == OP and e.op == "*" and e.args[1].ty == OP and e.args[1].op == "^"\
            and (e.args[1].args[1].ty == OP and len(e.args[1].args[1]) == 1 or e.args[1].args[1].ty == CONST and e.args[1].args[1].val < 0)):
            return e
            
        result = apart(expr.sympy_style(e))
        return parser.parse_expr(str(result).replace("**","^"))

class RewriteTrigonometric(Rule):
    """Rewrite using one of Fu's rules."""
    def __init__(self, rule_name):
        self.name = "Rewrite trigonometric"
        self.rule_name = rule_name

    def eval(self, e):
        if isinstance(e, str):
            e = parser.parse_expr(e)

        rule_fun, _ = expr.trigFun[self.rule_name]
        sympy_result = rule_fun(expr.sympy_style(e))
        result = expr.holpy_style(sympy_result)
        return result

class ElimAbs(Rule):
    """Eliminate abstract value."""
    def __init__(self):
        self.name = "Eliminate abs"

    def check_zero_point(self, e):
        integrals = e.separate_integral()
        if not integrals:
            return False
        abs_info = []
        for i, j in integrals:
            abs_expr = i.getAbs()
            abs_info += [(a, i) for a in abs_expr]
        zero_point = []
        for a, i in abs_info:
            arg = a.args[0]
            zeros = solveset(expr.sympy_style(arg), expr.sympy_style(i.var), Interval(sympy_style(i.lower), sympy_style(i.upper), left_open = True, right_open = True))
            zero_point += zeros
        return len(zero_point) > 0

    def get_zero_point(self, e):
        abs_expr = e.body.getAbs()
        zero_point = []
        for a in abs_expr:
            arg = a.args[0]
            zeros = solveset(expr.sympy_style(arg), expr.sympy_style(e.var), Interval(sympy_style(e.lower), sympy_style(e.upper), left_open = True, right_open = True))
            zero_point += zeros
        return holpy_style(zero_point[0])

    def eval(self, e):
        if isinstance(e, str):
            e = parser.parse_expr(e)

        if e.ty != expr.INTEGRAL:
            return e

        abs_expr = e.body.getAbs()
        if len(abs_expr) == 0:
            return e
        abs_expr = abs_expr[0]  # only consider the first absolute value

        g, s = abs_expr.args[0].ranges(e.var, e.lower, e.upper) # g: value in abs > 0, s: value in abs < 0
        new_integral = []
        for l, h in g:
            new_integral.append(expr.Integral(e.var, l, h, e.body.replace_trig(abs_expr, abs_expr.args[0])))
        for l, h in s:
            new_integral.append(expr.Integral(e.var, l, h, e.body.replace_trig(abs_expr, Op("-", abs_expr.args[0]))))
        return sum(new_integral[1:], new_integral[0])

class SplitRegion(Rule):
    """Split integral into two parts at a point."""
    def __init__(self, c):
        self.name = "Split region"
        self.c = c

    def eval(self, e):
        if isinstance(e, str):
            e = parser.parse_expr(e)

        
        if e.ty != expr.INTEGRAL:
            return e

        if expr.sympy_style(e.upper) <= expr.sympy_style(self.c) or \
        expr.sympy_style(e.lower) >= expr.sympy_style(self.c):
            raise AssertionError("Split region")

        return expr.Integral(e.var, e.lower, self.c, e.body) + expr.Integral(e.var, self.c, e.upper, e.body)


class IntegrateByEquation(Rule):
    """When the initial integral occurs in the steps."""
    def __init__(self, lhs):
        assert isinstance(lhs, Integral)
        self.lhs = lhs.normalize()
        self.coeff = None
    
    def validate(self, e):
        """Determine whether the lhs exists in e."""
        integrals = e.separate_integral()
        if not integrals:
            return False
        for i, j in integrals:
            if i.normalize() == self.lhs:
                return True
        return False

    def eval(self, e):
        """Eliminate the lhs's integral in rhs by solving equation."""
        if isinstance(e, str):
            e = parser.parse_expr(e)

        rhs_var = None
        def get_coeff(t):
            nonlocal rhs_var
            if t.ty == INTEGRAL:
                if t == self.lhs:
                    rhs_var = t.var
                    return 1
                else:
                    return 0
            elif t.is_plus():
                return get_coeff(t.args[0]) + get_coeff(t.args[1])
            elif t.is_minus():
                return get_coeff(t.args[0]) - get_coeff(t.args[1])
            elif t.is_uminus():
                return -get_coeff(t.args[0])
            elif t.is_times() and t.args[0].ty == CONST:
                return t.args[0].val * get_coeff(t.args[1])
            else:
                return 0

        coeff = get_coeff(e)
        if coeff == 0:
            return e
        new_rhs = (e + (Const(-coeff)*self.lhs.alpha_convert(rhs_var))).normalize()
        self.coeff = (-Const(coeff)).normalize()
        return (new_rhs/(Const(1-coeff))).normalize()

class ElimInfInterval(Rule):
    """Convert improper integral of TYPE 1 (infinite intervals) 
    to a limit expression."""
    def __init__(self):
        self.name = "Improper integral of Type 1"

    def eval(self, e, a=Const(0)):
        if isinstance(e, str):
            e = parser.parse_expr(e)

        def gen_lim_expr(var, lim, lower, upper):
            return expr.Limit(new_var, lim, expr.Integral(e.var, lower, upper, e.body))
        
        if e.ty != expr.INTEGRAL:
            return e
        upper, lower = e.upper, e.lower
        if upper != expr.inf and lower != expr.neg_inf:
            return e
        
        new_var = "s" if e.var == "t" else "t"
        if upper == expr.inf and lower != expr.neg_inf:
            return gen_lim_expr(new_var, expr.inf, lower, Var(new_var))
        elif upper != expr.inf and lower == expr.neg_inf:
            return gen_lim_expr(new_var, expr.neg_inf, Var(new_var), upper)
        elif upper == expr.inf and lower == expr.neg_inf:
            assert a is not None, "No split point provided"
            return gen_lim_expr(new_var, expr.neg_inf, Var(new_var), a) + \
                gen_lim_expr(new_var, expr.inf, a, Var(new_var))
        else:
            raise NotImplementedError

def check_item(item, target=None, *, debug=False):
    """Check application of rules in the item."""
    problem = parser.parse_expr(item['problem'])
    
    if debug:
        print("\n%s: %s" % (item['name'], problem))

    current = problem
    prev_steps = []

    for step in item['calc']:
        reason = step['reason']
        expected = parser.parse_expr(step['text'])

        if reason == 'Initial':
            result = current
        
        elif reason == 'Simplification':
            if "location" in step:
                result = OnLocation(FullSimplify(), step["location"]).eval(current)
            else:
                result = FullSimplify().eval(current)

        elif reason == 'Substitution':
            var_name = step['params']['var_name']
            f = parser.parse_expr(step['params']['f'])
            g = parser.parse_expr(step['params']['g'])
            rule = Substitution1(var_name, g)
            if 'location' in step:
                result = OnLocation(rule, step['location']).eval(current)
            else:
                result = rule.eval(current)
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
                result = OnLocation(rule, step['location']).eval(current)
            else:
                result = rule.eval(current)

        elif reason == 'Rewrite fraction':
            rule = PolynomialDivision()
            if 'location' in step:
                result = OnLocation(rule, step['location']).eval(current)
            else:
                result = rule.eval(current)

        elif reason == 'Rewrite':
            rhs = parser.parse_expr(step['params']['rhs'])
            if 'denom' in step['params']:
                rule = Equation(rhs, parser.parse_expr(step['params']['denom']))
            else:
                rule = Equation(rhs)
            if 'location' in step:
                result = OnLocation(rule, step['location']).eval(current)
            else:
                result = rule.eval(current)

        elif reason == 'Rewrite trigonometric':
            rule = RewriteTrigonometric(step['params']['rule'])
            if 'location' in step:
                result = OnLocation(rule, step['location']).eval(current)
            else:
                result = rule.eval(current)

        elif reason == 'Substitution inverse':
            var_name = step['params']['var_name']
            g = parser.parse_expr(step['params']['g'])
            rule = Substitution2(var_name, g)
            if 'location' in step:
                result = OnLocation(rule, step['location']).eval(current)
            else:
                result = rule.eval(current)

        elif reason == 'Elim abs':
            rule = ElimAbs()
            if 'location' in step:
                result = OnLocation(rule, step['location']).eval(current)
            else:
                result = rule.eval(current)

        elif reason == 'Split region':
            c = parser.parse_expr(step['params']['c'])
            rule = SplitRegion(c)
            if 'location' in step:
                result = OnLocation(rule, step['location']).eval(current)
            else:
                result = rule.eval(current)

        elif reason == 'Unfold power':
            rule = UnfoldPower()
            if 'location' in step:
                result = OnLocation(rule, step['location']).eval(current)
            else:
                result = rule.eval(current)

        elif reason == 'Solve equation':
            prev_id = int(step['params']['prev_id'])
            rule = IntegrateByEquation(prev_steps[prev_id])
            result = rule.eval(current)

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
