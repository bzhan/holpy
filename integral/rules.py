"""Rules for integration."""
import math
from decimal import Decimal

import sympy
import sympy.series.limits
from sympy.integrals import integrals
from integral import poly, expr
from integral.expr import Var, Const, Fun, EvalAt, Op, Integral, Symbol, Expr, trig_identity, \
    sympy_style, holpy_style, OP, CONST, INTEGRAL, VAR, LIMIT, sin, cos, FUN, EVAL_AT, \
    DERIV, decompose_expr_factor, Deriv, Inf, INF, Limit, NEG_INF, POS_INF
import functools, operator
from integral import parser
from sympy import Interval, expand_multinomial, apart
from sympy.solvers import solvers, solveset
from integral import parser
from fractions import Fraction

class Rule:
    """
    表示积分规则，输入一个积分，然后出来一个与之相等的表达式
    Represents a rule for integration. It takes an integral
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
        return res

class Linearity(Rule):
    """Applies linearity rules:
    这里INT表示积分
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
            return rule.eval(expr.Limit(e.var, e.lim, self.eval(e.body)))
        else:
            raise NotImplementedError

class OnLocation(Rule):
    """Apply given rule on subterm specified by given location."""
    def __init__(self, rule: Rule, loc):
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

        #积分中被替换的变量
        var_name = parser.parse_expr(self.var_name)
        #用来替换的式子
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
            # print('Substitution: case 1')
            self.f = body_subst
            if sympy_style(lower) <= sympy_style(upper):
                return Integral(self.var_name, lower, upper, body_subst).normalize()
            else:
                return Integral(self.var_name, upper, lower, Op("-", body_subst)).normalize()
        else:
            # Substitution is unable to clear x, need to solve for x
            # print('Substitution: case 2')
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
        if e.ty == INTEGRAL:
            raise NotImplementedError
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
# 分部积分
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

#对有理分式进行化简
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
        # 选择一条Fu-like rule然后对表示e进行重写
        rule_fun, _ = expr.trigFun[self.rule_name]
        sympy_result = rule_fun(expr.sympy_style(e))
        result = expr.holpy_style(sympy_result)
        return result



class ElimAbs(Rule):
    """Eliminate abstract value."""
    def __init__(self):
        self.name = "Eliminate abs"
    
    # 
    def check_zero_point(self, e):
        integrals = e.separate_integral()
        #print("e.sep:",integrals)
        if not integrals:
            return False
        abs_info = []
        for i, j in integrals:
            abs_expr = i.get_abs()
            abs_info += [(a, i) for a in abs_expr]
        zero_point = []
        for a, i in abs_info:
            arg = a.args[0]
            zeros = solveset(expr.sympy_style(arg), expr.sympy_style(i.var), Interval(sympy_style(i.lower), sympy_style(i.upper), left_open = True, right_open = True))
            zero_point += zeros
        return len(zero_point) > 0

    '''
    比如INT x:[-2,3]. |x-2| 故get_zero_point = 2
    '''
    def get_zero_point(self, e):
        # 收集积分中被积表达式中的所有abs表达式
        abs_expr = e.body.get_abs()
        zero_point = []
        
        for a in abs_expr:
            '''
               例如 a = |x+2| = abs(x+2)
               所以 args[0] = x+2 #即表达式
            '''
            arg = a.args[0]
            # 调用sympy
            zeros = solveset(expr.sympy_style(arg), expr.sympy_style(e.var), Interval(sympy_style(e.lower), sympy_style(e.upper), left_open = True, right_open = True))
            # [] += []
            zero_point += zeros
        return holpy_style(zero_point[0])

    def eval(self, e):
        if isinstance(e, str):
            e = parser.parse_expr(e)

        if e.ty != expr.INTEGRAL:
            return e

        abs_expr = e.body.get_abs()
        if len(abs_expr) == 0:
            return e
        # 选择一个 abs 表达式
        abs_expr = abs_expr[0]  # only consider the first absolute value
        # 表达式的上下界
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
        norm_e = e.normalize()
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

        coeff = get_coeff(norm_e)
        if coeff == 0:
            return e
        new_rhs = (norm_e + (Const(-coeff)*self.lhs.alpha_convert(rhs_var))).normalize()
        self.coeff = (-Const(coeff)).normalize()
        return (new_rhs/(Const(1-coeff))).normalize()


class ElimInfInterval(Rule):
    """Convert improper integral with infinite upper or lower limits to
    a limit expression.

    If both upper and lower limits are infinity, a split point need to be
    provided.

    """
    def __init__(self):
        self.name = "Improper integral of Type 1"

    def eval(self, e, a=Const(0)):
        if isinstance(e, str):
            e = parser.parse_expr(e)

        def gen_lim_expr(new_var, lim, lower, upper, drt = None):
            return expr.Limit(new_var, lim, expr.Integral(e.var, lower, upper, e.body),drt)

        if e.ty != expr.INTEGRAL:
            return e

        inf = Inf(Decimal('inf'))
        neg_inf = Inf(Decimal('-inf'))
        upper, lower = e.upper, e.lower
        new_var = "s" if e.var == "t" else "t"

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
            assert a is not None, "No split point provided"
            lim1 = gen_lim_expr(new_var, neg_inf, Var(new_var), a)
            lim2 = gen_lim_expr(new_var, inf, a, Var(new_var))
            return Op('+', lim1, lim2)
        elif upper == neg_inf and lower == inf:
            assert a is not None, "No split point provided"
            lim1 = gen_lim_expr(new_var, inf, Var(new_var), a)
            lim2 = gen_lim_expr(new_var, neg_inf, a, Var(new_var))
            return Op('+',lim1,lim2)
        else:
            raise NotImplementedError


class LHopital(Rule):
    """Apply L'Hoptial rule."""
    def __init__(self):
        self.name = "L'Hopital"

    def eval(self, e):
        if isinstance(e, str):
            e = parser.parse_expr(e)

        if not isinstance(e, expr.Limit):
            return e

        if e.body.op == '-' and len(e.body.args) == 1:
            e1 = e.body.args[0]
            if e1.op == '*' and len(e1.args) == 2:
                # Special case: x * exp(-x) -> x / exp(x)
                a, b = e1.args
                var, lim = e.var, e.lim
                res1 = compute_limit(a.replace_trig(Var(var), lim))
                res2 = compute_limit(b.replace_trig(Var(var), lim))
                if res1[0] in (NEG_INF, POS_INF) and res2[0] == expr.ZERO:
                    if b.ty == expr.FUN and b.func_name == 'exp':
                        e = Limit(var, lim, -a / Fun('exp', -b.args[0]))
                    else:
                        return e
                elif res2[0] in (NEG_INF, POS_INF) and res1[0] == expr.ZERO:
                    if a.ty == expr.FUN and a.func_name == 'exp':
                        e = Limit(var, lim, -b / Fun('exp', -a.args[0]))
                    else:
                        return e
                else:
                    return e

        if not (isinstance(e.body, expr.Op) and e.body.op == '/'):
            return e

        numerator, denominator = e.body.args
        rule = DerivativeSimplify()
        return expr.Limit(e.var ,e.lim, Op('/', rule.eval(Deriv(e.var,numerator)),
                                                rule.eval(Deriv(e.var,denominator))), e.drt)
        # if e.ty != LIMIT:
        #     return e
        # bd = e.body
        #
        # subst_poly = bd.replace_trig(Var(e.var), e.lim).to_poly()
        # if subst_poly.T != poly.UNKNOWN:
        #     return e
        # inf_part, zero_part, const_part = [], [], []
        #
        # bd_poly = bd.to_poly()
        # if len(bd_poly) != 1:
        #     raise NotImplementedError
        # m = bd_poly[0]
        # factors = m.factors
        # for i, j in factors:
        #     mono = poly.Polynomial([poly.Monomial(1, ((i, j),))])
        #     norm_m = expr.from_poly(mono)
        #     subst_m = norm_m.replace_trig(Var(e.var), e.lim).to_poly()
        #     if subst_m.T == poly.ZERO:
        #         zero_part.append((Const(1) / norm_m).normalize())
        #     elif subst_m.T in (poly.POS_INF, poly.NEG_INF):
        #         inf_part.append(norm_m)
        #     elif subst_m.T == poly.NON_ZERO:
        #         const_part.append(norm_m)
        #     else:
        #         raise NotImplementedError(str(mono))
        #
        # assert inf_part and zero_part
        # inf_expr = functools.reduce(operator.mul, inf_part[1:], inf_part[0])
        # zero_expr = functools.reduce(operator.mul, zero_part[1:], zero_part[0])
        #
        # nm_trace = [inf_expr]
        # denom_trace = [zero_expr]
        # while True:
        #     nm, denom = nm_trace[-1], denom_trace[-1]
        #     nm_deriv, denom_deriv = expr.deriv(e.var, nm), expr.deriv(e.var, denom)
        #     nm_subst, denom_subst = nm_deriv.replace_trig(Var(e.var), e.lim), denom_deriv.replace_trig(Var(e.var), e.lim)
        #     nm_poly, denom_poly = nm_subst.to_poly(), denom_subst.to_poly()
        #     if nm_poly.T in (poly.POS_INF, poly.NEG_INF) and denom_poly.T in (poly.POS_INF, poly.NEG_INF):
        #         continue
        #     elif nm_poly.T in (poly.ZERO, poly.NON_ZERO) and denom_poly.T in (poly.POS_INF, poly.NEG_INF):
        #         return Const(0)
        #     elif nm_poly.T in (poly.POS_INF, poly.NEG_INF) and denom_poly.T in (poly.ZERO, poly.NON_ZERO):
        #         return expr.from_poly(nm_poly)
        #     elif nm_poly.T == poly.NON_ZERO and denom_poly.T == poly.NON_ZERO:
        #         return (nm_subst / denom_subst).normalize()
        #     else:
        #         raise NotImplementedError


class LimSep(Rule):
    """Perform the following rewrites:

        Lim (exp1 + exp2) -> (Lim exp1) + (Lim exp2)
        Lim (exp1 - exp2) -> (Lim exp1) - (Lim exp2)
        Lim (exp1 * exp2) -> (Lim exp1) * (Lim exp2)
        Lim (exp1 / exp2) -> (Lim exp1) / (Lim exp2)

    """
    def __init__(self):
        self.name = "LimSep"

    def eval(self, e):
        if isinstance(e, str):
            e = parser.parse_expr(e)
        if not (isinstance(e, expr.Limit) and isinstance(e.body, expr.Op) and \
                e.body.op in ('+', '-' ,'*', '/') and len(e.body.args) == 2):
            return e
        return expr.Op(e.body.op, expr.Limit(e.var, e.lim, e.body.args[0], e.drt),
                                  expr.Limit(e.var, e.lim, e.body.args[1], e.drt))


class DerivativeSimplify(Rule):
    """Simplify the derivative of an expression"""
    def __init__(self):
        self.name = "Simplify derivative"

    def eval(self, e):
        if isinstance(e, str):
            e = parser.parse_expr(e)

        if not isinstance(e, Deriv):
            return e
        
        return expr.deriv(e.var, e.body)

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


def compute_limit(e: Expr):
    """Compute the limit of the expression.
    
    The returned value is of the form (e, type, order of infinity, type of infinity),
    where type is one of
    - "const": limit is a finite value
    - "pos_inf": limit is positive infinity
    - "neg_inf": limit is negative infinity
    - "indefinite_bounded": limit is unknown finite value
    - "indefinite_unbounded": "limit is unknown unbounded value
    - "unknown": limit is unknown

    Type of infinity is one of
    - "poly": polynomial growth
    - "log": logarithmic growth
    - "?": other kind of growth

    If type of infinity is "poly", order of infinity gives order of polynomial
    growth. Otherwise order of infinity is -1.

    """
    if e.ty == CONST or e.ty == FUN and len(e.args) == 0:
        # Constants
        return (e, 'const', 0, "?")
    elif e.ty == VAR:
        # Variable
        return (e, 'const', 0, '?')
    elif e.ty == OP and e.op == '-' and len(e.args) == 1:
        # Unary minus
        a, b, c, d = compute_limit(e.args[0])
        if b == 'pos_inf':
            return (-a, 'neg_inf', c, d)
        elif b == 'neg_inf':
            return (-a, 'pos_inf', c, d)
        return (-a, b, c, d)
    elif e.ty == OP and e.op == '-' and len(e.args) == 2:
        # Binary minus
        a1, b1, c1, d1 = compute_limit(e.args[0])
        a2, b2, c2, d2 = compute_limit(e.args[1])
        if b1 == 'const' and b2 == 'const':
            # Both sides have finite limits
            return (a1 - a2, 'const', 0, "?")
        elif b1 == 'pos_inf' and b2 == 'pos_inf':
            # Both sides to infinity: compare order of infinity
            if d1 == 'poly' and d2 == 'poly':
                if c1 == c2:
                    return (a1 - a2, 'unknown', -1, "?")
                elif c1 > c2:
                    return (Inf(Decimal('inf')), 'pos_inf', c1, d1)
                else:
                    return (Inf(Decimal('-inf')), 'neg_inf', c2, d2)
            else:
                return (a1 - a2, 'unknown', -1, "?")
        elif b1 == 'const' and b2 == 'pos_inf':
            # a - oo = -oo
            return (Inf(Decimal('-inf')), 'neg_inf', c2, d2)
        elif b1 == 'const' and b2 == 'neg_inf':
            # a - (-oo) = oo
            return (Inf(Decimal('inf')), 'pos_inf', c2, d2)
        elif b1 == 'const' and b2 == 'indefinite_bounded':
            # a - bounded = bounded
            return (a1 - a2, 'indefinite_bounded', -1, "?")
        elif b1 == 'const' and b2 == 'indefinite_unbounded':
            # a - unbounded = unbounded
            return (a1 - a2, "indefinite_unbounded", -1, "?")
        elif b1 == 'pos_inf' and b2 in ('indefinite_bounded', 'const'):
            # oo - bounded = oo
            return (Inf(Decimal('inf')), 'pos_inf', c1, d1)
        elif b1 == 'pos_inf' and b2 == 'neg_inf':
            # oo - (-oo) = oo, compute order of infinity
            if d1 == 'poly' and d2 == 'poly':
                return (Inf(Decimal('inf')), 'pos_inf', max(c1,c2), d2)
            else:
                return (Inf(Decimal('inf')), 'pos_inf', -1, "?")
        elif b1 == 'neg_inf' and b2 in ('const', 'indefinite_bounded'):
            # -oo - bounded = -oo
            return (Inf(Decimal('-inf')), 'neg_inf',c1,d1)
        elif b1 == 'neg_inf' and b2 == 'pos_inf':
            # (-oo) - oo = -oo, compute order of infinity
            if d1 == 'poly' and d2 == 'poly':
                return (Inf(Decimal('-inf')), 'neg_inf', max(c1,c2), d1)
            else:
                return (Inf(Decimal('-inf')), 'neg_inf', -1, "?")
        elif b1 == 'indefinite_bounded' and b2 == 'const':
            # bounded - const = bounded
            return (a1 - a2, "indefinite_bounded", -1, "?")
        elif b1 in ('indefinite_unbounded') and b2 == 'const':
            # unbounded - const = unbounded
            return (a1 - a2, "indefinite_unbounded", -1, "?")
        else:
            # Otherwise, return unknown
            return (a1 - a2, "unknown", -1, "?")
    elif e.ty == OP and e.op == '+' and len(e.args) == 2:
        # Binary plus
        a1, b1, c1, d1 = compute_limit(e.args[0])
        a2, b2, c2, d2 = compute_limit(e.args[1])
        if b1 == 'const' and b2 == 'const': 
            # Both sides have finite limits
            if a1.is_const() and a2.is_const():
                return (Const(a1.val + a2.val), "const", 0, "?")
            else:
                return (a1 + a2, 'const', 0, "?")
        elif b1 == 'const' and b2 == 'pos_inf':
            # a + oo = oo
            return (Inf(Decimal('inf')), 'pos_inf', c2, d2)
        elif b1 == 'const' and b2 == 'neg_inf':
            # a + (-oo) = -oo
            return (Inf(Decimal('-inf')), 'neg_inf', c2, d2)
        elif b2 == 'indefinite_bounded' and b1 == 'const':
            # bounded + const = bounded
            return (a1 + a2, "indefinite_bounded", -1, "?")
        elif b2 in ('indefinite_unbounded') and b1 == 'const':
            # unbounded + const = unbounded
            return (a1 + a2, "indefinite_unbounded", -1, "?")
        elif b1 == 'pos_inf' and b2 == 'pos_inf':
            # oo + oo = oo, compute order of infinity
            if d1 == 'poly' and d2 == 'poly':
                return (Inf(Decimal('inf')), 'pos_inf', max(c1,c2), d2)
            else:
                return (Inf(Decimal('inf')), 'pos_inf', -1, d2)
        elif b1 == 'pos_inf' and b2 in ('indefinite_bounded', 'const'):
            # oo + bounded = oo
            return (Inf(Decimal('inf')), 'pos_inf', c1, d1)
        elif b1 == 'neg_inf' and b2 == 'neg_inf':
            # -oo + -oo = -oo, compute order of infinity
            if d1 == 'poly' and d2 == 'poly':
                return (Inf(Decimal('-inf')), 'neg_inf', max(c2, c1), d2)
            else:
                return (Inf(Decimal('-inf')), 'neg_inf', -1, "?")
        elif b1 == 'neg_inf' and b2 in ('const', 'indefinite_bounded'):
            # -oo + bounded = -oo
            return (Inf(Decimal('-inf')), 'neg_inf', c1, d1)
        elif b1 == 'indefinite_bounded' and b2 == 'const':
            # bounded + const = bounded
            return (a1 + a2, "indefinite_bounded", -1, "?")
        elif b1 == 'indefinite_unbounded' and b2 == 'const':
            # unbounded + const = unbounded
            return (a1 + a2, "indefinite_unbounded", -1, "?")
        else:
            # Otherwise, return unknown
            return (a1 + a2, 'unknown', -1, "?")
    elif e.ty == OP and e.op == '*' and len(e.args) == 2:
        # Multiplication
        a1, b1, c1, d1 = compute_limit(e.args[0])
        a2, b2, c2, d2 = compute_limit(e.args[1])
        if b1 == 'const' and b2 == 'const':
            # Both sides have finite limits
            return (a1 * a2, 'const', 0, "?")
        elif b1 == 'const' and b2 in ('pos_inf', 'neg_inf'):
            # Cases when the left side is constant, and right side is infinity
            if a1.ty == CONST and a1.val > 0 and b2 == 'pos_inf':
                # pos * oo = oo
                return (Inf(Decimal('inf')) , 'pos_inf', c2, d2)
            elif a1.ty == CONST and a1.val > 0 and b2 == 'neg_inf':
                # pos * -oo = -oo
                return (Inf(Decimal('-inf')) , 'neg_inf', c2, d2)
            elif a1.ty == CONST and a1.val < 0 and b2 == 'pos_inf':
                # neg * oo = -oo
                return (Inf(Decimal('-inf')) , 'neg_inf', c2, d2)
            elif a1.ty == CONST and a1.val < 0 and b2 == 'neg_inf':
                # neg * -oo = oo
                return (Inf(Decimal('inf')) , 'pos_inf', c2, d2)
            elif a1.ty == FUN and a1.func_name in ('log') and a1.args[0].ty == CONST \
                    and a1.args[0].val > 1 and b2 == 'pos_inf':
                # log(a) * oo = oo, where a > 1
                return (Inf(Decimal('inf')), 'pos_inf', -1, '?')
            else:
                # Otherwise, return unknown
                return (a1*a2, 'unknown', -1, "?")
        elif b2 == 'const' and b1 in ('pos_inf', 'neg_inf'):
            # Cases when the right side is constant, and left side is infinity
            if a2.ty == CONST and a2.val > 0 and b1 == 'pos_inf':
                # oo * pos = oo
                return (Inf(Decimal('inf')), 'pos_inf', c1, d1)
            elif a2.ty == CONST and a2.val > 0 and b1 == 'neg_inf':
                # -oo * pos = -oo
                return (Inf(Decimal('-inf')), 'neg_inf', c1, d1)
            elif a2.ty == CONST and a2.val < 0 and b1 == 'pos_inf':
                # oo * neg = -oo
                return (Inf(Decimal('-inf')), 'neg_inf', c1, d1)
            elif a2.ty == CONST and a2.val < 0 and b1 == 'neg_inf':
                # -oo * neg = oo
                return (Inf(Decimal('inf')), 'pos_inf', c1, d1)
            else:
                # Otherwise, return unknown
                return (a1 * a2, 'unknown', -1, "?")
        elif b1 == 'pos_inf' and b2 == 'pos_inf':
            # oo * oo = oo, compute order of infinity
            if d1 == 'poly' and d2 == 'poly':
                return (Inf(Decimal('inf')), 'pos_inf', c1 + c2, 'poly')
            else:
                return (Inf(Decimal('inf')), 'pos_inf', -1, '?')
        elif b1 == 'pos_inf' and b2 == 'neg_inf':
            # oo * -oo = -oo, compute order of infinity
            if d1 == 'poly' and d2 == 'poly':
                return (Inf(Decimal('-inf')), 'neg_inf', c1 + c2, 'poly')
            else:
                return (Inf(Decimal('-inf')), 'neg_inf', -1, '?')
        elif b1 == 'neg_inf' and b2 == 'neg_inf':
            # -oo * -oo = oo, compute order of infinity
            if d1 == 'poly' and d2 == 'poly':
                return (Inf(Decimal('inf')), 'pos_inf', c1 + c2, 'poly')
            else:
                return (Inf(Decimal('inf')), 'pos_inf', -1, '?')
        elif b1 == 'neg_inf' and b2 == 'pos_inf':
            # -oo * oo = -oo, compute order of infinity
            if d1 == 'poly' and d2 == 'poly':
                return (Inf(Decimal('-inf')), 'neg_inf', c1 + c2, 'poly')
            else:
                return (Inf(Decimal('-inf')), 'neg_inf', -1, '?')
        else:
            return (a1 * a2 , 'unknown', -1, "?")
    elif e.ty == OP and e.op == '/' and len(e.args) == 2:
        # Division
        a1, b1, c1, d1 = compute_limit(e.args[0])
        a2, b2, c2, d2 = compute_limit(e.args[1])
        if b1 == 'const' and b2 == 'const':
            # Both sides have finite limits
            if a1.ty == CONST and a2.ty == CONST and a1.val != 0 and a2.val == 0:
                # Case where denominator is zero
                return (a1 / a2, 'unknown', 0, "?")
            else:
                # Case where denominator is nonzero
                return (a1 / a2, 'const', 0, "?")
        elif b1 == 'pos_inf' and b2 == 'const' and a2.ty == CONST and a2.val > 0:
            # oo / pos = oo
            return (Inf(Decimal("inf")), 'pos_inf', c1, d1)
        elif b1 == 'pos_inf' and b2 == 'const' and a2.ty == CONST and a2.val < 0:
            # oo / neg = -oo
            return (Inf(Decimal("-inf")), 'neg_inf', c1, d1)
        elif b1 == 'neg_inf' and b2 == 'const' and a2.ty == CONST and a2.val > 0:
            # -oo / pos = -oo
            return (Inf(Decimal("-inf")), 'neg_inf', c1, d1)
        elif b1 == 'neg_inf' and b2 == 'const' and a2.ty == CONST and a2.val < 0:
            # -oo / neg = oo
            return (Inf(Decimal("inf")), 'pos_inf', c1, d1)
        elif b1 == 'neg_inf' and b2 == 'pos_inf':
            # -oo / oo, compare order of infinity
            if d1 == 'poly' and d2 == 'poly':
                if c1 < c2:
                    # Numerator has smaller order, result is zero
                    return (Const(0), 'const', 0, "?")
                elif c2 > c1:
                    # Numerator has bigger order, result is negative infinity,
                    # compute order of infinity of result
                    return (Inf(Decimal("-inf")), "neg_inf", c2 - c1, "poly")
                else:
                    return (a1 / a2, 'unknown', -1, '?')
            else:
                return (a1 / a2, 'unknown', -1, '?')
        elif b1 == 'neg_inf' and b2 == 'neg_inf':
            # -oo / -oo, compare order of infinity
            if d1 == 'poly' and d2 == 'poly':
                if c1 < c2:
                    # Numerator has smaller order
                    return (Const(0), 'const', 0, "?")
                elif c2 > c1:
                    # Numerator has bigger order, result is positive infinity,
                    # compute order of infinity of result
                    return (Inf(Decimal("inf")), "pos_inf", c2 - c1, "poly")
                else:
                    return (a1 / a2, 'unknown', -1, '?')
            else:
                return (a1 / a2, 'unknown', -1, '?')
        elif b1 == 'pos_inf' and b2 == 'neg_inf':
            # oo / -oo, compare order of infinity
            if d1 == 'poly' and d2 == 'poly':
                if c1 < c2:
                    return (Const(0), 'const', 0, "?")
                elif c2 > c1:
                    return (Inf(Decimal("-inf")), "neg_inf", c2 - c1, "poly")
                else:
                    return (a1 / a2, 'unknown', -1, '?')
            else:
                return (a1 / a2, 'unknown', -1, '?')
        elif b1 == 'pos_inf' and b2 == 'pos_inf':
            # oo / oo, compare order of infinity
            if d1 == 'poly' and d2 == 'poly':
                if c1 < c2:
                    return (Const(0), 'const', 0, "?")
                elif c2 > c1:
                    return (Inf(Decimal("inf")), "pos_inf", c2 - c1, "poly")
                else:
                    return (a1 / a2, 'unknown', -1, '?')
            else:
                return (a1 / a2, 'unknown', -1, '?')
        elif b1 in ('const', 'indefinite_bounded') and b2 in ('neg_inf', 'pos_inf'):
            # bounded / infinity = 0
            return (Const(0), 'const', 0, "?")
        else:
            # Otherwise, return unknown
            return (a1 / a2, 'unknown', -1, "?")
    elif e.ty == OP and e.op == '^' and len(e.args) == 2:
        a1, b1, c1, d1 = compute_limit(e.args[0])
        a2, b2, c2, d2 = compute_limit(e.args[1])
        if b1 == 'const' and b2 == 'const':
            # Both sides have finite limits
            # TODO: more cases to consider
            if a1.ty == CONST and a2.ty == CONST and a1.val == 0 and a2.val < 0:
                return (a1 ^ a2, "unknown", 0, "?")
            else:
                return (a1 ^ a2, 'const', 0, "?")
        elif b1 == 'const' and a1.ty == CONST and abs(a1.val) < 1 and b2 == 'pos_inf':
            # a ^ oo = 0 where -1 < a < 1
            return (Const(0), "const", 0 ,"?")
        elif b1 == 'const' and a1.ty == CONST and a1.val > 1 and b2 == 'pos_inf':
            # a ^ oo = oo where a > 1
            return (Inf(Decimal('inf')), 'pos_inf', -1, '?')
        elif b1 == 'pos_inf' and b2 == 'const' and a2.ty == CONST and a2.val > 0:
            # oo ^ b = oo where b > 0
            return (Inf(Decimal('inf')), 'pos_inf', a2.val, d1)
        elif b1 == 'neg_inf' and b2 == 'const' and a2.ty == CONST and math.modf(a2.val)[0] == 0:
            if a2.val % 2 == 0:
                # -oo ^ b = oo, where b is an even integer
                return (Inf(Decimal('inf')), 'pos_inf', abs(a2.val), d1)
            else:
                # -oo ^ b = -oo, where b is an odd integer
                return (Inf(Decimal('-inf')), 'neg_inf', abs(a2.val), d1)
        elif b1 in ('pos_inf', 'neg_inf') and b2 == 'const' and a2.ty == CONST and a2.val < 0:
            # oo ^ b = 0, -oo ^ b = 0, where b < 0
            return (Const(0), 'const', 0, "?")
        else:
            # Otherwise, return unknown
            return (a1 ^ a2, 'unknown', -1, "?")
    elif e.ty == FUN and e.func_name in ('atan', 'acot', 'exp', "acsc", "asec"):
        # The following functions are finite within their range
        # TODO: this is not true for acsc and asec, which have infinities at zero.
        a, b, c, d = compute_limit(e.args[0])
        if b == 'const':
            return (Fun(e.func_name, a), 'const', 0, "?")
        elif e.func_name == 'atan' and b == 'pos_inf':
            # atan(oo) = pi/2
            return (Const(Fraction(1,2)) * Fun('pi'), 'const', 0, "?")
        elif e.func_name == 'atan' and b == 'neg_inf':
            # atan(-oo) = -pi/2
            return (Const(Fraction(-1,2)) * Fun('pi'), 'const', 0, "?")
        elif e.func_name == 'acot' and b == 'pos_inf':
            # acot(oo) = 0
            return (Const(0), 'const', 0, "?")
        elif e.func_name == 'acot' and b == 'neg_inf':
            # acot(-oo) = pi
            return (Fun('pi'), 'const', 0, "?")
        elif e.func_name == 'exp' and b == 'pos_inf':
            # exp(oo) = oo
            return (Inf(Decimal('inf')), 'pos_inf', -1, '?')
        elif e.func_name == 'exp' and b == 'neg_inf':
            # exp(-oo) = 0
            return (Const(0), 'const', 0, "?")
        elif e.func_name == 'asec' and b in ("pos_inf", 'neg_inf'):
            # asec(oo) = asec(-oo) = pi/2
            return (Const(Fraction(1,2)) * Fun('pi'), 'const', 0, "?")
        elif e.func_name == 'acsc' and b in ("pos_inf", 'neg_inf'):
            # acsc(oo) = acsc(-oo) = 0
            return (Const(0), 'const', 0, "?")
        else:
            # Otherwise, return unknown
            return (e, 'unknown', -1, "?")
    elif e.ty == FUN and e.func_name in ('sqrt', 'log', "sin", "cos", "asin", "acos", "tan", "cot", "csc", "sec"):
        # Other special functions
        a, b, c, d = compute_limit(e.args[0])
        if b == 'const':
            return (Fun(e.func_name, a), 'const', 0, "?")
        elif e.func_name == 'sqrt' and b == 'pos_inf':
            # sqrt(oo) = oo, compute order of infinity
            # TODO: divide into "poly" and "?" cases
            return (Inf(Decimal("inf")), 'pos_inf', c/2, d)
        elif e.func_name in ('sin', 'cos', 'asin', 'acos') and b in ("pos_inf", 'neg_inf'):
            return (Fun(e.func_name, a), 'indefinite_bounded', 0, "?")
        elif e.func_name in ('tan', 'cot', "csc", "sec") and b in ("pos_inf", 'neg_inf'):
            return (Fun(e.func_name, a), 'indefinite_unbounded', -1, "?")
        elif e.func_name == 'log' and b == "pos_inf":
            # log(oo) = oo
            # TODO: fix use of 0.0001
            return (Inf(Decimal('inf')), 'pos_inf', 0.0001, "log")
        else:
            # Otherwise, return unknown
            return (Fun(e.func_name, a), 'unknown', -1, "?")
    elif e.ty == INF and e == Inf(Decimal('inf')):
        # oo, order of infinity is 1
        return (e, 'pos_inf', 1, "poly")
    elif e.ty == INF and e == Inf(Decimal('-inf')):
        # -oo, order of infinity is 1
        return (e, 'neg_inf', 1, "poly")
    else:
        # Otherwise, return unknown
        return (e, 'unknown', -1, "?")

class LimitSimplify(Rule):
    """Simplification by computation of limits"""
    def __init__(self):
        self.name = "LimitSimplify"

    def eval(self, e):
        if isinstance(e, str):
            e = parser.parse_expr(e)

        if not isinstance(e, expr.Limit):
            return e

        var, lim, drt, body = e.var, e.lim, e.drt, e.body
        deriv = DerivativeSimplify()

        if drt == None:
            rep = body.replace_trig(Var(var), lim)
            if isinstance(body, Op) and body.op == '/' and len(body.args) == 2:
                # Case of a / b, where one of a or b are square roots. Perform the
                # computations on the square of a and b.
                if body.args[0].ty == FUN and body.args[0].func_name == 'sqrt' or \
                        body.args[1].ty == FUN and body.args[1].func_name == 'sqrt':
                    t1 = compute_limit(body.args[0].replace_trig(Var(var), lim))[1]
                    t2 = compute_limit(body.args[1].replace_trig(Var(var), lim))[1]
                    sign = 1
                    if t1 == 'pos_inf' and t2 == 'neg_inf':
                        sign = -1
                    elif t1 == 'neg_inf' and t2 == 'pos_inf':
                        sign = -1

                    # a and b are squares of numerator and denominator, respectively
                    a, b = None, None
                    if body.args[0].ty == FUN and body.args[0].func_name == 'sqrt' and \
                            body.args[1].ty == FUN and body.args[1].func_name == 'sqrt':
                        # Both sides are square roots
                        a = body.args[0].args[0]
                        b = body.args[1].args[0]
                    elif body.args[0].ty == FUN and body.args[0].func_name == 'sqrt':
                        # Numerator is square root
                        a = body.args[0].args[0]
                        b = body.args[1] ^ 2
                    elif body.args[1].ty == FUN and body.args[1].func_name == 'sqrt':
                        # Denominator is square root
                        a = body.args[0] ^ 2
                        b = body.args[1].args[0]

                    # repa and repb are limits of a and b
                    repa, repb = a.replace_trig(Var(var), lim), b.replace_trig(Var(var), lim)

                    # Apply L'Hopital's rule
                    while (repa.normalize() == Const(0) and repb.normalize() == Const(0) \
                           or compute_limit(repa)[1] in ('pos_inf', 'neg_inf') and \
                           compute_limit(repb)[1] in ('pos_inf', 'neg_inf')):
                        a, b = deriv.eval(expr.Deriv(var, a)), deriv.eval(expr.Deriv(var, b))
                        repa, repb = a.replace_trig(Var(var), lim), b.replace_trig(Var(var), lim)

                    # Take square root of the result
                    return compute_limit(Const(sign) * Fun('sqrt', repa / repb))

                # Apply L'Hopital's rule
                while (compute_limit(rep.args[0])[1] == 'const' and \
                        compute_limit(rep.args[1])[1] == 'const' and \
                        rep.args[1].normalize() == Const(0) and \
                        rep.args[0].normalize() == Const(0) \
                        or compute_limit(rep.args[0])[1] in ('pos_inf', 'neg_inf') and \
                           compute_limit(rep.args[1])[1] in ('pos_inf', 'neg_inf')):
                    new_body = LHopital().eval(e).body
                    e = expr.Limit(var, lim, new_body, drt)
                    rep = new_body.replace_trig(Var(var), lim)

            elif isinstance(body, Op) and body.op == '-' and len(body.args) == 2 \
                    and (body.args[0].ty == FUN and body.args[0].func_name == 'sqrt' or \
                    body.args[1].ty == FUN and body.args[1].func_name == 'sqrt'):
                # Case of a - b, where one of a and b are square roots, perform the
                # computation after rewriting to (a^2 - b^2) / (a + b)
                a, b = body.args
                repa, repb = a.replace_trig(Var(var), lim), b.replace_trig(Var(var), lim)

                if compute_limit(repa)[1] == 'pos_inf' and \
                        compute_limit(repb)[1] == 'pos_inf' or \
                        compute_limit(repa)[1] == 'neg_inf' and \
                        compute_limit(repb)[1] == 'neg_inf':
                    # Case oo - oo or -oo - (-oo)
                    # Let ta = a, tb = b, t1 = a^2, t2 = b^2
                    ta, tb = a, b
                    t1, t2 = ta ^ 2, tb ^ 2
                    if ta.ty == FUN and ta.func_name == 'sqrt':
                        t1 = ta.args[0]
                    if tb.ty == FUN and tb.func_name == 'sqrt':
                        t2 = tb.args[0]
                    a = t1 - t2
                    b = ta + tb
                    a = a.normalize()
                    b = b.normalize()
                    repa, repb = a.replace_trig(Var(var), lim), b.replace_trig(Var(var), lim)
                    while (compute_limit(repa)[1] in ('pos_inf', 'neg_inf') and \
                           compute_limit(repb)[1] in ('pos_inf', 'neg_inf')):
                        newa, newb = deriv.eval(expr.Deriv(var, a)), deriv.eval(expr.Deriv(var, b))
                        a, b = newa, newb
                        repa, repb = a.replace_trig(Var(var), lim), b.replace_trig(Var(var), lim)
                    return compute_limit(repa / repb)

            elif isinstance(body, Fun) and isinstance(body.args[0], Op) and body.args[0].op == '/':
                # Case of function application, where the argument is a / b
                a, b = body.args[0].args[0], body.args[0].args[1]
                repa, repb = a.replace_trig(Var(var), lim), b.replace_trig(Var(var), lim)

                while (repa.normalize() == Const(0) and repb.normalize() == Const(0) \
                       or compute_limit(repa)[1] in ('pos_inf', 'neg_inf') and \
                       compute_limit(repb)[1] in ('pos_inf', 'neg_inf')):
                    newa, newb = deriv.eval(expr.Deriv(var, a)), deriv.eval(expr.Deriv(var, b))
                    a, b = newa, newb
                    repa, repb = a.replace_trig(Var(var), lim), b.replace_trig(Var(var), lim)
                return compute_limit(Fun(body.func_name, repa / repb))

            elif body.ty == OP and body.op == '^' and body.args[1].ty == VAR and body.args[1].name == var \
                and (body.args[0] == Op('+',Const(1),Op('/',Const(1),Var(var))) or \
                     body.args[0] == Op('+',Op('/', Const(1), Var(var)), Const(1) ) or \
                     body.args[0] == Op('+', Const(1), Op('^',  Var(var), Const(-1))) or \
                     body.args[0] == Op('+', Op('^' , Var(var), Const(-1)), Const(1))):
                # lim x -> oo. (1 + 1 / x) ^ x = e
                return (Fun('exp', Const(1)), 'const', 0, "?")

            res = compute_limit(rep)
            return res
        else:
            raise NotImplementedError


class DerivIntExchange(Rule):
    """Exchanging derivative and integral"""
    def __init__(self):
        self.name = "Exchange of derivative and integral"

    def eval(self, e):
        if not e.is_deriv() or not e.body.is_integral():
            raise AssertionError("DerivIntExchange: unexpected form of input")

        v1, v2 = e.var, e.body.var
        return Integral(v2, e.body.lower, e.body.upper, Deriv(v1, e.body.body))
