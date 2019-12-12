"""Rules for integration."""

from integral import expr
from integral import poly
from integral.expr import Var, Const, Fun, EvalAt, Op, Integral, Expr, trig_identity
import functools, operator
from sympy import apart
from sympy.parsing import sympy_parser
from sympy import solvers
from integral import parser

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
    def eval(self, e):
        e = e.normalize()
        if e.ty == expr.INTEGRAL and e.body.ty == expr.OP and e.body.op == "/":
            old = e
            up_monos, up_common     = expr.extract(e.body.args[0].to_poly())
            down_monos, down_common = expr.extract(e.body.args[1].to_poly())
            common_item = up_common.keys() & down_common.keys()
            min_value = {}
            for key in common_item:
                min_value[key]    = up_common[key] if up_common[key] < down_common[key] else down_common[key]
                up_common[key]   -= min_value[key]
                down_common[key] -= min_value[key]
            if len(min_value) != 0:
                #numerartor and denominator have same element.
                upp   = [(k ^ Const(v)).normalize() for k, v in up_common.items()]
                dpp   = [(k ^ Const(v)).normalize() for k, v in down_common.items()]
                upp_1 = functools.reduce(operator.mul, upp[1:], upp[0])
                dpp_1 = functools.reduce(operator.mul, dpp[1:], dpp[0])
                simp  = (sum(up_monos[1:], up_monos[0]) * upp_1).normalize() / (sum(down_monos[1:], down_monos[0]) * dpp_1).normalize()
                return Integral(old.var, old.lower, old.upper, simp.normalize())
            else:
                return Integral(old.var, old.lower, old.upper, old.body.args[0].normalize()/old.body.args[1].normalize())
        else:
            return e.normalize()

class Linearity(Rule):
    """Applies linearity rules:
    
    INT (a + b) = INT a + INT b,
    INT (c * a) = c * INT a  (where c is a constant).
    INT (c / a) = c * INT 1 / a (where c is a contant)
    """
    def eval(self, e):
        def eval1(e):
            if e.ty != expr.INTEGRAL:
                return e           
            p = e.body.to_poly()
            ts = []
            for mono in p.monomials:
                t = expr.Integral(e.var, e.lower, e.upper, expr.from_mono(poly.Monomial(Const(1), mono.factors)))
                if mono.coeff != Const(1):
                    if isinstance(mono.coeff, expr.Op):
                        t = mono.coeff * t
                    else:
                        t = mono.coeff * t
                ts.append(t)
            if len(ts) == 0:
                return Const(0)
            else:
                return sum(ts[1:], ts[0])
        integrals = e.separate_integral()
        result = []
        for i in integrals:
            result.append(eval1(i))
        for i in range(len(integrals)):
            e = e.replace_trig(integrals[i], result[i])
        return e

class CommonIntegral(Rule):
    """Applies common integrals:

    INT c = c * x,
    INT x ^ n = x ^ (n + 1) / (n + 1),  (where n != -1, c is a constant)
    INT (x + c) ^ n = (x + c) ^ (n + 1) / (n + 1)
    INT 1 / x ^ n = (-n) / x ^ (n + 1), (where n != 1)
    INT sin(x) = -cos(x),
    INT cos(x) = sin(x),
    INT 1 / (x + c) = log(x + c),  (where the range is positive, c is a constant)
    INT e^x = e^x
    INT 1 / (x^2 + 1) = arctan(x)
    """
    def eval(self, e):
        if e.ty != expr.INTEGRAL:
            return e

        if e.body == Var(e.var):
            # Integral of x is x^2/2.
            return EvalAt(e.var, e.lower, e.upper, (Var(e.var) ^ Const(2)) / Const(2))
        elif e.body.ty == expr.CONST: 
            if e.body.val == 1:
                # Integral of 1 is x
                integral = Var(e.var)
            else:
                # Integral of c is c*x
                integral = e.body * Var(e.var)
            return EvalAt(e.var, e.lower, e.upper, integral)
        elif e.body.ty == expr.OP:
            if e.body.op == "^":
                a, b = e.body.args
                if a.ty == expr.CONST and b.ty == expr.CONST:
                    integral = e.body * Var(e.var)
                    return EvalAt(e.var, e.lower, e.upper, integral)
                elif (a == Var(e.var) or a.op in ("+", "-") and a.args[0] == Var(e.var) and \
                        a.args[1].ty == expr.CONST) and b.ty == expr.CONST and \
                            b.val != -1:
                    # Integral of x ^ n is x ^ (n + 1)/(n + 1)
                    # Intgeral of (x + c) ^ n = (x + c) ^ (n + 1) / (n + 1)
                    integral = (a ^ Const(b.val + 1)) / Const(b.val + 1)
                    return EvalAt(e.var, e.lower, e.upper, integral)
                elif (a == Var(e.var) or a.op in ("+", "-") and a.args[0] == Var(e.var) and \
                        a.args[1].ty == expr.CONST) and b.ty == expr.CONST and b.val == -1:
                    # Integral of x ^ -1 is log(x)
                    # Integral of (x + c) ^ -1 is log(x)
                    return EvalAt(e.var, e.lower, e.upper, expr.log(a))
                else:
                    return e
            elif e.body.op == "/":
                a, b = e.body.args
                if b.ty == expr.OP and a.ty == expr.CONST:
                    c, d = b.args
                    if b.op == "^":
                        if (c == Var(e.var) or c.op in ("+", "-") and c.args[0] == Var(e.var) and \
                                c.args[1].ty == expr.CONST) and d.ty == expr.CONST and d.val != 1:
                            #Integral of 1 / x ^ n is (-n) / x ^ (n + 1)
                            #Integral of 1 / (x + c) ^ n is (-1) / (n - 1) * x ^ (n - 1)
                            integral = a * Const(-1) / (Const(d.val - 1) * (c ^ Const(d.val - 1)))
                            return EvalAt(e.var, e.lower, e.upper, integral)
                    elif b.op in ("+", "-"):
                        if c == Var(e.var) and d.ty == expr.CONST:
                            #Integral of 1 / (x + c) is log(x + c)
                            return EvalAt(e.var, e.lower, e.upper, a * expr.log(b))
                        elif b.op == "+" and c.ty == expr.OP and c.op == "^" and \
                                c.args[0] == Var(e.var) and c.args[1] == Const(2) and \
                                d == expr.Const(1):
                            #Integral of 1 / x ^ 2 + 1 is arctan(x)
                            return EvalAt(e.var, e.lower, e.upper, a * expr.arctan(Var(e.var)))
                elif b == Var(e.var):
                    return EvalAt(e.var, e.lower, e.upper, a * expr.log(b))
            else:
                return e

        elif e.body.ty == expr.FUN:
            if e.body.func_name == "sin" and e.body.args[0] == Var(e.var):
                return EvalAt(e.var, e.lower, e.upper, -expr.cos(Var(e.var)))
            elif e.body.func_name == "cos" and e.body.args[0] == Var(e.var):
                return EvalAt(e.var, e.lower, e.upper, expr.sin(Var(e.var)))
            elif e.body.func_name == "exp" and e.body.args[0] == Var(e.var):
                return EvalAt(e.var, e.lower, e.upper, expr.exp(Var(e.var)))
            else:
                return e
        else:
            return e

class CommonDeriv(Rule):
    """Common rules for evaluating a derivative."""

    def eval(self, e):
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
        else:
            raise NotImplementedError

class Substitution(Rule):
    """Apply substitution."""
    def __init__(self, var_name, var_subst):
        assert isinstance(var_name, str) and isinstance(var_subst, expr.Expr)
        self.var_name = var_name
        self.var_subst = var_subst

    def eval(self, e):
        if e.ty != expr.INTEGRAL:
            return e
        self.var_name = parser.parse_expr(self.var_name)
        d_subst_1 = expr.deriv(str(self.var_name.findVar()), self.var_name)
        d_subst = expr.deriv(e.var, self.var_subst)
        body2 = e.body.replace_trig(self.var_subst, self.var_name) * (d_subst_1 / d_subst)
        body2 = parser.parse_expr(str(sympy_parser.parse_expr(str(body2).replace("^","**"))).replace("**","^"))
        if self.var_name.ty == expr.VAR:
            #u subsitutes f(x)
            lower2 = self.var_subst.subst(e.var, e.lower).normalize()
            upper2 = self.var_subst.subst(e.var, e.upper).normalize()
        else:
            #x substitue g(u)
            lower2 = solvers.solve(sympy_parser.parse_expr(str(self.var_name - e.lower).replace("^","**")), sympy_parser.parse_expr(str(self.var_name.findVar())))[0]
            upper2 = solvers.solve(sympy_parser.parse_expr(str(self.var_name - e.upper).replace("^","**")), sympy_parser.parse_expr(str(self.var_name.findVar())))[0]
            lower2 = parser.parse_expr(str(lower2).replace("**", "^"))
            upper2 = parser.parse_expr(str(upper2).replace("**", "^"))
        return expr.Integral(self.var_name.findVar().name, lower2, upper2, body2)

class Equation(Rule):
    """Apply substitution for equal expressions"""
    def __init__(self, old_expr, new_expr):
        assert isinstance(old_expr, Expr) and isinstance(new_expr, Expr)
        self.old_expr = old_expr
        self.new_expr = new_expr
    
    def eval(self, e):
        if self.old_expr.normalize() != self.new_expr.normalize():
            return e
        else:
            return Integral(e.var, e.lower, e.upper, self.new_expr)

class TrigSubstitution(Rule):
    """Apply trig identities transformation on expression."""
    def eval(self, e):
        exprs =  e.body.identity_trig_expr(trig_identity)
        n_expr = [] #exprs in a tuple        
        for i in range(len(exprs)):
            n_expr.append((Integral(e.var, e.lower, e.upper, exprs[i][0]),exprs[i][1]))
        return n_expr
        

class IntegrationByParts(Rule):
    """Apply integration by parts."""
    def __init__(self, u, v):
        assert isinstance(u, expr.Expr) and isinstance(v, expr.Expr)
        self.u = u
        self.v = v

    def eval(self, e):
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
            raise NotImplementedError

class PolynomialDivision(Rule):
    """Simplify the representation of polynomial divided by polinomial.
    """
    def eval(self, e):
        result = apart(sympy_parser.parse_expr(str(e.body).replace("^", "**")))
        return expr.Integral(e.var, e.lower, e.upper, parser.parse_expr(str(result).replace("**","^")))