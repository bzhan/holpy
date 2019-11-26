"""Rules for integration."""

from integral import expr
from integral import poly
from integral.expr import Var, Const, Fun, EvalAt, Op
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
        return e.normalize()

class Linearity(Rule):
    """Applies linearity rules:
    
    INT (a + b) = INT a + INT b,
    INT (c * a) = c * INT a  (where c is a constant).
    INT (c / a) = c * INT 1 / a (where c is a contant)
    """
    def eval(self, e):
        if e.ty != expr.INTEGRAL:
            return e

        p = e.body.to_poly()
        ts = []
        for mono in p.monomials:
            t = expr.Integral(e.var, e.lower, e.upper, expr.from_mono(poly.Monomial(1, mono.factors)))
            if mono.coeff != 1:
                t = Const(mono.coeff) * t
            ts.append(t)

        if len(ts) == 0:
            return Const(0)
        else:
            return sum(ts[1:], ts[0])

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
                if (a == Var(e.var) or a.op in ("+", "-") and a.args[0] == Var(e.var) and \
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

        d_subst = expr.deriv(e.var, self.var_subst)
        body2 = e.body.replace(self.var_subst, expr.Var(self.var_name)) / d_subst
        lower2 = self.var_subst.subst(e.var, e.lower).normalize()
        upper2 = self.var_subst.subst(e.var, e.upper).normalize()
        return expr.Integral(self.var_name, lower2, upper2, body2)

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
        assert isinstance(e.body, expr.Op) and e.body.op == "/"
        dividend = e.body.args[0].normalize().to_poly().standardize()
        divisor = e.body.args[1].normalize().to_poly().standardize()
        if dividend.degree < divisor.degree:
            return e
        jieguo = []
        quotinent = dividend.monomials[0] / divisor.monomials[0]
        jieguo.append(quotinent)
        s = poly.Polynomial([quotinent]) * divisor
        #k is the remainder
        k = poly.Polynomial(tuple(dividend.monomials[0:divisor.degree+1])) - s
        if k.is_zero_constant():
            return expr.Integral(e.var, e.lower, e.upper, expr.from_poly(poly.Polynomial(jieguo)) + expr.from_poly(poly.Polynomial(dividend.monomials[-k.monomials[-1].degree:]).del_zero_mono()) \
                        /expr.from_poly(divisor.del_zero_mono()))
        k = poly.Polynomial(tuple(k.monomials[1:]))
        k = k + poly.Polynomial([dividend.monomials[-k.degree]])
        #every time delete the first item which coffe has been 0 after sub
        while not k.degree < divisor.degree and not k.is_nonzero_constant():
            quotinent = k.monomials[0] / divisor.monomials[0]
            jieguo.append(quotinent)
            s = poly.Polynomial([quotinent]) * divisor
            k = k - s
            if k.is_zero_constant():
                return expr.Integral(e.var, e.lower, e.upper, expr.from_poly(poly.Polynomial(jieguo)) + expr.from_poly(poly.Polynomial(dividend.monomials[-k.monomials[-1].degree:]).del_zero_mono()) \
                        /expr.from_poly(divisor.del_zero_mono()))
            k = k + poly.Polynomial([dividend.monomials[-k.degree]])
            k = poly.Polynomial(tuple(k.monomials[1:]))
        return expr.Integral(e.var, e.lower, e.upper, expr.from_poly(poly.Polynomial(jieguo)) + expr.from_poly(poly.Polynomial(k.monomials))/expr.from_poly(divisor))

