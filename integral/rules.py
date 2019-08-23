"""Rules for integration."""

from integral import expr
from integral import poly
from integral.expr import Var, Const, Fun, EvalAt

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
        return expr.from_poly(e.to_poly())

class Linearity(Rule):
    """Applies linearity rules:
    
    INT (a + b) = INT a + INT b,
    INT (c * a) = c * INT a  (where c is a constant).

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
    INT x^n = x^(n+1) / (n+1),  (where n > 0)
    INT sin(x) = -cos(x),
    INT cos(x) = sin(x),
    INT 1/x = log(x),  (where the range is positive)

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
                # Integral of x^n is x^(n+1)/(n+1)
                a, b = e.body.args
                if a == Var(e.var) and b.ty == expr.CONST:
                    integral = (Var(e.var) ^ Const(b.val + 1)) / Const(b.val + 1)
                    return EvalAt(e.var, e.lower, e.upper, integral)
                else:
                    return e
            else:
                return e
        else:
            return e
