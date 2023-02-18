"""Intervals and propagation algorithm."""
import fractions
from typing import Dict, Tuple, Optional

from integral import expr
from integral.expr import eval_expr, Expr


# Tolerance for floating-point rounding errors
tol = 1e-16

class Interval:
    """Specifies an interval. Each side can be either open or closed."""
    def __init__(self, start: Expr, end: Expr, left_open: bool, right_open: bool):
        self.start = start
        self.end = end
        self.left_open = left_open
        self.right_open = right_open

    def __str__(self):
        left = '(' if self.left_open else '['
        right = ')' if self.right_open else ']'
        return left + str(self.start) + ', ' + str(self.end) + right

    @staticmethod
    def closed(start: Expr, end: Expr) -> "Interval":
        return Interval(start, end, left_open=False, right_open=False)

    @staticmethod
    def open(start: Expr, end: Expr) -> "Interval":
        return Interval(start, end, left_open=True, right_open=True)

    @staticmethod
    def lopen(start: Expr, end: Expr) -> "Interval":
        return Interval(start, end, left_open=True, right_open=False)

    @staticmethod
    def ropen(start: Expr, end: Expr) -> "Interval":
        return Interval(start, end, left_open=False, right_open=True)

    @staticmethod
    def point(val: Expr) -> "Interval":
        return Interval.closed(val, val)

    @staticmethod
    def from_condition(cond: Expr) -> Optional[Tuple[Expr, "Interval"]]:
        """Obtain interval from condition."""

        # First consider the absolute value cases
        if cond.is_less() and cond.args[0].is_fun() and cond.args[0].func_name == 'abs' and cond.args[1].is_constant():
            # |x| < const  ==>  x in (-const, const)
            return cond.args[0].args[0], Interval.open(-cond.args[1], cond.args[1])
        if cond.is_less_eq() and cond.args[0].is_fun() and cond.args[0].func_name == 'abs' and cond.args[1].is_constant():
            # |x| <= const  ==>  x in [-const, const]
            return cond.args[0].args[0], Interval.close(-cond.args[1], cond.args[1])

        # Then cases where one side is constant, and other side is arbitrary
        if cond.is_less() and cond.args[1].is_constant():
            # x < const  ==>  x in (-oo, const)
            return cond.args[0], Interval.open(expr.NEG_INF, cond.args[1])
        if cond.is_less() and cond.args[0].is_constant():
            # const < x  ==>  x in (const, oo)
            return cond.args[1], Interval.open(cond.args[0], expr.POS_INF)
        if cond.is_less_eq() and cond.args[1].is_constant():
            # x <= const  ==>  x in (-oo, const]
            return cond.args[0], Interval.lopen(expr.NEG_INF, cond.args[1])
        if cond.is_less_eq() and cond.args[0].is_constant():
            # const <= x  ==>  x in [const, oo)
            return cond.args[1], Interval.ropen(cond.args[0], expr.POS_INF)
        if cond.is_equals() and cond.args[1].is_constant():
            return cond.args[0], Interval.point(cond.args[1])
        if cond.is_equals() and cond.args[0].is_constant():
            return cond.args[1], Interval.point(cond.args[0])
        if cond.is_greater():
            return Interval.from_condition(expr.Op("<", cond.args[1], cond.args[0]))
        if cond.is_greater_eq():
            return Interval.from_condition(expr.Op("<=", cond.args[1], cond.args[0]))

        # Cannot be converted to condition on intervals
        return None

    def is_closed(self) -> bool:
        return not self.left_open and not self.right_open

    def is_open(self) -> bool:
        return self.left_open and self.right_open

    def __add__(self, other: "Interval") -> "Interval":
        """Addition in interval arithmetic."""
        from integral.poly import normalize_constant
        if self.start == expr.NEG_INF or other.start == expr.NEG_INF:
            start = expr.NEG_INF
        else:
            start = normalize_constant(self.start + other.start)
        if self.end == expr.POS_INF or other.end == expr.POS_INF:
            end = expr.POS_INF
        else:
            end = normalize_constant(self.end + other.end)
        return Interval(start, end, self.left_open or other.left_open,
                        self.right_open or other.right_open)

    def __neg__(self) -> "Interval":
        """Negation (unitary minus) of an interval."""
        return Interval(-self.end, -self.start, self.right_open, self.left_open)

    def __sub__(self, other: "Interval") -> "Interval":
        """Subtraction in interval arithmetic."""
        return self + (-other)

    def __mul__(self, other: "Interval") -> "Interval":
        """Product in interval arithmetic."""
        from integral.poly import normalize_constant
        def lim_mul(a: Expr, b: Expr):
            if a == expr.POS_INF and eval_expr(b) > 0:
                return expr.POS_INF
            if a == expr.POS_INF and eval_expr(b) < 0:
                return expr.NEG_INF
            if a == expr.NEG_INF and eval_expr(b) < 0:
                return expr.POS_INF
            if a == expr.NEG_INF and eval_expr(b) > 0:
                return expr.NEG_INF
            if a == expr.POS_INF and b == expr.POS_INF:
                return expr.POS_INF
            if a == expr.POS_INF and b == expr.NEG_INF:
                return expr.NEG_INF
            if a == expr.NEG_INF and b == expr.POS_INF:
                return expr.NEG_INF
            if a == expr.NEG_INF and b == expr.NEG_INF:
                return expr.POS_INF
            if a.is_inf() and b == expr.Const(0):
                return None
            if b.is_inf():
                return lim_mul(b, a)
            return normalize_constant(a * b)

        bounds = [
            (lim_mul(self.start, other.start), self.left_open or other.left_open),
            (lim_mul(self.start, other.end), self.left_open or other.right_open),
            (lim_mul(self.end, other.start), self.right_open or other.left_open),
            (lim_mul(self.end, other.end), self.right_open or other.right_open)
        ]
        bounds = [bd for bd in bounds if bd[0] is not None]

        start, left_open = min(bounds, key=lambda p: (eval_expr(p[0]), p[1]))
        end, right_open = max(bounds, key=lambda p: (eval_expr(p[0]), p[1]))
        return Interval(start, end, left_open, right_open)

    def inverse(self) -> "Interval":
        """Inverse of an interval."""
        from integral.poly import normalize_constant
        if self.end == expr.POS_INF:
            start = expr.Const(0)
            left_open = True
        elif eval_expr(self.end) == 0:
            start = expr.NEG_INF
            left_open = True
        else:
            start = normalize_constant(1 / self.end)
            left_open = self.right_open
        if self.start == expr.NEG_INF:
            end = expr.Const(0)
            right_open = True
        elif eval_expr(self.start) == 0:
            end = expr.POS_INF
            right_open = True
        else:
            end = normalize_constant(1 / self.start)
            right_open = self.left_open
        return Interval(start, end, left_open, right_open)

    def __truediv__(self, other: "Interval") -> "Interval":
        """Quotient in interval arithmetic."""
        return self * other.inverse()

    def __pow__(self, other: "Interval") -> "Interval":
        """Power in interval arithmetic."""
        from integral.poly import normalize_constant
        from integral import limits
        if eval_expr(other.start) == eval_expr(other.end):
            # Exponent has single value
            if eval_expr(other.start) == 0:
                return Interval.point(expr.Const(1))
            elif eval_expr(other.start) == 2:
                # Simple case
                if eval_expr(self.start) >= 0:
                    return Interval(normalize_constant(self.start ** expr.Const(2)),
                                    normalize_constant(self.end ** expr.Const(2)) \
                        if not self.end.is_inf() else expr.POS_INF, self.left_open, self.right_open)
                else:
                    es, ee = eval_expr(self.start), eval_expr(self.end)
                    if es == float('-inf'):
                        if ee <= 0:
                            return Interval(normalize_constant(self.end ** expr.Const(2)), \
                                            expr.POS_INF, self.right_open, True)
                        elif ee > 0:
                            return Interval(expr.Const(0), expr.POS_INF, False, True)
                    elif es < 0:
                        if ee <= 0:
                            return Interval(normalize_constant(self.end ** expr.Const(2)), \
                                            normalize_constant(self.start ** expr.Const(2)), \
                                            self.right_open, self.left_open)
                        elif ee > 0:
                            if ee == float('inf'):
                                return Interval.ropen(expr.Const(0), expr.POS_INF)
                            else:
                                aee, aes = abs(ee), abs(es)
                                if aes > aee:
                                    return Interval(expr.Const(0), normalize_constant(self.start ** expr.Const(2)), \
                                                    False, self.left_open)
                                elif aes == aee:
                                    return Interval(expr.Const(0), normalize_constant(self.start ** expr.Const(2)), \
                                                    False, self.left_open and self.right_open)
                                else:
                                    return Interval(expr.Const(0), normalize_constant(self.end ** expr.Const(2)), \
                                                    False, self.right_open)
                return Interval.ropen(expr.Const(0), expr.POS_INF)
            elif eval_expr(other.start) > 0:
                # TODO: distinguish by parity of denominator        
                if self.start == expr.NEG_INF:
                    start = expr.NEG_INF
                else:
                    start = self.start ** other.start
                if self.end == expr.POS_INF:
                    end = expr.POS_INF
                else:
                    end = self.end ** other.end
                return Interval(start, end, self.left_open or other.left_open,
                                self.right_open or other.right_open)
            elif eval_expr(other.start) < 0:
                return (self ** Interval.point(-other.start)).inverse()
        else:
            if eval_expr(self.start) > 0:
                if eval_expr(other.start) > 0:
                    r = eval_expr(self.end) * eval_expr(other.end)
                    l = eval_expr(self.start) * eval_expr(other.start)
                    if r != float('inf'):
                        r = normalize_constant(self.end * other.end)
                        l = normalize_constant(self.start * other.start)
                        return Interval(l, r, self.left_open or other.left_open, self.right_open or other.right_open)
                    else:
                        l = expr.Const(fractions.Fraction(l))
                        return Interval(l, expr.POS_INF, self.left_open or other.left_open, True)
            return Interval.open(expr.NEG_INF, expr.POS_INF)

    def less(self, other: "Interval") -> bool:
        """Whether self is strictly less than other."""
        if eval_expr(self.end) < eval_expr(other.start):
            return True
        elif eval_expr(self.end) <= eval_expr(other.start):
            return self.right_open or other.left_open
        else:
            return False

    def less_eq(self, other: "Interval") -> bool:
        """Whether self is less than or equal to other."""
        return eval_expr(self.end) <= eval_expr(other.start)

    def greater(self, other: "Interval") -> bool:
        """Whether self is strictly greater htan other."""
        return other.less(self)

    def greater_eq(self, other: "Interval") -> bool:
        """Whether self is greater than or equal to other."""
        return other.less_eq(self)

    def not_eq(self, other: "Interval") -> bool:
        """Whether there is no overlap between self and other (either less or greater)."""
        return self.less(other) or self.greater(other)

    def contained_in(self, other: "Interval") -> bool:
        """Whether self is contained in other."""
        if eval_expr(self.start) < eval_expr(other.start) - tol:
            return False
        if abs(eval_expr(self.start) - eval_expr(other.start)) < tol and \
            (not self.left_open) and other.left_open:
            return False
        if eval_expr(self.end) > eval_expr(other.end) + tol:
            return False
        if abs(eval_expr(self.end) - eval_expr(other.end)) < tol and \
            (not self.right_open) and other.right_open:
            return False
        return True

    def intersection(self, other: "Interval") -> "Interval":
        """Return the intersection of two intervals."""
        if eval_expr(self.start) > eval_expr(other.start):
            start = self.start
            left_open = self.left_open
        elif eval_expr(self.start) < eval_expr(other.start):
            start = other.start
            left_open = other.left_open
        else:
            start = self.start
            left_open = self.left_open or other.left_open
        
        if eval_expr(self.end) < eval_expr(other.end):
            end = self.end
            right_open = self.right_open
        elif eval_expr(self.end) > eval_expr(other.end):
            end = other.end
            right_open = other.right_open
        else:
            end = self.end
            right_open = self.right_open or other.right_open
        return Interval(start, end, left_open, right_open)

    def sqrt(self) -> "Interval":
        """Square root of interval."""
        from integral.poly import normalize_constant
        if eval_expr(self.start) <= 0:
            start = expr.Const(0)
        else:
            start = normalize_constant(expr.Fun('sqrt', self.start))
        if self.end == expr.POS_INF:
            end = expr.POS_INF
        else:
            end = normalize_constant(expr.Fun('sqrt', self.end))
        return Interval(start, end, self.left_open, self.right_open)

    def exp(self) -> "Interval":
        """Exp function of an interval."""
        from integral.poly import normalize_constant
        if self.start == expr.NEG_INF:
            start = expr.Const(0)
        else:
            start = normalize_constant(expr.Fun('exp', self.start))
        if self.end == expr.POS_INF:
            end = expr.POS_INF
        else:
            end = normalize_constant(expr.Fun('exp', self.end))
        return Interval(start, end, self.left_open, self.right_open)

    def log(self) -> "Interval":
        """Log function of an interval."""
        from integral.poly import normalize_constant
        if eval_expr(self.start) <= 0:
            start = expr.NEG_INF
        else:
            start = normalize_constant(expr.Fun('log', self.start))
        if self.end == expr.POS_INF:
            end = expr.POS_INF
        else:
            end = normalize_constant(expr.Fun('log', self.end))
        return Interval(start, end, self.left_open, self.right_open)

    def sin(self) -> "Interval":
        """Sin function of an interval."""
        if self.contained_in(Interval.closed(-(expr.pi / 2), expr.pi / 2)):
            return Interval(expr.Fun('sin', self.start), expr.Fun('sin', self.end),
                            self.left_open, self.right_open)
        elif self.contained_in(Interval.open(expr.Const(0), expr.pi)):
            return Interval.lopen(expr.Const(0), expr.Const(1))
        elif self.contained_in(Interval.closed(expr.Const(0), expr.pi)):
            return Interval.closed(expr.Const(0), expr.Const(1))
        else:
            return Interval.closed(expr.Const(-1), expr.Const(1))

    def cos(self) -> "Interval":
        """Cos function of an interval."""
        if self.contained_in(Interval.closed(expr.Const(0), expr.pi)):
            return Interval(expr.Fun('cos', self.end), expr.Fun('cos', self.start),
                            self.right_open, self.left_open)
        elif self.contained_in(Interval.closed(-(expr.pi / 2), expr.pi / 2)):
            return Interval.closed(expr.Const(0), expr.Const(1))
        else:
            return Interval.closed(expr.Const(-1), expr.Const(1))


def get_bounds_for_expr(e: Expr, bounds: Dict[Expr, Interval]) -> Interval:
    """Obtain the range of expression e as a variable.

    e - Expr, an expression.
    bounds - dict(Expr, Interval): mapping from expressions to intervals.

    Returns bounds on the values of e. If None, no bound can be obtained.

    """
    def rec(e: Expr) -> Interval:
        if e in bounds:
            return bounds[e]

        if e.is_const():
            return Interval.closed(e, e)

        if e.is_op():
            if e.is_plus():
                a = rec(e.args[0])
                b = rec(e.args[1])
                return a + b
            elif e.is_uminus():
                a = rec(e.args[0])
                return -a
            elif e.is_minus():
                a = rec(e.args[0])
                b = rec(e.args[1])
                return a - b
            elif e.is_times():
                a = rec(e.args[0])
                b = rec(e.args[1])
                res = a * b
                return res
            elif e.is_divides():
                a = rec(e.args[0])
                b = rec(e.args[1])
                return a / b
            elif e.is_power():
                a = rec(e.args[0])
                b = rec(e.args[1])
                return a ** b

        elif e.is_fun():
            if e.func_name == 'sqrt':
                return rec(e.args[0]).sqrt()
            elif e.func_name == 'exp':
                return rec(e.args[0]).exp()
            elif e.func_name == 'log':
                return rec(e.args[0]).log()
            elif e.func_name == 'sin':
                return rec(e.args[0]).sin()
            elif e.func_name == 'cos':
                return rec(e.args[0]).cos()
            elif e.func_name == 'factorial':
                return Interval.ropen(expr.Const(1), expr.POS_INF)
            elif e.func_name == 'Gamma':
                a = rec(e.args[0])
                if a.contained_in(Interval.open(expr.Const(0), expr.POS_INF)):
                    return Interval.open(expr.Const(0), expr.POS_INF)
                else:
                    return Interval.open(expr.NEG_INF, expr.POS_INF)

        elif e.is_integral():
            if get_bounds_for_expr(e.body, bounds).contained_in(Interval.open(expr.Const(0), expr.POS_INF)) and \
                e.lower.is_evaluable() and e.upper.is_evaluable() and eval_expr(e.lower) < eval_expr(e.upper):
                return Interval.open(expr.Const(0), expr.POS_INF)

        # No information
        return Interval.open(expr.NEG_INF, expr.POS_INF)

    res = rec(e)
    return res
