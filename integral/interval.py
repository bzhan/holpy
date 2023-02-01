"""Intervals and propagation algorithm."""

from typing import Dict

from integral import expr
from integral.expr import Expr, eval_expr

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

    def is_closed(self) -> bool:
        return not self.left_open and not self.right_open

    def is_open(self) -> bool:
        return self.left_open and self.right_open

    def __add__(self, other: "Interval") -> "Interval":
        """Addition in interval arithmetic."""
        return Interval((self.start + other.start).normalize_constant(),
                        (self.end + other.end).normalize_constant(),
                        self.left_open or other.left_open,
                        self.right_open or other.right_open)

    def __neg__(self) -> "Interval":
        """Negation (unitary minus) of an interval."""
        return Interval(-self.end, -self.start, self.right_open, self.left_open)

    def __sub__(self, other: "Interval") -> "Interval":
        """Subtraction in interval arithmetic."""
        return self + (-other)

    def __mul__(self, other: "Interval") -> "Interval":
        """Product in interval arithmetic."""
        bounds = [
            (self.start * other.start, self.left_open or other.left_open),
            (self.start * other.end, self.left_open or other.right_open),
            (self.end * other.start, self.right_open or other.left_open),
            (self.end * other.end, self.right_open or other.right_open)
        ]

        start, left_open = min(bounds, key=lambda p: (eval_expr(p[0]), p[1]))
        end, right_open = max(bounds, key=lambda p: (eval_expr(p[0]), p[1]))
        return Interval(start.normalize_constant(), end.normalize_constant(), left_open, right_open)

    def inverse(self) -> "Interval":
        """Inverse of an interval."""
        return Interval((1 / self.end).normalize_constant(),
                        (1 / self.start).normalize_constant(),
                        self.right_open, self.left_open)

    def __truediv__(self, other: "Interval") -> "Interval":
        """Quotient in interval arithmetic."""
        return self * other.inverse()

    def __pow__(self, other: "Interval") -> "Interval":
        """Power in interval arithmetic."""
        if eval_expr(other.start) >= 0:
            return Interval(self.start ** other.start, self.end ** other.end,
                            self.left_open or other.left_open,
                            self.right_open or other.right_open)
        elif eval_expr(other.end) <= 0:
            return Interval(self.end ** other.end, self.start ** other.start,
                            self.right_open or other.right_open,
                            self.left_open or other.left_open)
        else:
            raise NotImplementedError

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
        if eval_expr(self.start) < eval_expr(other.start):
            return False
        if eval_expr(self.start) == eval_expr(other.start) and \
            (not self.left_open) and other.left_open:
            return False
        if eval_expr(self.end) > eval_expr(other.end):
            return False
        if eval_expr(self.end) == eval_expr(other.end) and \
            (not self.right_open) and other.right_open:
            return False
        return True

    def sqrt(self) -> "Interval":
        """Square root of interval."""
        return Interval(expr.Fun('sqrt', self.start).normalize_constant(),
                        expr.Fun('sqrt', self.end).normalize_constant(),
                        self.left_open, self.right_open)

    def exp(self) -> "Interval":
        """Exp function of an interval."""
        return Interval(expr.Fun('exp', self.start).normalize_constant(),
                        expr.Fun('exp', self.end).normalize_constant(),
                        self.left_open, self.right_open)

    def log(self) -> "Interval":
        """Log function of an interval."""
        return Interval(expr.Fun('log', self.start).normalize_constant(),
                        expr.Fun('log', self.end).normalize_constant(),
                        self.left_open, self.right_open)

    def sin(self) -> "Interval":
        """Sin function of an interval."""
        if self.contained_in(Interval(-(expr.pi / 2), expr.pi / 2, False, False)):
            return Interval(expr.Fun('sin', self.start).normalize_constant(),
                            expr.Fun('sin', self.end).normalize_constant(),
                            self.left_open, self.right_open)
        elif self.contained_in(Interval(expr.Const(0), expr.pi, False, False)):
            return Interval(expr.Const(0), expr.Const(1), False, False)
        else:
            raise NotImplementedError

    def cos(self) -> "Interval":
        """Cos function of an interval."""
        if self.contained_in(Interval(expr.Const(0), expr.pi, False, False)):
            return Interval(expr.Fun('cos', self.end).normalize_constant(),
                            expr.Fun('cos', self.start).normalize_constant(),
                            self.right_open, self.left_open)
        elif self.contained_in(Interval(-(expr.pi / 2), expr.pi / 2, False, False)):
            return Interval(expr.Const(0), expr.Const(1), False, False)
        else:
            raise NotImplementedError


def get_bounds(e: Expr, var_range: Dict[str, Interval]) -> "Interval":
    """Obtain the range of expression e as a variable.

    e - expr.Expr, an expression.
    var_range - dict(str, Interval): mapping from variables to intervals.

    Returns Interval: an overapproximation of the values of e.

    """
    if e.is_var():
        assert e.name in var_range, "get_bounds: variable %s not found" % e.name
        return var_range[e.name]

    elif e.is_const():
        return Interval.closed(e, e)

    elif e.is_op():
        if e.is_plus():
            return get_bounds(e.args[0], var_range) + get_bounds(e.args[1], var_range)
        elif e.is_uminus():
            return -get_bounds(e.args[0], var_range)
        elif e.is_minus():
            return get_bounds(e.args[0], var_range) - get_bounds(e.args[1], var_range)
        elif e.is_times():
            return get_bounds(e.args[0], var_range) * get_bounds(e.args[1], var_range)
        elif e.is_divides():
            return get_bounds(e.args[0], var_range) / get_bounds(e.args[1], var_range)
        elif e.is_power():
            return get_bounds(e.args[0], var_range) ** get_bounds(e.args[1], var_range)
        else:
            raise NotImplementedError

    elif e.is_fun():
        if e.func_name == 'sqrt':
            return get_bounds(e.args[0], var_range).sqrt()
        elif e.func_name == 'exp':
            return get_bounds(e.args[0], var_range).exp()
        elif e.func_name == 'log':
            return get_bounds(e.args[0], var_range).log()
        elif e.func_name == 'sin':
            return get_bounds(e.args[0], var_range).sin()
        elif e.func_name == 'cos':
            return get_bounds(e.args[0], var_range).cos()
        else:
            raise NotImplementedError

    else:
        raise NotImplementedError
