"""Deciding inequalities."""


from integral import expr


class Interval:
    """Specifies an interval. Each side can be either open or closed."""
    def __init__(self, start, end, left_open, right_open):
        self.start = start
        self.end = end
        self.left_open = left_open
        self.right_open = right_open

    def __str__(self):
        left = '(' if self.left_open else '['
        right = ')' if self.right_open else ']'
        return left + str(self.start) + ', ' + str(self.end) + right

    @staticmethod
    def closed(start, end):
        return Interval(start, end, left_open=False, right_open=False)

    @staticmethod
    def open(start, end):
        return Interval(start, end, left_open=True, right_open=True)

    @staticmethod
    def lopen(start, end):
        return Interval(start, end, left_open=True, right_open=False)

    @staticmethod
    def ropen(start, end):
        return Interval(start, end, left_open=False, right_open=True)

    @staticmethod
    def point(val):
        return Interval.closed(val, val)

    def __add__(self, other):
        """Addition in interval arithmetic."""
        return Interval((self.start + other.start).normalize_constant(),
                        (self.end + other.end).normalize_constant(),
                        self.left_open or other.left_open,
                        self.right_open or other.right_open)

    def __neg__(self):
        """Negation (unitary minus) of an interval."""
        return Interval(-self.end, -self.start, self.right_open, self.left_open)

    def __sub__(self, other):
        """Subtraction in interval arithmetic."""
        return self + (-other)

    def __mul__(self, other):
        """Product in interval arithmetic."""
        raise NotImplementedError


def get_bound(e, var_range):
    """Obtain the range of expression e as a variable.

    e - expr.Expr, an expression.
    var_range - dict(str, Interval): mapping from variables to intervals.

    Returns Interval: an overapproximation of the values of e.

    """
    if e.ty == expr.VAR:
        assert e.name in var_range, "get_bound: variable %s not found" % e.name
        return var_range[e.name]

    elif e.ty == expr.CONST:
        return Interval.closed(e, e)

    elif e.ty == expr.OP:
        if e.is_plus():
            return get_bound(e.args[0], var_range) + get_bound(e.args[1], var_range)
        elif e.is_uminus():
            return -get_bound(e.args[0], var_range)
        elif e.is_minus():
            return get_bound(e.args[0], var_range) - get_bound(e.args[1], var_range)
        elif e.is_times():
            return get_bound(e.args[0], var_range) * get_bound(e.args[1], var_range)
        elif e.is_power():
            raise NotImplementedError