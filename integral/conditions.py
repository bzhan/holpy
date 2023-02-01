"""Conditions"""

from typing import Optional, Dict

from integral import expr
from integral.expr import Expr
from integral import latex
from integral import interval
from integral.interval import Interval


class Conditions:
    """A condition is represented by a list of boolean expressions."""
    def __init__(self, conds=None):
        self.data = list()
        if conds is not None:
            self.data.extend(conds)

    def __str__(self):
        return ", ".join(str(cond) for cond in self.data)

    def add_condition(self, cond: Expr):
        assert isinstance(cond, Expr)
        self.data.append(cond)

    def __eq__(self, other):
        return isinstance(other, Conditions) and self.data == other.data

    def export(self):
        res = list()
        for cond in self.data:
            res.append({
                "cond": str(cond),
                "latex_cond": latex.convert_expr(cond)
            })
        return res

    def get_bounds(self) -> Dict[Expr, Interval]:
        """Convert conditions into a dictionary from variables to intervals."""
        bounds: Dict[Expr, Interval] = dict()
        for cond in self.data:
            res = Interval.from_condition(cond)
            if res:
                x, interval = res
                if x in bounds:
                    bounds[x] = bounds[x].intersection(interval)
                else:
                    bounds[x] = interval
        return bounds

    def get_bounds_for_expr(self, e: Expr) -> Optional[Interval]:
        bounds = self.get_bounds()
        return interval.get_bounds_for_expr(e, bounds)

    def is_positive(self, e: Expr) -> bool:
        """Return whether conditions imply e is positive."""
        interval = self.get_bounds_for_expr(e)
        if interval is None:
            return False
        else:
            return interval.contained_in(Interval.open(expr.Const(0), expr.POS_INF))
    
    def is_not_negative(self, e: Expr) -> bool:
        """Return whether conditions imply e is not negative."""
        interval = self.get_bounds_for_expr(e)
        if interval is None:
            return False
        else:
            return interval.contained_in(Interval.ropen(expr.Const(0), expr.POS_INF))

    def is_negative(self, e: Expr) -> bool:
        """Return whether conditions imply e is negative."""
        interval = self.get_bounds_for_expr(e)
        if interval is None:
            return False
        else:
            return interval.contained_in(Interval.open(expr.NEG_INF, expr.Const(0)))

    def is_not_positive(self, e: Expr) -> bool:
        """Return whether conditions imply e is not positive."""
        interval = self.get_bounds_for_expr(e)
        if interval is None:
            return False
        else:
            return interval.contained_in(Interval.lopen(expr.NEG_INF, expr.Const(0)))
