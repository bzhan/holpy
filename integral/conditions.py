"""Conditions"""

from typing import Optional, Dict, List

from integral import expr
from integral.expr import Expr
from integral import latex
from integral import interval
from integral.interval import Interval


class Conditions:
    """A condition is represented by a list of boolean expressions."""
    def __init__(self, conds=None):
        self.data: List[Expr] = list()
        if isinstance(conds, Conditions):
            self.data.extend(conds.data)
        elif conds is not None:
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
        res = interval.get_bounds_for_expr(e, bounds)
        return res
    
    def check_condition(self, cond: Expr) -> bool:
        res = Interval.from_condition(cond)
        if res:
            e, interval = res
            interval2 = self.get_bounds_for_expr(e)
            return interval2.contained_in(interval)
        return False

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

    def is_nonzero(self, e: Expr) -> bool:
        """Return whether conditions imply e is nonzero."""
        from integral.poly import normalize
        if e.is_op():
            if e.is_times():
                return self.is_nonzero(e.args[0]) and self.is_nonzero(e.args[1])
            elif e.is_power():
                if self.is_positive(e.args[0]):
                    return True
        for cond in self.data:
            if cond.is_not_equals():
                if cond.args[0] == e and cond.args[1] == expr.Const(0):
                    return True
                elif normalize(e.replace(cond.args[0], cond.args[1]), self) == expr.Const(0):
                    return True
        if self.is_positive(e):
            return True
        if self.is_negative(e):
            return True
        return False
