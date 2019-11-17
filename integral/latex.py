"""Conversion from expressions to latex."""

from decimal import Decimal
from fractions import Fraction

from integral import expr

def convert_expr(e, mode="large"):
    if e.ty == expr.VAR:
        return e.name
    elif e.ty == expr.CONST:
        if isinstance(e.val, (int, Decimal)):
            return str(e.val)
        elif isinstance(e.val, Fraction):
            if mode == 'large':
                return "\\frac{%d}{%d}" % (e.val.numerator, e.val.denominator)
            else:
                return "%d/%d" % (e.val.numerator, e.val.denominator)
        else:
            raise NotImplementedError
    elif e.ty == expr.OP:
        if len(e.args) == 1:
            a, = e.args
            sa = convert_expr(a, mode)
            if a.priority() < 80:
                sa = "(%s)" % sa
            return "%s%s" % (e.op, sa)
        elif len(e.args) == 2:
            x, y = e.args
            sx = convert_expr(x, mode)
            sy = convert_expr(y, mode)
            if e.op in ("+", "-", "^"):
                if x.priority() < expr.op_priority[e.op]:
                    sx = "(%s)" % sx
                if y.priority() < expr.op_priority[e.op]:
                    sy = "(%s)" % sy
                if e.op == "^" and len(sy) > 1:
                    sy = "{%s}" % sy
                return "%s %s %s" % (sx, e.op, sy)
            elif e.op == "*":
                return "%s %s" % (sx, sy)
            elif e.op == "/":
                if mode == 'large':
                    return "\\frac{%s}{%s}" % (sx, sy)
                else:
                    return "%s/%s" % (sx, sy)
            else:
                raise NotImplementedError
        else:
            raise NotImplementedError
    elif e.ty == expr.FUN:
        if len(e.args) == 0:
            return "\\%s" % e.func_name
        elif len(e.args) == 1:
            x, = e.args
            sx = convert_expr(x, mode)
            if len(sx) > 1:
                sx = "(%s)" % sx
            return "\\%s{%s}" % (e.func_name, sx)
        else:
            raise NotImplementedError
    elif e.ty == expr.INTEGRAL:
        lower = convert_expr(e.lower, mode='short')
        upper = convert_expr(e.upper, mode='short')
        body = convert_expr(e.body, mode)
        return "\\int_{%s}^{%s} %s \\,\\mathrm{d%s}" % (lower, upper, body, e.var)
    elif e.ty == expr.EVAL_AT:
        lower = convert_expr(e.lower, mode='short')
        upper = convert_expr(e.upper, mode='short')
        body = convert_expr(e.body, mode)
        return "\\left. %s \\right\\vert_{%s=%s}^{%s}" % (body, e.var, lower, upper)
    else:
        raise NotImplementedError
