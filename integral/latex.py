"""Conversion from expressions to latex."""

from decimal import Decimal
from fractions import Fraction

from integral import expr

def convert_expr(e):
    if e.ty == expr.VAR:
        return e.name
    elif e.ty == expr.CONST:
        if isinstance(e.val, (int, Decimal)):
            return str(e.val)
        elif isinstance(e.val, Fraction):
            return "\\frac{%d}{%d}" % (e.val.numerator, e.val.denominator)
        else:
            raise NotImplementedError
    elif e.ty == expr.OP:
        if e.op in ("+", "-", "^") and len(e.args) == 2:
            x, y = e.args
            sx, sy = convert_expr(x), convert_expr(y)
            if x.priority() < expr.op_priority[e.op]:
                sx = "(%s)" % sx
            if y.priority() < expr.op_priority[e.op]:
                sy = "(%s)" % sy
            if e.op == "^" and len(sy) > 1:
                sy = "{%s}" % sy
            return "%s %s %s" % (sx, e.op, sy)
        elif e.op == "*":
            x, y = e.args
            return "%s %s" % (convert_expr(x), convert_expr(y))
        elif e.op == "/":
            x, y = e.args
            return "\\frac{%s}{%s}" % (convert_expr(x), convert_expr(y))
        else:
            raise NotImplementedError
    elif e.ty == expr.FUN:
        if len(e.args) == 1:
            x, = e.args
            sx = convert_expr(x)
            if len(sx) > 1:
                sx = "(%s)" % sx
            return "\\%s{%s}" % (e.func_name, sx)
        else:
            raise NotImplementedError
    elif e.ty == expr.INTEGRAL:
        return "\\int_{%s=%s}^{%s} %s \\,\\mathrm{d%s}" % (
            e.var, convert_expr(e.lower), convert_expr(e.upper), convert_expr(e.body), e.var
        )
    elif e.ty == expr.EVAL_AT:
        return "\\left. %s \\right\\vert_{%s=%s}^{%s}" % (
            convert_expr(e.body), e.var, convert_expr(e.lower), convert_expr(e.upper)
        )
    else:
        raise NotImplementedError
