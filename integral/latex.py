"""Conversion from expressions to latex."""

from decimal import Decimal
from fractions import Fraction
from integral import expr
from integral.expr import EVAL_AT, OP, CONST, FUN, Const, Op


def convert_expr(e: expr.Expr, mode: str = "large") -> str:
    if e.is_var():
        return e.name
    elif e.is_const():
        if isinstance(e.val, (int, Decimal)):
            if e.val == Decimal("inf"):
                return "\\infty"
            elif e.val == Decimal("-inf"):
                return "-\\infty"
            else:
                return str(e.val)
        elif isinstance(e.val, Fraction):
            if e.val.denominator == 1:
                return "%d" % e.val.numerator
            elif mode == 'large':
                if e.val.numerator > 0:
                    return "\\frac{%d}{%d}" % (e.val.numerator, e.val.denominator)
                elif e.val.numerator < 0:
                    return "-\\frac{%d}{%d}" % (-e.val.numerator, e.val.denominator)
            else:
                return "%d/%d" % (e.val.numerator, e.val.denominator)
        else:
            raise NotImplementedError
    elif e.is_inf():
        if e == expr.POS_INF:
            return "\\infty"
        else:
            return "-\\infty"
    elif e.is_op():
        if len(e.args) == 1:
            a, = e.args
            sa = convert_expr(a, mode)
            if a.priority() < 70:
                sa = "(%s)" % sa
            return "%s%s" % (e.op, sa)
        elif len(e.args) == 2:
            x, y = e.args
            sx = convert_expr(x, mode)
            sy = convert_expr(y, mode)
            if e.op == '^':
                if y.ty == expr.CONST and isinstance(y.val, Fraction) and y.val.numerator == 1:
                    # Square root and other root cases
                    if y.val.denominator == 2:
                        return "\\sqrt{%s}" % sx
                    else:
                        return "\\sqrt[%s]{%s}" % (y.val.denominator, sx)
                elif isinstance(x, expr.Fun) and len(x.args) > 0 and x.func_name != "abs" \
                        and x.func_name in ('log', 'cos', 'sin', 'tan', 'sec', 'csc', 'cot'):
                    # If base is logarithmic or trigonometric function, use special format
                    sy = convert_expr(y, mode="short")
                    return "\%s^{%s}(%s)" % (x.func_name, sy, convert_expr(x.args[0]))
                elif isinstance(x, expr.Fun) and len(x.args) > 0 and \
                        x.func_name not in ("abs", "factorial", "sqrt"):
                    sy = convert_expr(y, mode="short")
                    return "%s^{%s}(%s)" % (x.func_name, sy, convert_expr(x.args[0]))
                elif isinstance(x, expr.Const) and x.val<0:
                    return "(%s)^{%s}" % (sx,sy)
                elif isinstance(x, expr.Fun) and x.func_name == 'factorial':
                    return "(%s)^{%s}" % (sx,sy)
                else:
                    # Ordinary cases
                    sy = convert_expr(y, mode="short")
                    if x.priority() <= e.priority():
                        sx = "(%s)" % sx
                    sy = "{%s}" % sy
                    return "%s %s %s" % (sx, e.op, sy)
            elif e.op == '+' or e.op == '-':
                # Ordinary cases
                if x.priority() < e.priority():
                    sx = "(%s)" % sx
                if y.priority() <= e.priority():
                    sy = "(%s)" % sy
                return "%s %s %s" % (sx, e.op, sy)
            elif e.op == "*":
                if x.priority() < e.priority():
                    sx = "(%s)" % sx
                if y.priority() <= e.priority():
                    sy = "(%s)" % sy
                if mode == 'short' and x.is_const() and isinstance(x.val, Fraction) and \
                    x.val.denominator != 1:
                    # If left side is a fraction, add dot to reduce ambiguity
                    return "%s\\cdot %s" % (sx, sy)
                elif x.is_constant() and y.is_constant():
                    if not y.is_const():
                        return "%s %s"%(sx, sy)
                    # 2*1 = 2· 1
                    return "%s\\cdot %s" % (sx, sy)
                elif y.is_constant() and not x.is_constant():
                    # (m/2) * 2 = m/2 · 2
                    return "%s\\cdot %s" % (sx, sy)
                else:
                    return "%s %s" % (sx, sy)
            elif e.op == "/":
                if mode == 'large':
                    return "\\frac{%s}{%s}" % (sx, sy)
                else:
                    if x.priority() < e.priority():
                        sx = "(%s)" % sx
                    if y.priority() <= e.priority():
                        sy = "(%s)" % sy
                    return "%s/%s" % (sx, sy)
            elif e.op in ("=", "<", ">"):
                return "%s %s %s" % (sx, e.op, sy)
            elif e.op == '<=':
                return "%s \\le %s" % (sx, sy)
            elif e.op == ">=":
                return "%s \\ge %s" % (sx, sy)
            elif e.op == "!=":
                return "%s \\neq %s" % (sx, sy)
            else:
                raise NotImplementedError
        else:
            raise NotImplementedError
    elif e.is_fun():
        if len(e.args) == 0:
            return "\\%s" % e.func_name
        elif len(e.args) == 1:
            x, = e.args
            sx = convert_expr(x, mode)
            if e.func_name == "exp":
                if e.args[0] == expr.Const(1):
                    return "e"
                else:
                    sx = convert_expr(x, mode="short")
                    return "e^{%s}" % sx
            elif e.func_name == "sqrt":
                return "\\sqrt{%s}" % sx
            elif e.func_name == "abs":
                return "\\left| %s \\right|" % sx
            elif e.func_name == "atan":
                return "\\arctan{(%s)}" % sx
            elif e.func_name == "asin":
                return "\\arcsin{(%s)}" % sx
            elif e.func_name == "acos":
                return "\\arccos{(%s)}" % sx
            elif e.func_name in ('log', 'sin', 'cos', 'tan', 'cot', 'csc', 'sec'):
                return "\\%s{(%s)}" % (e.func_name, sx)
            elif e.func_name == 'factorial':
                if x.is_var():
                    return "%s!" % sx
                else:
                    return "(%s)!" % sx
            elif e.func_name == 'Gamma':
                return "\\Gamma{(%s)}" % sx
            else:
                return "%s{(%s)}" % (e.func_name, sx)
        elif len(e.args) == 2:
            x, y = e.args
            sx, sy = convert_expr(x, mode), convert_expr(y, mode)
            if e.func_name == "binom":
                return "\\binom{%s}{%s}" % (sx, sy)
            else:
                return "%s(%s,%s)" % (e.func_name, sx, sy)
        else:
            raise NotImplementedError
    elif e.is_integral():
        lower = convert_expr(e.lower, mode='short')
        upper = convert_expr(e.upper, mode='short')
        body = convert_expr(e.body, mode)
        return "\\int_{%s}^{%s} %s \\,d%s" % (lower, upper, body, e.var)
    elif e.is_evalat():
        lower = convert_expr(e.lower, mode='short')
        upper = convert_expr(e.upper, mode='short')
        body = convert_expr(e.body, mode)
        return "\\left. %s \\right\\vert_{%s=%s}^{%s}" % (body, e.var, lower, upper)
    elif e.is_limit():
        lim = convert_expr(e.lim, mode="short")
        body = convert_expr(e.body, mode)
        if e.body.ty == expr.OP and len(e.body.args) > 1:
            return "\\lim\\limits_{%s\\to %s} (\,%s\,)" % (e.var, lim, body)
        else:
            return "\\lim\\limits_{%s\\to %s} %s" % (e.var, lim, body)
    elif e.is_deriv():
        if e.body.ty == expr.OP and e.body.op in ('+', '-'):
            return "\\frac{d}{d%s} (%s)" % (e.var, convert_expr(e.body, mode))
        else:
            return "\\frac{d}{d%s} %s" % (e.var, convert_expr(e.body, mode))
    elif e.is_indefinite_integral():
        body = convert_expr(e.body, mode)
        return "\\int %s \\,d%s" % (body, e.var)
    elif e.is_skolem_func():
        if not e.dependent_vars:
            return e.name
        else:
            return e.name+'('+', '.join([str(arg) for arg in list(e.dependent_vars)])+')'
        return "%s" % str(e)
    elif e.is_summation():
        lower = convert_expr(e.lower, mode)
        upper = convert_expr(e.upper, mode)
        body = convert_expr(e.body, mode)
        return "\\sum_{%s=%s}^{%s}{%s}" % (e.index_var, lower, upper, body)
    else:
        raise NotImplementedError
