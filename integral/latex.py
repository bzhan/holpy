"""Conversion from expressions to latex."""

from decimal import Decimal
from fractions import Fraction
from integral import expr
from integral.expr import EVAL_AT, OP, CONST, FUN, Const, Op


def convert_expr(e: expr.Expr, mode: str = "large") -> str:
    if e.ty == expr.VAR:
        return e.name
    elif e.ty == expr.CONST:
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
    elif e.ty == expr.INF:
        if e == expr.POS_INF:
            return "\\infty"
        else:
            return "-\\infty"
    elif e.ty == expr.OP:
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
                        and x.func_name in ('cos', 'sin', 'tan', 'sec', 'csc', 'cot'):
                    # If base is a trigonometric function, use special format
                    sy = convert_expr(y, mode="short")
                    return "\%s^{%s}(%s)" % (x.func_name, sy, convert_expr(x.args[0]))
                elif isinstance(x, expr.Fun) and len(x.args) > 0 and x.func_name != "abs":
                    sy = convert_expr(y, mode="short")
                    return "%s^{%s}(%s)" % (x.func_name, sy, convert_expr(x.args[0]))
                elif isinstance(x, expr.Const) and x.val<0:
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
                # if not x.is_constant() and not y.is_constant() and not (y.ty == OP and y.op == "^" and y.args[1].ty == CONST and y.args[1].val < 0) or x == expr.Fun("pi") or y == expr.Fun("pi"):
                #     if x.ty == expr.OP and (x.op not in ("^", "*")) and not len(x.args) == 1:
                #         sx = "(" + sx + ")"
                #     if y.ty == expr.OP and y.op != "^":
                #         sy = "(" + sy + ")"
                #     return "%s %s" % (sx, sy)
                # elif x.is_constant() and y.is_constant() and y.ty != CONST and not (y.ty == OP and y.op in ("+", "-") or y.ty == CONST and isinstance(y.val, Fraction)):
                #     if x == Const(-1):
                #         return "-%s" % sy
                #     if x.ty == expr.OP and x.op != "^" and len(x.args) != 1:
                #         sx = "(" + sx + ")"
                #     if y.ty == expr.OP and not (len(y.args) == 2 and y.op == "^" or y.args[1].ty == CONST and y.args[1].val == Fraction(1/2)):
                #         sy = "(" + sy + ")"
                #     if x.ty == expr.CONST and isinstance(x.val, Fraction) and mode == "short":
                #         sx = "(" + sx + ")"
                #     return "%s %s" % (sx, sy)
                # elif x.ty == expr.CONST:
                #     if x.val == -1:
                #         if y.ty == OP:
                #             return "-(%s)" % sy
                #         else:
                #             return "-%s" % sy
                #     elif x.val == 1 and not y.ty == OP:
                #         if y.ty == OP:
                #             return "(%s)" % sy
                #         else:
                #             return "%s" % sy
                #     elif isinstance(x.val, Fraction) and x.val.numerator == 1 and y.ty not in (expr.INTEGRAL, expr.OP, expr.EVAL_AT):
                #         return "\\frac{%s}{%s}" % (sy, convert_expr(expr.Const(x.val.denominator)))
                #     elif y.ty in (expr.VAR, expr.FUN):
                #         if isinstance(x.val, Fraction):
                #             return "(%s) %s" % (sx, sy)
                #         else:
                #             return "%s %s" % (sx, sy)
                #     elif not y.is_constant():
                #         if y.ty == OP and y.op != '^':
                #             return "%s (%s)" % (sx, sy)
                #         elif y.ty == EVAL_AT:
                #             return "%s \\times (%s)" % (sx, sy)
                #         return "%s %s" % (sx, sy)
                #     elif y.ty != CONST and y.is_constant() and not (y.ty == OP and y.op in ('+', '-')):
                #         return "%s %s"%(sx, sy)
                #     elif y.ty == OP and y.op == "^" and not y.args[0].is_constant():
                #         return "%s %s" % (sx, sy)
                #     else:
                #         if x.priority() < expr.op_priority[e.op]:
                #             sx = "(%s)" % sx
                #         if y.priority() < expr.op_priority[e.op]:
                #             sy = "(%s)" % sy
                #         return "%s %s %s" % (sx, e.op, sy)
                # else:
                #     if x.priority() < expr.op_priority[e.op]:
                #         sx = "(%s)" % sx
                #     if y.priority() < expr.op_priority[e.op]:
                #         sy = "(%s)" % sy
                #     return "%s %s %s" % (sx, e.op, sy)
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
    elif e.ty == expr.FUN:
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
            elif e.func_name == 'is_const':
                return "%s \\ is \\  a \\  const \\  expression" % str(e.args[0])
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
    elif e.ty == expr.INTEGRAL:
        lower = convert_expr(e.lower, mode='short')
        upper = convert_expr(e.upper, mode='short')
        body = convert_expr(e.body, mode)
        return "\\int_{%s}^{%s} %s \\,d%s" % (lower, upper, body, e.var)
    elif e.ty == expr.EVAL_AT:
        lower = convert_expr(e.lower, mode='short')
        upper = convert_expr(e.upper, mode='short')
        body = convert_expr(e.body, mode)
        return "\\left. %s \\right\\vert_{%s=%s}^{%s}" % (body, e.var, lower, upper)
    elif e.ty == expr.LIMIT:
        lim = convert_expr(e.lim, mode="short")
        body = convert_expr(e.body, mode)
        if e.body.ty == expr.OP and len(e.body.args) > 1:
            return "\\lim\\limits_{%s\\to %s} (\,%s\,)" % (e.var, lim, body)
        else:
            return "\\lim\\limits_{%s\\to %s} %s" % (e.var, lim, body)
    elif e.ty == expr.DERIV:
        if e.body.ty == expr.OP and e.body.op in ('+', '-'):
            return "\\frac{d}{d%s} (%s)" % (e.var, convert_expr(e.body, mode))
        else:
            return "\\frac{d}{d%s} %s" % (e.var, convert_expr(e.body, mode))
    elif e.ty == expr.INDEFINITEINTEGRAL:
        body = convert_expr(e.body, mode)
        return "\\int %s \\,d%s" % (body, e.var)
    elif e.ty == expr.SKOLEMFUNC:
        if e.dependent_vars == set():
            return e.name
        else:
            return e.name+'('+', '.join([str(arg) for arg in list(e.dependent_vars)])+')'
        return "%s" % str(e)
    elif e.ty == expr.SUMMATION:
        lower = convert_expr(e.lower, mode)
        upper = convert_expr(e.upper, mode)
        body = convert_expr(e.body, mode)
        return "\\sum_{%s=%s}^{%s}{%s}" % (e.index_var, lower, upper, body)
    else:
        raise NotImplementedError
