"""Conversion from expressions to latex."""

from decimal import Decimal
from fractions import Fraction
from integral import expr
from integral.expr import EVAL_AT, OP, CONST, FUN, Const, Op


def convert_expr(e, mode="large"):
    if e.ty == expr.VAR:
        return e.name
    elif e.ty == expr.CONST:
        if isinstance(e.val, (int, Decimal)):
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
            if e.op in ("+", "-", "^"):
                if e.op == "^":
                    # Still can improve 
                    if y.ty == expr.CONST and isinstance(y.val, Fraction):
                        if y.val.numerator == 1:
                            if y.val.denominator == 2:
                                return "\\sqrt{%s}" % sx
                            else:
                                return "\\sqrt[%s]{%s}" % (y.val.denominator, sx)
                        if x.ty == OP:
                            return "(%s) ^ {%s}" % (sx, sy)
                        return "%s ^ {%s}" % (sx, sy)
                    if y.ty == expr.CONST and y.val < 0:
                        if y.val != -1:
                            new_expr = expr.Op("/", expr.Const(1), expr.Op("^", x, expr.Const(-y.val)))
                        else:
                            new_expr = expr.Op("/", expr.Const(1), x)
                        return convert_expr(new_expr)
                    elif isinstance(x, expr.Fun) and len(x.args) > 0 and x.func_name != "abs":
                        return "\%s^{%s}(%s)" % (x.func_name, sy, convert_expr(x.args[0]))                    
                if x.priority() < expr.op_priority[e.op]:
                    sx = "(%s)" % sx
                if y.priority() < expr.op_priority[e.op]:
                    sy = "{(%s)}" % sy
                if e.op == "^" and len(sy) > 1:
                    sy = "{%s}" % sy
                if y.ty == expr.OP and y.op == e.op and y.op in ("-", "/"):
                    sy = "{(%s)}" % sy
                return "%s %s %s" % (sx, e.op, sy)
            elif e.op == "*":
                if not x.is_constant() and not y.is_constant() and not (y.ty == OP and y.op == "^" and y.args[1].ty == CONST and y.args[1].val < 0) or x == expr.Fun("pi") or y == expr.Fun("pi"):
                    if x.ty == expr.OP and (x.op not in ("^", "*")) and not len(x.args) == 1:
                        sx = "(" + sx + ")"
                    if y.ty == expr.OP and y.op != "^":
                        sy = "(" + sy + ")"
                    return "%s %s" % (sx, sy)
                elif x.is_constant() and y.is_constant() and y.ty != CONST and not (y.ty == OP and y.op in ("+", "-") or y.ty == CONST and isinstance(y.val, Fraction)):
                    if x == Const(-1):
                        return "-%s" % sy
                    if x.ty == expr.OP and x.op != "^" and len(x.args) != 1:
                        sx = "(" + sx + ")"
                    if y.ty == expr.OP and not (len(y.args) == 2 and y.op == "^" or y.args[1].ty == CONST and y.args[1].val == Fraction(1/2)):
                        sy = "(" + sy + ")"
                    if x.ty == expr.CONST and isinstance(x.val, Fraction) and mode == "short":
                        sx = "(" + sx + ")"
                    return "%s %s" % (sx, sy)
                elif x.is_constant() and y.ty == CONST and isinstance(y.val, Fraction) and y.val.numerator == 1 and y.val.denominator != 1:
                    return "\\frac{%s}{%s}" % (sx, convert_expr(expr.Const(y.val.denominator)))
                elif y.ty == OP and y.op == "^" and y.args[1].ty == CONST and y.args[1].val < 0:
                    if y.args[1].val == -1:
                        return "\\frac{%s}{%s}" % (sx, convert_expr(y.args[0]))
                    else:
                        new_denom = Op("^", y.args[0], Const(-y.args[1].val))
                        return "\\frac{%s}{%s}" % (sx, convert_expr(new_denom, mode))
                elif x.ty == expr.CONST:
                    if x.val == -1:
                        if y.ty == OP:
                            return "-(%s)" % sy
                        else:
                            return "-%s" % sy
                    elif x.val == 1 and not y.ty == OP:
                        if y.ty == OP:
                            return "(%s)" % sy
                        else:
                            return "%s" % sy
                    elif isinstance(x.val, Fraction) and x.val.numerator == 1 and y.ty not in (expr.INTEGRAL, expr.OP, expr.EVAL_AT):
                        return "\\frac{%s}{%s}" % (sy, convert_expr(expr.Const(x.val.denominator)))
                    elif y.ty in (expr.VAR, expr.FUN):
                        if isinstance(x.val, Fraction):
                            return "(%s) %s" % (sx, sy)
                        else:
                            return "%s %s" % (sx, sy)
                    elif not y.is_constant():
                        if y.ty == OP and y.op != '^':
                            return "%s (%s)" % (sx, sy)
                        elif y.ty == EVAL_AT:
                            return "%s \\times (%s)" % (sx, sy)
                        return "%s %s" % (sx, sy)
                    elif y.ty != CONST and y.is_constant() and not (y.ty == OP and y.op in ('+', '-')):
                        return "%s %s"%(sx, sy)
                    elif y.ty == OP and y.op == "^" and not y.args[0].is_constant():
                        return "%s %s" % (sx, sy)
                    else:
                        if x.priority() < expr.op_priority[e.op]:
                            sx = "(%s)" % sx
                        if y.priority() < expr.op_priority[e.op]:
                            sy = "(%s)" % sy
                        return "%s %s %s" % (sx, e.op, sy)
                else:
                    if x.priority() < expr.op_priority[e.op]:
                        sx = "(%s)" % sx
                    if y.priority() < expr.op_priority[e.op]:
                        sy = "(%s)" % sy
                    return "%s %s %s" % (sx, e.op, sy)
            elif e.op == "/":
                if mode == 'large':
                    if sy == "1":
                        return "%s" % sx
                    elif x.ty == expr.OP:
                        if x.op == "-" and len(x.args) == 1:
                            # (-x) / y => - (x/y)
                            sxx = convert_expr(x.args[0])
                            return "-\\frac{%s}{%s}" % (sxx, sy)
                        elif y.ty == expr.CONST:
                            return "\\frac{1}{%s} \\times %s" % (sy, sx)
                        else:
                            return "\\frac{%s}{%s}" % (sx, sy)
                    else:
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
            if e.func_name == "exp":
                if e.args[0] == expr.Const(1):
                    return "e"
                else:
                    return "e^{%s}" % sx
            elif e.func_name == "sqrt":
                return "\\sqrt{%s}" % sx
            elif e.func_name == "abs":
                return "\\left| %s \\right|" % sx
            elif e.func_name == "atan":
                return "\\arctan{%s}" % sx
            elif e.func_name == "asin":
                return "\\arcsin{%s}" % sx
            elif e.func_name == "acos":
                return "\\arccos{%s}" % sx
            return "\\%s{(%s)}" % (e.func_name, sx)
        else:
            raise NotImplementedError
    elif e.ty == expr.INTEGRAL:
        lower = convert_expr(e.lower, mode='short')
        upper = convert_expr(e.upper, mode='short')
        body = convert_expr(e.body, mode)
        return "\\int_{%s}^{%s} %s \\,\\mathit{d%s}" % (lower, upper, body, e.var)
    elif e.ty == expr.EVAL_AT:
        lower = convert_expr(e.lower, mode='short')
        upper = convert_expr(e.upper, mode='short')
        body = convert_expr(e.body, mode)
        return "\\left. %s \\right\\vert_{%s=%s}^{%s}" % (body, e.var, lower, upper)
    else:
        raise NotImplementedError
