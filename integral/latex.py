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
                    elif isinstance(x, expr.Fun) and len(x.args) > 0:
                        return "\%s^{%s}%s" % (x.func_name, sy, x.args[0])
                elif e.op in ("+", "-"):
                    if y.ty == expr.CONST:
                        if y.val < 0:
                            new_y = expr.Const(0 - y.val)
                            return "%s %s %s" % (sx, "-", convert_expr(new_y))
                    if y.ty == expr.OP:
                        y1, y2 = y.args
                        if isinstance(y1, expr.Const):
                            new_y = y
                            if y1.val < 0:
                                new_y = expr.Op(y.op, expr.Const(0 - y1.val), y2)                            
                                if y.op == "*":
                                    if y1.val == -1:
                                        new_y = y2
                                sy = convert_expr(new_y, mode)
                                new_op = "-" if e.op == "+" else "+"
                                return "%s %s %s" % (sx, new_op, sy)                    
                if x.priority() < expr.op_priority[e.op]:
                    sx = "(%s)" % sx
                if y.priority() < expr.op_priority[e.op]:
                    sy = "(%s)" % sy
                if e.op == "^" and len(sy) > 1:
                    sy = "{%s}" % sy
                return "%s %s %s" % (sx, e.op, sy)
            elif e.op == "*":
                if not x.is_constant() and not y.is_constant():
                    if x.ty == expr.OP and x.op != "^":
                        sx = "(" + sx + ")"
                    if y.ty == expr.OP and y.op != "^":
                        sy = "(" + sy + ")"
                    return "%s %s" % (sx, sy)
                if x.ty == expr.CONST and y.ty == expr.VAR:
                    if sx == "1":
                        return "%s" % sy
                    return "%s %s" % (sx, sy)
                elif x.ty == expr.CONST and y.ty == expr.OP:
                    if y.op == "^" and y.args[0].ty == expr.VAR:
                        if sx == "1":
                            return "%s" % sy
                    return "%s %s %s" % (sx, e.op, sy)
                elif x.ty == expr.CONST and y.ty == expr.FUN:
                    if sx == "1":
                        return "%s" % sy
                    return "%s %s" % (sx, sy)
                elif x.ty == expr.CONST and x.val == -1:
                    return "-%s" % sy
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
            if len(sx) > 1:
                sx = "(%s)" % sx
            if e.func_name == "exp":
                if e.args[0] == expr.Const(1):
                    return "\\%s" % e.func_name
                else:
                    return "e^{%s}" % sx
            elif e.func_name == "sqrt":
                return "\\sqrt{%s}" % sx
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
