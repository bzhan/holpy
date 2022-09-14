"""Parsing"""

from lark import Lark, Transformer, v_args, exceptions
from decimal import Decimal
from fractions import Fraction

from integral import expr
from integral.expr import Expr
from integral.inequality import Interval


grammar = r"""
    ?atom: CNAME -> var_expr
        | "-0" -> neg_zero_expr
        | INT -> int_expr
        | DECIMAL -> decimal_expr
        | "D" CNAME "." expr -> deriv_expr
        | "pi" -> pi_expr
        | "inf" -> pos_inf_expr
        | "oo" -> pos_inf_expr
        | "-inf" -> neg_inf_expr
        | "-oo" -> neg_inf_expr
        | CNAME "(" expr ("," expr)* ")" -> fun_expr
        | "(" expr ")"
        | "\|" expr "\|" -> abs_expr 
        | "$" expr "$" -> trig_expr
        | "INT" CNAME ":[" expr "," expr "]." expr -> integral_expr
        | "INT" CNAME "." expr -> indefinite_integral_expr
        | "DIFF" "." expr -> differential_expr
        | "[" expr "]_" CNAME "=" expr "," expr -> eval_at_expr
        | "LIM" "{" CNAME "->" expr "}" "." expr -> limit_inf_expr
        | "LIM" "{" CNAME "->" expr "-}" "."  expr -> limit_l_expr
        | "LIM" "{" CNAME "->" expr "+}" "."  expr -> limit_r_expr

    ?uminus: "-" uminus -> uminus_expr | atom  // priority 80

    ?pow: pow "^" uminus -> pow_expr          // priority 75
        | "-" atom "^" uminus -> uminus_pow_expr
        | uminus

    ?times: times "*" pow -> times_expr        // priority 70
        | times "/" pow -> divides_expr | pow

    ?plus: plus "+" times -> plus_expr         // priority 65
        | plus "-" times -> minus_expr | times

    ?compare: plus "=" plus -> eq_expr              // priority 50
        | plus "!=" plus -> not_eq_expr
        | plus ">" plus -> greater_expr
        | plus "<" plus -> less_expr
        | plus ">=" plus -> greater_eq_expr
        | plus "<=" plus -> less_eq_expr
        | plus

    ?expr: compare

    !interval: ("(" | "[") expr "," expr ("]" | ")") -> interval_expr

    %import common.CNAME
    %import common.WS
    %import common.INT
    %import common.DECIMAL

    %ignore WS
"""

@v_args(inline=True)
class ExprTransformer(Transformer):
    def __init__(self):
        pass

    def var_expr(self, s):
        return expr.Var(str(s))

    def int_expr(self, n):
        return expr.Const(int(n))

    def neg_zero_expr(self):
        return expr.Op("-", expr.Const(0))

    def decimal_expr(self, n):
        return expr.Const(Decimal(n))
        
    def plus_expr(self, a, b):
        return expr.Op("+", a, b)

    def minus_expr(self, a, b):
        return expr.Op("-", a, b)

    def times_expr(self, a, b):
        return expr.Op("*", a, b)

    def divides_expr(self, a, b):
        if a.ty == expr.CONST and b.ty == expr.CONST:
            return expr.Const(Fraction(a.val) / Fraction(b.val))
        else:
            return expr.Op("/", a, b)

    def pow_expr(self, a, b):
        return expr.Op("^", a, b)

    def eq_expr(self, a, b):
        return expr.Op("=", a, b)

    def not_eq_expr(self, a, b):
        return expr.Op("!=", a, b)

    def less_expr(self, a, b):
        return expr.Op("<", a, b)

    def greater_expr(self, a, b):
        return expr.Op(">", a, b)

    def less_eq_expr(self, a, b):
        return expr.Op("<=", a, b)

    def greater_eq_expr(self, a, b):
        return expr.Op(">=", a, b)
    
    def uminus_expr(self, a):
        if a.ty == expr.CONST:
            return expr.Const(-a.val)
        else:
            return expr.Op("-", a)
    
    def uminus_pow_expr(self, a, b):
        return expr.Op("-", expr.Op("^", a, b))

    def pi_expr(self):
        return expr.pi

    def pos_inf_expr(self):
        return expr.Inf(Decimal("inf"))
    def neg_inf_expr(self):
        return expr.Inf(Decimal("-inf"))

    def fun_expr(self, func_name, *args):
        if func_name == 'SKOLEM_CONST':
            return expr.SkolemFunc(str(args[0]))
        elif func_name == 'SKOLEM_FUNC':
            return expr.SkolemFunc(str(args[0].func_name), *[arg for arg in args[0].args])
        return expr.Fun(func_name, *args)

    def abs_expr(self, expr):
        return expr.Abs(expr)

    def deriv_expr(self, var, body):
        return expr.Deriv(var, body)

    def integral_expr(self, var, lower, upper, body):
        return expr.Integral(str(var), lower, upper, body)

    def indefinite_integral_expr(self, var, body):
        return expr.IndefiniteIntegral(str(var), body)

    def eval_at_expr(self, body, var, lower, upper):
        return expr.EvalAt(var, lower, upper, body)
    
    def trig_expr(self, e):
        e.selected = True
        expr.trig_identity = list()
        expr.trig_identity.append(e)
        return e

    def interval_expr(self, l, e1, comma, e2, r):
        return Interval(e1, e2, left_open=(l == '('), right_open=(r == ')'))

    def limit_inf_expr(self, var, lim, body):
        return expr.Limit(str(var), lim, body)

    def limit_l_expr(self, var, lim, body):
        return expr.Limit(str(var), lim, body, "-")

    def limit_r_expr(self, var, lim, body):
        return expr.Limit(str(var), lim, body, "+")

    def differential_expr(self, body):
        return expr.Differential(body)

expr_parser = Lark(grammar, start="expr", parser="lalr", transformer=ExprTransformer())
interval_parser = Lark(grammar, start="interval", parser="lalr", transformer=ExprTransformer())

def parse_expr(s: str) -> Expr:
    """Parse an integral expression."""
    try:
        return expr_parser.parse(s)
    except (exceptions.UnexpectedCharacters, exceptions.UnexpectedToken) as e:
        print("When parsing:", s)
        raise e

def parse_interval(s: str) -> Interval:
    """Parse an interval."""
    try:
        return interval_parser.parse(s)
    except (exceptions.UnexpectedCharacters, exceptions.UnexpectedToken) as e:
        print("When parsing:", s)
        raise e
