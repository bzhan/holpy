"""Parsing"""

from lark import Lark, Transformer, v_args, exceptions
from decimal import Decimal

from integral import expr


grammar = r"""
    ?atom: CNAME -> var_expr
        | INT -> int_expr
        | DECIMAL -> decimal_expr
        | "D" CNAME "." expr -> deriv_expr
        | CNAME "(" expr ("," expr)* ")" -> fun_expr
        | "(" expr ")"
        | "INT" CNAME ":[" expr "," expr "]." expr -> integral_expr
        | "[" expr "]_" CNAME "=" expr "," expr -> eval_at_expr

    ?uminus: "-" uminus -> uminus_expr | atom

    ?pow: pow "^" uminus -> pow_expr | uminus

    ?times: times "*" pow -> times_expr
        | times "/" pow -> divides_expr | pow

    ?plus: plus "+" times -> plus_expr
        | plus "-" times -> minus_expr | times

    ?expr: plus

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

    def decimal_expr(self, n):
        return expr.Const(Decimal(n))
        
    def plus_expr(self, a, b):
        return a + b

    def minus_expr(self, a, b):
        return a - b

    def times_expr(self, a, b):
        return a * b

    def divides_expr(self, a, b):
        return a / b

    def pow_expr(self, a, b):
        return a ^ b

    def uminus_expr(self, a):
        if a.ty == expr.CONST:
            return expr.Const(-a.val)
        else:
            return -a

    def fun_expr(self, func_name, *args):
        return expr.Fun(func_name, *args)

    def deriv_expr(self, var, body):
        return expr.Deriv(var, body)

    def integral_expr(self, var, lower, upper, body):
        return expr.Integral(var, lower, upper, body)

    def eval_at_expr(self, body, var, lower, upper):
        return expr.EvalAt(var, lower, upper, body)

expr_parser = Lark(grammar, start="expr", parser="lalr", transformer=ExprTransformer())

def parse_expr(s):
    try:
        return expr_parser.parse(s)
    except (exceptions.UnexpectedCharacters, exceptions.UnexpectedToken) as e:
        print("When parsing:", s)
        raise e
