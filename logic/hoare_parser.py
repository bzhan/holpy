# Author: Bohua Zhan

from lark import Lark, Transformer, v_args, exceptions

from kernel.type import TFun
from kernel.term import Term, Var
from logic import logic
from logic import nat
from logic import hoare

"""Parsing for simple imperative programs."""

grammar = r"""
    ?expr: CNAME -> var_expr
        | INT -> num_expr
        | expr "+" expr -> plus_expr

    ?cond: expr "==" expr -> eq_cond
        | expr "!=" expr -> ineq_cond

    ?cmd: "skip" -> skip_cmd
        | CNAME ":=" expr -> assign_cmd
        | "if" "(" cond ")" "then" cmd "else" cmd -> if_cmd
        | "while" "(" cond ")" "{" cmd "}" -> while_cmd
        | cmd ";" cmd -> seq_cmd

    %import common.CNAME
    %import common.WS
    %import common.INT

    %ignore WS
"""

natFun = TFun(nat.natT, nat.natT)
st = Var("s", natFun)

def str_to_nat(s):
    """Convert string to natural number."""
    return ord(s) - ord("a")

@v_args(inline=True)
class HoareTransformer(Transformer):
    def __init__(self):
        pass

    def var_expr(self, s):
        return st(nat.to_binary(str_to_nat(s)))

    def num_expr(self, n):
        return nat.to_binary(int(n))

    def plus_expr(self, e1, e2):
        return nat.plus(e1, e2)

    def eq_cond(self, e1, e2):
        return Term.mk_equals(e1, e2)

    def ineq_cond(self, e1, e2):
        return logic.neg(Term.mk_equals(e1, e2))

    def skip_cmd(self):
        return hoare.Skip(natFun)

    def assign_cmd(self, v, e):
        Assign = hoare.Assign(nat.natT, nat.natT)
        return Assign(nat.to_binary(str_to_nat(v)), Term.mk_abs(st, e))

    def if_cmd(self, b, c1, c2):
        Cond = hoare.Cond(natFun)
        return Cond(Term.mk_abs(st, b), c1, c2)

    def while_cmd(self, b, c):
        While = hoare.While(natFun)
        return While(Term.mk_abs(st, b), Term.mk_abs(st, logic.true), c)

    def seq_cmd(self, c1, c2):
        Seq = hoare.Seq(natFun)
        return Seq(c1, c2)

hoare_parser = Lark(grammar, start="cmd", parser="lalr", transformer=HoareTransformer())

def parse_hoare(s):
    return hoare_parser.parse(s)
