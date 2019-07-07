# Author: Bohua Zhan

"""Parsing imperative programs into Com objects."""

from lark import Lark, Transformer, v_args, exceptions

from kernel.type import TFun
from kernel.term import Term, Var
from logic import logic
from data import int as hol_int
from imperative import com


grammar = r"""
    ?expr: CNAME -> var_expr
        | INT -> num_expr
        | expr "+" expr -> plus_expr
        | expr "-" expr -> minus_expr
        | expr "*" expr -> times_expr

    ?cond: expr "==" expr -> eq_cond
        | expr "!=" expr -> ineq_cond
        | expr "<=" expr -> less_eq_cond
        | expr "<" expr -> less_cond
        | cond "&" cond -> conj_cond
        | cond "|" cond -> disj_cond
        | cond "-->" cond -> imp_cond
        | "true" -> true_cond

    ?cmd: "skip" -> skip_cmd
        | CNAME ":=" expr -> assign_cmd
        | "if" "(" cond ")" "then" cmd "else" cmd -> if_cmd
        | "while" "(" cond ")" "{" cmd "}" -> while_cmd
        | "while" "(" cond ")" "[" cond "]" "{" cmd "}" -> while_cmd_inv
        | cmd ";" cmd -> seq_cmd

    %import common.CNAME
    %import common.WS
    %import common.INT

    %ignore WS
"""

@v_args(inline=True)
class HoareTransformer(Transformer):
    def __init__(self):
        pass

    def var_expr(self, s):
        return Var(s, hol_int.intT)

    def num_expr(self, n):
        return hol_int.to_binary_int(int(n))

    def plus_expr(self, e1, e2):
        return hol_int.plus(e1, e2)

    def minus_expr(self, e1, e2):
        return hol_int.minus(e1, e2)

    def times_expr(self, e1, e2):
        return hol_int.times(e1, e2)

    def eq_cond(self, e1, e2):
        return Term.mk_equals(e1, e2)

    def ineq_cond(self, e1, e2):
        return logic.neg(Term.mk_equals(e1, e2))

    def conj_cond(self, b1, b2):
        return logic.conj(b1, b2)

    def disj_cond(self, b1, b2):
        return logic.disj(b1, b2)

    def imp_cond(self, b1, b2):
        return Term.mk_implies(b1, b2)

    def true_cond(self):
        return logic.true

    def less_eq_cond(self, e1, e2):
        return hol_int.less_eq(e1, e2)

    def less_cond(self, e1, e2):
        return hol_int.less(e1, e2)

    def skip_cmd(self):
        return com.Skip()

    def assign_cmd(self, v, e):
        return com.Assign(v, e)

    def if_cmd(self, b, c1, c2):
        return com.Cond(b, c1, c2)

    def while_cmd(self, b, c):
        return com.While(b, logic.true, c)

    def while_cmd_inv(self, b, inv, c):
        return com.While(b, inv, c)

    def seq_cmd(self, c1, c2):
        return com.Seq(c1, c2)

cond_parser = Lark(grammar, start="cond", parser="lalr", transformer=HoareTransformer())
com_parser = Lark(grammar, start="cmd", parser="lalr", transformer=HoareTransformer())