# Author: Bohua Zhan

"""Parsing imperative programs into Com objects."""

import os, json
from lark import Lark, Transformer, v_args, exceptions

from kernel.type import TFun, BoolType
from kernel.term import Term, Var, Const, Abs, true
from logic import logic
from logic import basic
from imperative import expr
from imperative import com


grammar = r"""
    ?expr: CNAME -> var_expr
        | expr "." CNAME -> field_expr
        | expr "[" expr "]" -> array_expr
        | INT -> num_expr
        | expr "+" expr -> plus_expr
        | "-" expr -> uminus_expr
        | expr "-" expr -> minus_expr
        | expr "*" expr -> times_expr
        | CNAME "(" expr ("," expr)* ")" -> fun_expr
        | "(" expr ")"

    ?atom_cond: expr "==" expr -> eq_cond
        | expr "!=" expr -> ineq_cond
        | expr "<=" expr -> less_eq_cond
        | expr "<" expr -> less_cond
        | "true" -> true_cond
        | "if" cond "then" cond "else" cond -> if_cond
        | "forall" CNAME "." cond -> forall_cond
        | "(" cond ")"

    ?neg: "~" atom_cond -> neg | atom_cond  // Negation: priority 40
    
    ?conj: neg "&" conj | neg     // Conjunction: priority 35

    ?disj: conj "|" disj | conj   // Disjunction: priority 30

    ?imp: disj "-->" imp | disj  // Implies: priority 25

    ?cond: imp

    ?cmd: "skip" -> skip_cmd
        | CNAME ":=" expr -> assign_cmd
        | "if" "(" cond ")" "then" cmd "else" cmd -> if_cmd
        | "while" "(" cond ")" "{" cmd "}" -> while_cmd
        | "while" "(" cond ")" "{" "[" cond "]" cmd "}" -> while_cmd_inv
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
        return expr.Var(str(s))

    def field_expr(self, ident, fieldname):
        return expr.Field(ident, fieldname)

    def array_expr(self, ident, idx):
        return expr.ArrayElt(ident, idx)

    def num_expr(self, n):
        return expr.Const(int(n))

    def plus_expr(self, e1, e2):
        return expr.Op("+", e1, e2)

    def uminus_expr(self, e):
        return expr.Op("-", e)

    def minus_expr(self, e1, e2):
        return expr.Op("-", e1, e2)

    def times_expr(self, e1, e2):
        return expr.Op("*", e1, e2)

    def fun_expr(self, fname, *args):
        assert fname in expr.global_fnames, "Function %s not found" % fname
        return expr.Fun(fname, *args)

    def eq_cond(self, e1, e2):
        return expr.Op("==", e1, e2)

    def ineq_cond(self, e1, e2):
        return expr.Op("!=", e1, e2)

    def if_cond(self, cond, e1, e2):
        return expr.ITE(cond, e1, e2)

    def conj(self, b1, b2):
        return expr.Op("&", b1, b2)

    def disj(self, b1, b2):
        return expr.Op("|", b1, b2)

    def imp(self, b1, b2):
        return expr.Op("-->", b1, b2)

    def neg(self, b):
        return expr.Op("~", b)

    def true_cond(self):
        return expr.Const(True)

    def less_eq_cond(self, e1, e2):
        return expr.Op("<=", e1, e2)

    def less_cond(self, e1, e2):
        return expr.Op("<", e1, e2)

    def forall_cond(self, var_name, body):
        return expr.Forall(expr.Var(var_name), body)

    def skip_cmd(self):
        return com.Skip()

    def assign_cmd(self, v, e):
        return com.Assign(expr.Var(str(v)), e)

    def if_cmd(self, b, c1, c2):
        return com.Cond(b, c1, c2)

    def while_cmd(self, b, c):
        return com.While(b, true, c)

    def while_cmd_inv(self, b, inv, c):
        return com.While(b, inv, c)

    def seq_cmd(self, c1, c2):
        return com.Seq(c1, c2)

cond_parser = Lark(grammar, start="cond", parser="lalr", transformer=HoareTransformer())
com_parser = Lark(grammar, start="cmd", parser="lalr", transformer=HoareTransformer())

def process_file(input):
    basic.load_theory('hoare')

    dn = os.path.dirname(os.path.realpath(__file__))
    with open(os.path.join(dn, 'examples/' + input + '.json'), encoding='utf-8') as a:
        data = json.load(a)

    content = data['content']

    for run in content:
        if run['ty'] == 'vcg':
            c = com_parser.parse(run['com'])
            pre = cond_parser.parse(run['pre'])
            post = cond_parser.parse(run['post'])
            c.pre = [pre]
            c.compute_wp(post)
