# Author: Bohua Zhan

"""Parsing imperative programs into Com objects."""

import os, json
from lark import Lark, Transformer, v_args, exceptions

from kernel.type import TFun
from kernel.term import Term, Var, Const
from logic import logic
from logic import basic
from imperative import imp
from data import int as hol_int
from imperative import com


grammar = r"""
    ?expr: CNAME -> var_expr
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
        return Var(s, hol_int.intT)

    def num_expr(self, n):
        return hol_int.to_binary_int(int(n))

    def plus_expr(self, e1, e2):
        return hol_int.plus(e1, e2)

    def uminus_expr(self, e):
        return hol_int.uminus(e)

    def minus_expr(self, e1, e2):
        return hol_int.minus(e1, e2)

    def times_expr(self, e1, e2):
        return hol_int.times(e1, e2)

    def fun_expr(self, fname, *args):
        T = hol_int.intT
        for arg in args:
            T = TFun(hol_int.intT, T)
        if fname == "abs":
            fname = "int_abs"
        return Const(fname, T)(*args)

    def eq_cond(self, e1, e2):
        return Term.mk_equals(e1, e2)

    def ineq_cond(self, e1, e2):
        return logic.neg(Term.mk_equals(e1, e2))

    def if_cond(self, b, b1, b2):
        return logic.mk_if(b, b1, b2)

    def conj(self, b1, b2):
        return logic.conj(b1, b2)

    def disj(self, b1, b2):
        return logic.disj(b1, b2)

    def imp(self, b1, b2):
        return Term.mk_implies(b1, b2)

    def neg(self, b):
        return logic.neg(b)

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

def process_file(input):
    thy = basic.load_theory('hoare')

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
            print(c.print_com(thy))
