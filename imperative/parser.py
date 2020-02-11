# Author: Bohua Zhan

import json, os
from lark import Lark, Transformer, v_args, exceptions

from kernel.type import TFun, NatType
from kernel.term import Term, Var, Not, And, Or, Implies, Eq, Lambda, true, Nat
from kernel.report import ProofReport
from kernel import theory
from logic import basic
from logic import logic
from data import nat
from data.function import mk_const_fun, mk_fun_upd
from imperative import imp
from kernel.proofterm import ProofTerm
from syntax import json_output

"""Parsing for simple imperative programs."""

grammar = r"""
    ?expr: CNAME -> var_expr
        | INT -> num_expr
        | expr "+" expr -> plus_expr
        | expr "*" expr -> times_expr

    ?cond: expr "==" expr -> eq_cond
        | expr "!=" expr -> ineq_cond
        | expr "<=" expr -> less_eq_cond
        | expr "<" expr -> less_cond
        | cond "&" cond -> conj_cond
        | cond "|" cond -> disj_cond
        | "true" -> true_cond

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

natFunT = TFun(NatType, NatType)
st = Var("s", natFunT)

def str_to_nat(s):
    """Convert string to natural number."""
    return ord(s) - ord("a")

@v_args(inline=True)
class HoareTransformer(Transformer):
    def __init__(self):
        pass

    def var_expr(self, s):
        if ord(s) >= ord('a') and ord(s) <= ord('z'):
            return st(Nat(str_to_nat(s)))
        elif ord(s) >= ord('A') and ord(s) <= ord('Z'):
            return Var(s, NatType)
        else:
            raise NotImplementedError

    def num_expr(self, n):
        return Nat(int(n))

    def plus_expr(self, e1, e2):
        return nat.plus(e1, e2)

    def times_expr(self, e1, e2):
        return nat.times(e1, e2)

    def eq_cond(self, e1, e2):
        return Eq(e1, e2)

    def ineq_cond(self, e1, e2):
        return Not(Eq(e1, e2))

    def conj_cond(self, b1, b2):
        return And(b1, b2)

    def disj_cond(self, b1, b2):
        return Or(b1, b2)

    def true_cond(self):
        return true

    def less_eq_cond(self, e1, e2):
        return nat.less_eq(e1, e2)

    def less_cond(self, e1, e2):
        return nat.less(e1, e2)

    def skip_cmd(self):
        return imp.Skip(natFunT)

    def assign_cmd(self, v, e):
        Assign = imp.Assign(NatType, NatType)
        return Assign(Nat(str_to_nat(v)), Lambda(st, e))

    def if_cmd(self, b, c1, c2):
        Cond = imp.Cond(natFunT)
        return Cond(Lambda(st, b), c1, c2)

    def while_cmd(self, b, c):
        While = imp.While(natFunT)
        return While(Lambda(st, b), Lambda(st, true), c)

    def while_cmd_inv(self, b, inv, c):
        While = imp.While(natFunT)
        return While(Lambda(st, b), Lambda(st, inv), c)

    def seq_cmd(self, c1, c2):
        Seq = imp.Seq(natFunT)
        return Seq(c1, c2)

cond_parser = Lark(grammar, start="cond", parser="lalr", transformer=HoareTransformer())
com_parser = Lark(grammar, start="cmd", parser="lalr", transformer=HoareTransformer())

def parse_cond(s):
    return cond_parser.parse(s)

def parse_com(s):
    return com_parser.parse(s)

def process_file(input, output):
    basic.load_theory('hoare')

    dn = os.path.dirname(os.path.realpath(__file__))
    with open(os.path.join(dn, 'examples/' + input + '.json'), encoding='utf-8') as a:
        data = json.load(a)

    output = json_output.JSONTheory(output, ["hoare"], "Generated from " + input)
    content = data['content']
    eval_count = 0
    vcg_count = 0
    for run in content[:5]:
        if run['ty'] == 'eval':
            com = parse_com(run['com'])
            st1 = mk_const_fun(NatType, nat.zero)
            for k, v in sorted(run['init'].items()):
                st1 = mk_fun_upd(st1, Nat(str_to_nat(k)), Nat(v))
            st2 = mk_const_fun(NatType, nat.zero)
            for k, v in sorted(run['final'].items()):
                st2 = mk_fun_upd(st2, Nat(str_to_nat(k)), Nat(v))
            Sem = imp.Sem(natFunT)
            goal = Sem(com, st1, st2)
            prf = ProofTerm("eval_Sem", goal, []).export()
            rpt = ProofReport()
            th = theory.check_proof(prf, rpt)
            output.add_theorem("eval" + str(eval_count), th, prf)
            eval_count += 1
        elif run['ty'] == 'vcg':
            com = parse_com(run['com'])
            pre = Lambda(st, parse_cond(run['pre']))
            post = Lambda(st, parse_cond(run['post']))
            Valid = imp.Valid(natFunT)
            goal = Valid(pre, com, post)
            prf = imp.vcg_solve(goal).export()
            rpt = ProofReport()
            th = theory.check_proof(prf, rpt)
            output.add_theorem("vcg" + str(vcg_count), th, prf)
            vcg_count += 1
        else:
            raise TypeError

    output.export_json()
