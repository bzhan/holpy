"""Parser for expressions and rules."""

from lark import Lark, Transformer, v_args, exceptions

from geometry.expr import Fact, Rule


grammar = r"""
    ?fact: CNAME "(" CNAME ("," CNAME)* ")"
    ?rule: fact ":-" fact ("," fact)*

    %import common.CNAME
    %import common.WS

    %ignore WS
"""

@v_args(inline=True)
class GeometryTransformer(Transformer):
    def __init__(self):
        pass

    def fact(self, pred_name, *args):
        pred_name = str(pred_name)
        args = list(str(arg) for arg in args)
        return Fact(pred_name, args)

    def rule(self, concl, *assums):
        return Rule(list(assums), concl)


fact_parser = Lark(grammar, start="fact", parser="lalr", transformer=GeometryTransformer())
rule_parser = Lark(grammar, start="rule", parser="lalr", transformer=GeometryTransformer())

def parse_fact(s):
    return fact_parser.parse(s)

def parse_rule(s):
    return rule_parser.parse(s)
