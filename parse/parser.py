# Author: Bohua Zhan

from lark import Lark, Transformer

from kernel.type import TVar, Type

grammar = r"""
    ?start: type

    ?type: tvar
       | CNAME -> type
       | type CNAME
       | "(" type ("," type)* ")" CNAME

    tvar: "'" CNAME

    %import common.CNAME
    %import common.WS

    %ignore WS
"""

class TypeTransformer(Transformer):
    def tvar(self, s):
        assert len(s) == 1, "tvar: more than one argument"
        return TVar(s[0])

    def type(self, s):
        return Type(s[-1], *s[:-1])

type_parser = Lark(grammar, parser="lalr", lexer="standard", transformer=TypeTransformer())
