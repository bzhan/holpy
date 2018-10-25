# Author: Bohua Zhan

from lark import Lark, Transformer

from kernel.type import TVar, Type, TFun

grammar = r"""
    ?start: type

    ?type: "'" CNAME     -> tvar          // Type variable
        | type "=>" type -> funtype       // Function types
        | CNAME -> type                   // Type constants
        | type CNAME                      // Type constructor with one argument
        | "(" type ("," type)* ")" CNAME  // Type constructor with multiple arguments
        | "(" type ")"                    // Parenthesis

    %import common.CNAME
    %import common.WS

    %ignore WS
"""

class TypeTransformer(Transformer):
    def tvar(self, s):
        assert len(s) == 1, "tvar: one argument expected"
        return TVar(s[0])

    def type(self, s):
        return Type(s[-1], *s[:-1])

    def funtype(self, s):
        assert len(s) == 2, "funtype: two arguments expected"
        return TFun(*s)

type_parser = Lark(grammar, parser="lalr", lexer="standard", transformer=TypeTransformer())
