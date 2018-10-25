# Author: Bohua Zhan

from lark import Lark, Transformer

from kernel.type import TVar, Type, TFun
from kernel.term import Var, Const, Comb, Abs, Bound, Term

grammar = r"""
    ?type: "'" CNAME -> tvar              // Type variable
        | type "=>" type -> funtype       // Function types
        | CNAME -> type                   // Type constants
        | type CNAME                      // Type constructor with one argument
        | "(" type ("," type)* ")" CNAME  // Type constructor with multiple arguments
        | "(" type ")"                    // Parenthesis

    ?atom: CNAME -> vname                       // Constant, variable, or bound variable
        | "%" CNAME "::" type ". " term -> abs  // Abstraction
        | "(" term ")"                          // Parenthesis

    ?comb: comb atom | atom

    ?eq: comb "=" comb | comb

    ?implies: eq "-->" implies | eq

    ?term: implies

    %import common.CNAME
    %import common.WS

    %ignore WS
"""

class HOLTransformer(Transformer):
    def __init__(self, thy, ctxt = dict()):
        """thy is the current Theory object. ctxt is a dictionary
        from names of free variables to their types.

        """
        self.thy = thy
        self.ctxt = ctxt

    def tvar(self, args):
        assert len(args) == 1, "tvar: one argument expected"
        return TVar(args[0])

    def type(self, args):
        return Type(args[-1], *args[:-1])

    def funtype(self, args):
        assert len(args) == 2, "funtype: two arguments expected"
        return TFun(*args)

    def vname(self, args):
        assert len(args) == 1, "vname: one argument expected"
        s = args[0]

        if self.thy.has_term_sig(s):
            # s is the name of a constant in the theory
            return Const(s, self.thy.get_term_sig(s))
        elif s in self.ctxt:
            # s is the name of a variable in the theory
            return Var(s, self.ctxt[s])
        else:
            # s not found, presumably a bound variable
            return Var(s, None)

    def comb(self, args):
        assert len(args) == 2, "comb: two arguments expected"
        return Comb(args[0], args[1])

    def abs(self, args):
        assert len(args) == 3, "abs: three arguments expected"
        var_name, T, body = args

        # Bound variables should be represented by Var(var_name, None).
        # Abstract over it, and remember to change the type to T.
        t = body.abstract_over(Var(var_name, None))
        return Abs(var_name, T, t.body)

    def eq(self, args):
        assert len(args) == 2, "eq: two arguments expected"
        return Term.mk_equals(*args)

    def implies(self, args):
        assert len(args) == 2, "implies: two arguments expected"
        return Term.mk_implies(*args)

def type_parser(thy):
    return Lark(grammar, start="type", parser="lalr", transformer=HOLTransformer(thy))

def term_parser(thy, ctxt):
    return Lark(grammar, start="term", parser="lalr", transformer=HOLTransformer(thy, ctxt))
