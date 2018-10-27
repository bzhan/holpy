# Author: Bohua Zhan

from lark import Lark, Transformer, v_args

from kernel.type import TVar, Type, TFun
from kernel.term import Var, Const, Comb, Abs, Bound, Term
from kernel.thm import Thm
from logic.basic import Logic

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

    ?eq: eq "=" comb | comb      // Equality: priority 50

    ?conj: eq "&" conj | eq      // Conjunction: priority 35

    ?disj: conj "|" disj | conj  // Disjunction: priority 30

    ?imp: disj "-->" imp | disj  // Implies: priority 25

    ?term: imp

    thm: "|-" term
        | term ("," term)* "|-" term

    %import common.CNAME
    %import common.WS

    %ignore WS
"""

@v_args(inline=True)
class HOLTransformer(Transformer):
    def __init__(self, thy, ctxt = None):
        """thy is the current Theory object.
        
        ctxt is a dictionary from names of free variables to their types.
        Default to the empty dictionary.

        """
        self.thy = thy
        if ctxt is None:
            ctxt = dict()
        self.ctxt = ctxt

    def tvar(self, s):
        return TVar(s)

    def type(self, *args):
        return Type(args[-1], *args[:-1])

    def funtype(self, t1, t2):
        return TFun(t1, t2)

    def vname(self, s):
        if self.thy.has_term_sig(s):
            # s is the name of a constant in the theory
            return Const(s, self.thy.get_term_sig(s))
        elif s in self.ctxt:
            # s is the name of a variable in the theory
            return Var(s, self.ctxt[s])
        else:
            # s not found, presumably a bound variable
            return Var(s, None)

    def comb(self, fun, arg):
        return Comb(fun, arg)

    def abs(self, var_name, T, body):
        # Bound variables should be represented by Var(var_name, None).
        # Abstract over it, and remember to change the type to T.
        t = body.abstract_over(Var(var_name, None))
        return Abs(var_name, T, t.body)

    def eq(self, lhs, rhs):
        return Term.mk_equals(lhs, rhs)

    def conj(self, s, t):
        return Logic.mk_conj(s, t)

    def disj(self, s, t):
        return Logic.mk_disj(s, t)

    def imp(self, s, t):
        return Term.mk_implies(s, t)

    def thm(self, *args):
        return Thm(args[:-1], args[-1])

def type_parser(thy):
    """Parse a type."""
    return Lark(grammar, start="type", parser="lalr", transformer=HOLTransformer(thy))

def term_parser(thy, ctxt):
    """Parse a term."""
    return Lark(grammar, start="term", parser="lalr", transformer=HOLTransformer(thy, ctxt))

def thm_parser(thy, ctxt):
    """Parse a theorem (sequent)."""
    return Lark(grammar, start="thm", parser="lalr", transformer=HOLTransformer(thy, ctxt))

def split_proof_rule(s):
    """Split proof rule into parseable parts.

    Currently able to handle string of the form:
    [id]: [rule_name] [args] by [prevs]

    """
    id, rest = s.split(": ", 1)  # split off id
    id = id.strip()
    rule_name, rest = rest.split(" ", 1)  # split off name of rule
    rule_name = rule_name.strip()

    if rest.count("from") > 0:
        args, rest = rest.split("from", 1)
        return (id, rule_name, args.strip(), [prev.strip() for prev in rest.split(",")])
    else:
        return (id, rule_name, rest.strip(), [])

def parse_proof_rule(thy, ctxt, s):
    """Parse a proof rule.

    This need to be written by hand because different proof rules
    require different parsing of the arguments.

    """
    (id, rule_name, args, prevs) = split_proof_rule(s)

