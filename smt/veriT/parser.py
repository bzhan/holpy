"""
A proof parser for veriT with arguments:
[--proof-prune, --proof-with-sharing, --proof-version=2, --proof-merge]
"""

from lark import Lark, Transformer, v_args, exceptions
from smt.veriT.proof import *
from kernel.term import *

grammar = r"""
    ?sort_type: "(declare-sort " CNAME INT ")"
    ?fun_type: "(declare-fun " CNAME (CNAME*) CNAME ")"

    ?type: sort_type -> type | fun_type -> type

    ?atom: CNAME -> var_name
        | INT -> integer
        | DECIMAL -> decimal
        | "@" CNAME -> quant_var
        
    ?typed_atom: "(" atom "Int" ")" -> int_tm
        | "(" atom "Real)" -> real_tm
        | "(" atom "Bool)" -> bool_tm 
    
    ?comb: "(" comb atom+ ")" -> comb_tm
        | atom

    ?arith: "(-" arith ")" -> uminus_tm
        | "(+" arith arith ")" -> plus_tm
        | "(-" arith arith ")" -> minus_tm
        | "(*" arith arith ")" -> times_tm
        | "(/" arith arith ")" -> divides_tm
        | comb

    ?compares: "(>" arith arith ")" -> greater_tm
        | "(<" arith arith ")" -> less_tm
        | "(>=" arith arith ")" -> greater_eq_tm
        | "(<=" arith arith ")" -> less_eq_tm
        | arith

    ?logical: "(not" logical ")" -> neg_tm
        | "(and" logical logical+ ")" -> and_tm
        | "(or" logical logical+ ")" -> or_tm
        | "(=>" logical logical ")" -> implies_tm
        | "#" INT ":" logical -> name_tm
        | "#" INT -> repr_tm
        | "(exists" "(" typed_atom+ ")" logical ")" -> exists_tm
        | "(forall" "(" typed_atom+ ")" logical ")" -> forall_tm
        | "(let (" logical+ "))" -> let_tm
        | compares

    ?conclusion: "conclusion (" logical* ")" -> concl_tm | "conclusion ((" logical* "))" -> concl_tm

    ?clause_name: "c" INT -> clause_name

    ?clauses: "clauses (." clause_name+ ")" -> clauses

    ?args: "args (" CNAME+ ")" -> args

    ?step: "(set .c" INT "(" CNAME ":" (clauses | args) ":" conclusion "))" -> step

    ?input: "(set .c" INT "(" CNAME ":" conclusion "))" -> input
    
    ?proof: step -> proof | input -> proof

    %import common.CNAME
    %import common.INT
    %import common.DECIMAL
    %import common.WS
    %ignore WS
"""

@v_args(inline=True)
class TermTransformer(Transformer):
    """Parse terms in proof."""
    def __init__(self, sorts):
        """
        Args:
            sorts: a dict map from variable(function) name to its sort
        """
        self.sorts = sorts

    def var_name(self, x):
        return Var(x, self.sorts[a])
    
    def integer(self, num):
        return Int(num)
    
    def decimal(self, num):
        return Real(num)

    def int_tm(self, var):
        return Var(var, IntType)
    
    def real_tm(self, var):
        return Var(var, RealType)

    def bool_tm(self, var):
        return Var(var, BoolType)

    def comb_tm(self, *args):
        pass

@v_args(inline=True)
class ProofTransformer(Transformer):
    """Parse a proof step."""
    def __init__(self):
        pass
    
    def var_name(self, a):
        return Var(a)

term_parser = Lark(grammar, start="logical", parser="lalr", transformer=TermTransformer())
proof_parser = Lark(grammar, start="proof", parser="lalr", transformer=ProofTransformer())

def parse_term(s):
    """Parse a proof step."""
    try:
        return term_parser.parse(s)
    except (exceptions.UnexpectedCharacters, exceptions.UnexpectedToken) as e:
        print("When parsing:", s)
        raise e