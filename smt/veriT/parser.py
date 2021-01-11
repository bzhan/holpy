"""
A proof parser for veriT with arguments:
[--proof-prune, --proof-with-sharing, --proof-version=2, --proof-merge]
"""

from lark import Lark, Transformer, v_args, exceptions
from smt.veriT.proof import *
from kernel.term import *
from kernel.type import TConst
from kernel.proofterm import ProofTerm

grammar = r"""
    ?type: "(declare-sort" NAME INT ")" -> sort_type
        | "(declare-fun " NAME "(" NAME+ ")" NAME ")" -> fun_type1
        | "(declare-fun " NAME "()" NAME ")" -> fun_type2
    ?atom: NAME -> var_name
        | INT -> integer
        | DECIMAL -> decimal
        | "@" NAME -> quant_var
        
    ?typed_atom: "(" NAME "Int" ")" -> int_tm
        | "(" NAME "Real)" -> real_tm
        | "(" NAME "Bool)" -> bool_tm 
    
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
        | "(and" logical logical+ ")" -> conj_tm
        | "(or" logical logical+ ")" -> disj_tm
        | "(=>" logical logical ")" -> implies_tm        
        | "#" INT ":" logical -> names_tm
        | "#" INT -> repr_tm
        | "(exists" "(" typed_atom+ ")" logical* ")" -> exists_tm
        | "(forall" "(" typed_atom+ ")" logical* ")" -> forall_tm
        | "(" logical logical ")" -> pair_tm
        | "(=" logical logical ")" -> equals_tm
        | "#" INT ":(let (" (logical)+ ")" logical* ")" -> name_let_tm
        | compares

    ?conclusion: "conclusion (" logical* ")" -> concl_tm

    ?clause_name: ".c" INT -> clause_name

    ?clauses: "clauses (" clause_name+ ")" -> clauses

    ?args: "args (" CNAME ")" -> args

    ?proof: "(set .c" INT "(" CNAME ":" ((clauses | args)":")? conclusion "))" -> step_proof 
        | "(set .c" INT "(input :" conclusion "))" -> input_proof
        | logical

    %import common.CNAME
    %import common.INT
    %import common.DIGIT
    %import common.DECIMAL
    %import common.WS
    %ignore WS
    NAME: (CNAME|"$"|"@")("$"|"@"|CNAME|DIGIT)*
"""
@v_args(inline=True)
class TypeTransformer(Transformer):
    """Parse types in format of smt2."""
    def __init__(self):
        pass

    def sort_type(self, name, arity):
        return TConst(str(name))

    def fun_type1(self, name, *args):
        """
        Args:
            n1: name of the variable
            n2: list of arguments
            n3: range type

        return a HOL variable
        """ 
        domain_type = [TConst(t) for t in args[:-1]]
        if args[-1] == "Bool":
            range_type = BoolType
        elif args[-1] == "Int":
            range_type = IntType
        elif args[-1] == "Real":
            range_type = RealType
        else:
            range_type = TConst(args[-1])

        return Var(str(name), TFun(*domain_type, range_type))

    def fun_type2(self, n1, n2):
        """
        Args:
            n1: name of the variable
            n2: list of arguments
            n3: range type

        return a HOL variable
        """ 
        if n2 == "Bool":
            range_type = BoolType
        elif n2 == "Int":
            range_type = IntType
        elif n2 == "Real":
            range_type = RealType
        else:
            range_type = TConst(n3)

        return Var(str(n1), range_type)

def bind_var(smt2_file):
    """Given a smt2 file, parse the declaration of sorts and return a dict."""
    with open(smt2_file, "r") as f:
        return {type_parser.parse(s.replace("\n", "")).name: \
                    type_parser.parse(s.replace("\n", "")) for s in f.readlines() if \
                        s.startswith("(declare-fun")}

@v_args(inline=True)
class TermTransformer(Transformer):
    """Parse terms in proof."""
    def __init__(self, sorts):
        """
        Args:
            sorts: maps from variable name to variable
        """
        self.sorts = sorts

        # names mapping a sequence number to a term
        self.names = dict()

        # clauses mapping a sequence number to a proof term
        self.clauses = dict()

    def var_name(self, x):
        return self.sorts[x]
    
    def integer(self, num):
        return Int(num)
    
    def decimal(self, num):
        return Real(num)

    def int_tm(self, var):
        return Var(var.value, IntType)
    
    def real_tm(self, var):
        return Var(var.value, RealType)

    def bool_tm(self, var):
        return Var(var.value, BoolType)

    def comb_tm(self, *args):
        return args[0](*args[1:])

    def uminus_tm(self, arg):
        return Const("uminus", None)(arg)

    def plus_tm(self, lhs, rhs):
        return Const("plus", None)(lhs, rhs)

    def minus_tm(self, lhs, rhs):
        return Const("minus", None)(lhs, rhs)

    def times_tm(self, lhs, rhs):
        return Const("times", None)(lhs, rhs)

    def greater_tm(self, lhs, rhs):
        return Const("greater", None)(lhs, rhs)

    def greater_eq_tm(self, lhs, rhs):
        return Const("greater_eq", None)(lhs, rhs)

    def less_tm(self, lhs, rhs):
        return Const("less", None)(lhs, rhs)

    def less_eq_tm(self, lhs, rhs):
        return Const("less_eq", None)(lhs, rhs)

    def neg_tm(self, tm):
        return Not(tm)

    def conj_tm(self, *tm):
        return And(tm)

    def disj_tm(self, *tm):
        return Or(tm)

    def implies_tm(self, s, t):
        return Implies(s, t)

    def names_tm(self, num, tm):
        self.names[num] = tm
        return tm

    def repr_tm(self, num):
        return self.names[num]

    def exists_tm(self, v, t):
        return Exists(v, t)

    def forall_tm(self, v, t):
        return Forall(v, t)
    
    def equals_tm(self, lhs, rhs):
        return Const("equals", None)(lhs, rhs)

    def pair_tm(self, s, t):
        return (s, t)

    def let_tm(self, *tms):
        return [ProofTerm.assume(Eq(s, t)) for s, t in tms]

    def name_let_tm(self, num, *tms):
        return [ProofTerm.assume(Eq(s, t)) for s, t in tms]
    
    def concl_tm(self, *tms):
        return Or(*tms)

    def clause_name(self, cl):
        return self.clauses[cl]

    def clauses(self, *clauses):
        return tuple(clauses)

    def args(self, name):
        """Used in forall_inst."""
        return name

    def step_proof(self, num, params, concl):
        self.clauses[num] = concl
        return Rule(num, params, concl)

    def input_proof(self, num, concl):
        self.clauses[num] = concl
        return Input(num, concl)

def term_parser(sorts):
    return Lark(grammar, start="proof", parser="lalr", transformer=TermTransformer(sorts=sorts))

type_parser = Lark(grammar, start="type", parser="lalr", transformer=TypeTransformer())

def parse_term(s):
    """Parse a proof step."""
    try:
        return term_parser.parse(s)
    except (exceptions.UnexpectedCharacters, exceptions.UnexpectedToken) as e:
        print("When parsing:", s)
        raise e

def parse_type(s):
    """Parse a proof step."""
    try:
        return type_parser.parse(s)
    except (exceptions.UnexpectedCharacters, exceptions.UnexpectedToken) as e:
        print("When parsing:", s)
        raise e
