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
    
    ?let_pair: "(" NAME logical ")" -> let_pair

    ?logical: "(-" logical ")" -> uminus_tm
        | "(+" logical logical ")" -> plus_tm
        | "(-" logical logical ")" -> minus_tm
        | "(*" logical logical ")" -> times_tm
        | "(/" logical logical ")" -> divides_tm
        | "(>" logical logical ")" -> greater_tm
        | "(<" logical logical ")" -> less_tm
        | "(>=" logical logical ")" -> greater_eq_tm
        | "(<=" logical logical ")" -> less_eq_tm
        | "(not" logical ")" -> neg_tm
        | "(and" logical logical+ ")" -> conj_tm
        | "(or" logical logical+ ")" -> disj_tm
        | "(=>" logical logical ")" -> implies_tm      
        | "(ite" logical logical logical ")"
        | "(distinct" logical logical+ ")" -> distinct_tm  
        | "#" INT ":" logical -> names_tm
        | "#" INT -> repr_tm
        | "(exists" "(" typed_atom ")" logical* ")" -> exists_tm
        | "(forall" "(" typed_atom ")" logical* ")" -> forall_tm
        | "(" logical "#" INT ":" logical ")" -> pair_tm
        | "(=" logical logical ")" -> equals_tm
        | "(let (" let_pair+ ")" logical* ")" -> let_tm1
        | "(" logical logical+ ")" -> comb_tm
        | atom

    ?conclusion: "conclusion (" logical* ")" -> concl_tm

    ?clause_name: ".c" INT -> clause_name

    ?clauses: "clauses (" clause_name+ ")" -> get_clauses

    ?args: "args (" NAME ")" -> args

    ?proof: "(set .c" INT "(" NAME ":" clauses ":" conclusion "))" -> step_proof1
        | "(set .c" INT "(" NAME ":" args ":" conclusion "))" -> step_proof2
        | "(set .c" INT "(" NAME ":"  conclusion "))" -> step_proof3
        | "(set .c" INT "(input :" conclusion "))" -> input_proof
        | logical

    %import common.CNAME
    %import common.INT
    %import common.DIGIT
    %import common.DECIMAL
    %import common.WS
    %ignore WS
    NAME: (CNAME|"$"|"@"|"?")("?"|"$"|"@"|CNAME|DIGIT)*
"""
@v_args(inline=True)
class TypeTransformer(Transformer):
    """Parse types in format of smt2."""
    def __init__(self):
        pass

    def convert_type(self, T):
        """convert Int, Bool, Real to IntType, BoolType, RealType."""
        if T == "Bool":
            return BoolType
        elif T == "Int":
            return IntType
        elif T == "Real":
            return RealType
        else:
            return TConst(T)

    def sort_type(self, name, arity):
        return TConst(str(name))

    def fun_type1(self, name, *args):
        return Var(str(name), TFun(*[self.convert_type(t) for t in args]))

    def fun_type2(self, n1, n2):
        """
        Args:
            n1: name of the variable
            n2: type

        return a HOL variable
        """ 
        if n2 == "Bool":
            range_type = BoolType
        elif n2 == "Int":
            range_type = IntType
        elif n2 == "Real":
            range_type = RealType
        else:
            range_type = TConst(n2)

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
        if x in self.sorts:
            return self.sorts[x]
        else:
            raise NotImplementedError
    
    def integer(self, num):
        return Int(int(num))
    
    def decimal(self, num):
        return Real(float(num))

    def int_tm(self, var):
        self.sorts[var.value] = Var(var.value, IntType)
        return Var(var.value, IntType)
    
    def real_tm(self, var):
        self.sorts[var.value] = Var(var.value, RealType)
        return Var(var.value, RealType)

    def bool_tm(self, var):
        self.sorts[var.value] = Var(var.value, BoolType)
        return Var(var.value, BoolType)

    def comb_tm(self, *args):
        return args[0](*args[1:])

    def uminus_tm(self, arg):
        return -arg

    def plus_tm(self, lhs, rhs):
        return lhs + rhs

    def minus_tm(self, lhs, rhs):
        return lhs - rhs

    def times_tm(self, lhs, rhs):
        return lhs * rhs

    def greater_tm(self, lhs, rhs):
        return lhs > rhs

    def greater_eq_tm(self, lhs, rhs):
        return lhs >= rhs

    def less_tm(self, lhs, rhs):
        return lhs < rhs

    def less_eq_tm(self, lhs, rhs):
        return lhs <= rhs

    def neg_tm(self, tm):
        return Not(tm)

    def conj_tm(self, *tm):
        conj_tm = And(*tm)
        conj_tm.arity = len(tm)
        return conj_tm

    def disj_tm(self, *tm):
        disj_tm = Or(*tm)
        disj_tm.arity = len(tm)
        return disj_tm

    def implies_tm(self, s, t):
        return Implies(s, t)

    def distinct_tm(self, *tm):
        dis_tm = [Not(Eq(tm[i], tm[j])) for i in range(len(tm)) for j in range(i+1, len(tm))]
        return And(*dis_tm)

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
        return Eq(lhs, rhs)

    def pair_tm(self, s, t):
        return (s, t)

    def let_pair(self, tm1, tm2):
        """Note: the let var used in body will be inserted a dollar symbol at first position."""
        inferred_tm1 = Var(tm1.value, tm2.get_type())
        self.sorts[tm1.value] = inferred_tm1
        return (inferred_tm1, tm2)

    def let_tm1(self, *tms):
        return tms[-1]

    def let_tm2(self, *tms):
        return tms[-1]

    def name_let_tm(self, tm1, tm2, *tms):
        ty = tm2.get_type()
        self.sorts[tm1.name] = Var(tm1.name, ty)
        return tms[-1]
    
    def concl_tm(self, *tms):
        # if len(tms) == 1:
        #     return tms[0]
        # else:
        #     return Or(*tms)
        return Concl(*tms)

    def clause_name(self, cl):
        return int(cl.value)

    def get_clauses(self, *clauses):
        return tuple(clauses)

    def args(self, name):
        """Used in forall_inst."""
        return name

    def step_proof1(self, num, proof_name, assms, concl):
        self.clauses[int(num.value)] = concl
        return Rule(int(num), str(proof_name), concl, assms=assms)

    def step_proof2(self, num, proof_name, args, concl):
        return Rule(int(num), str(proof_name), concl, args=args)

    def step_proof3(self, num, proof_name, concl):
        return Rule(int(num), str(proof_name), concl)

    def input_proof(self, num, concl):
        self.clauses[num] = concl
        return Rule(int(num), "input", concl)

def term_parser(sorts):
    return Lark(grammar, start="proof", parser="lalr", transformer=TermTransformer(sorts=sorts))

type_parser = Lark(grammar, start="type", parser="lalr", transformer=TypeTransformer())

def parse_step(s, sorts):
    """Parse a proof step."""
    try:
        return term_parser(sorts).parse(s)
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