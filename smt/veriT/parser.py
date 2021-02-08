"""
A proof parser for veriT with arguments:
[--proof-prune, --proof-with-sharing, --proof-version=2, --proof-merge]
"""

from lark import Lark, Transformer, v_args, exceptions
from smt.veriT.proof import *
from kernel.term import *
from kernel.type import TConst
from kernel.proofterm import ProofTerm
from logic import context
from syntax import parser as hol_parser
from fractions import Fraction
import numbers

grammar = r"""
    ?type: "(declare-sort" NAME INT ")" -> sort_type
        | "(declare-fun " NAME "(" NAME+ ")" NAME ")" -> fun_type1
        | "(declare-fun " NAME "()" NAME ")" -> fun_type2

    ?atom: "true" -> true_tm
        | "false" -> false_tm
        | NAME -> var_name
        | (DECIMAL|INT)
        
    ?typed_atom: "(" NAME NAME ")" -> common_tm
     
    ?let_pair: "(" NAME logical ")" -> let_pair

    ?logical: "(-" logical ")" -> uminus_tm
        | "(+" logical+ ")" -> plus_tm
        | "(-" logical+ ")" -> minus_tm
        | "(*" logical+ ")" -> times_tm
        | "(/" logical logical ")" -> divides_tm
        | "(>" logical logical ")" -> greater_tm
        | "(<" logical logical ")" -> less_tm
        | "(>=" logical logical ")" -> greater_eq_tm
        | "(<=" logical logical ")" -> less_eq_tm
        | "(not" logical ")" -> neg_tm
        | "(and" logical logical+ ")" -> conj_tm
        | "(or" logical logical+ ")" -> disj_tm
        | "(=>" logical logical ")" -> implies_tm      
        | "(ite" logical logical logical ")" -> ite_tm
        | "(distinct" logical logical+ ")" -> distinct_tm  
        | "#" INT ":" logical -> names_tm
        | "#" INT -> repr_tm
        | "(exists" "(" typed_atom+ ")" logical* ")" -> exists_tm
        | "(forall" "(" typed_atom+ ")" logical* ")" -> forall_tm
        | "(=" logical logical ")" -> equals_tm
        | "(let (" let_pair+ ")" logical* ")" -> let_tm1
        | "(" logical logical+ ")" -> comb_tm
        | atom

    ?conclusion: "conclusion (" logical* ")" -> concl_tm

    ?clause_name: ".c" INT -> clause_name

    ?clauses: "clauses (" clause_name+ ")" -> get_clauses

    ?args: "args (" (NAME|NUMBER) ")" -> args

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
    %import common.NUMBER
    %ignore WS
    NAME: (CNAME|"$"|"?"|"@")("~"|"?"|"$"|"@"|CNAME|DIGIT)*
"""

@v_args(inline=True)
class TypeTransformer(Transformer):
    """Parse types in format of smt2."""
    def __init__(self):
        pass

    def type_str(self, s):
        return s.lower() if s in ("Bool", "Real", "Int") else s

    def sort_type(self, name, arity):
        return str(name)

    def fun_type1(self, name, *args):
        T = " => ".join(self.type_str(s) for s in args)
        return {name.value: T}

    def fun_type2(self, n1, n2):
        """
        Args:
            n1: name of the variable
            n2: type

        return a HOL variable
        """ 
        return {n1.value: self.type_str(n2)}

def bind_var(smt2_file):
    """Given a smt2 file, parse the declaration of sorts and return a dict."""
    d = dict()
    with open(smt2_file, "r") as f:
        for s in f.readlines():
            if s.strip().startswith("(declare-fun"):
                d.update(type_parser.parse(s.replace("\n", "")))
    return d

@v_args(inline=True)
class TermTransformer(Transformer):
    """Parse terms in proof.
    
    Note: For now, remove all the "?" or "$" at the start of variable.
    """
    def __init__(self, ctx):
        """
        Args:
            sorts: maps from variable name to variable
        """
        context.set_context("verit", vars=ctx)
        # mapping from let vars to the real tm
        self.sorts = dict()

        # names mapping a sequence number to a term
        self.names = dict()

        # clauses mapping a sequence number to a proof term
        self.clauses = dict()

        # ite_num mapping a number to an ite term
        self.ites = dict()

        # store the vars occured in the text
        self.vars = set()

    def true_tm(self):
        return "true"
    
    def false_tm(self):
        return "false"

    def ite_name(self, num):
        return self.ites[int(num)]

    def var_name(self, x):
        s = str(x)
        if s in self.sorts:
            return self.sorts[s]
        if s[:4] == "@ite":
            return self.ite_name(int(x[4:]))
        if s[0] == "$" and s not in self.sorts and s[1:] in self.sorts:
            return s[1:]
        if s[0] == "@":
            return s[1:]
        return s

    def comb_tm(self, *args):
        return "(" + " ".join(str(arg) for arg in args) + ")"

    def uminus_tm(self, arg):
        return "-" + str(arg)

    def plus_tm(self, *tms):
        return "(%s)" % (" + ".join(str(t) for t in tms))

    def minus_tm(self, *tms):
        return "(%s)" % (" - ".join(str(t) for t in tms))

    def times_tm(self, *tms):
        return "(%s)" % (" * ".join(str(t) for t in tms))

    def divides_tm(self, lhs, rhs):
        return "(%s / %s)" % (str(lhs), str(rhs))

    def greater_tm(self, lhs, rhs):
        return "(%s > %s)" % (str(lhs), str(rhs))

    def greater_eq_tm(self, lhs, rhs):
        return "(%s >= %s)" % (str(lhs), str(rhs))

    def less_tm(self, lhs, rhs):
        return "(%s < %s)" % (str(lhs), str(rhs))

    def less_eq_tm(self, lhs, rhs):
        return "(%s <= %s)" % (str(lhs), str(rhs))

    def neg_tm(self, tm):
        return "~(%s)" % str(tm)

    def conj_tm(self, *tms):
        return "(%s)" % (" & ".join(str(tm) for tm in tms))

    def disj_tm(self, *tms):
        return "(%s)" % (" | ".join(str(tm) for tm in tms))

    def implies_tm(self, s, t):
        return "(%s --> %s)" % (str(s), str(t))

    def distinct_tm(self, *tms):
        str_tms = ["~(%s = %s)" % (str(tm[i]), str(tm[j])) for i in range(len(tms)) for j in range(i+1, len(tms))]
        return "(%s)" % (" & ".join(str_tms))

    def names_tm(self, num, tm):
        self.names[num] = str(tm)
        return str(tm)

    def repr_tm(self, num):
        return self.names[num]

    def exists_tm(self, *vs):
        var, tm = ". ".join("?" + str(v) for v in vs[:-1]), vs[-1]
        return "(%s. %s)" % (str(var), str(tm))

    def forall_tm(self, *vs):
        var, tm = ". ".join("!" + str(v) for v in vs[:-1]), vs[-1]
        return "(%s. %s)" % (str(var), str(tm))
    
    def equals_tm(self, lhs, rhs):
        return "(%s = %s)" % (str(lhs), str(rhs))

    def ite_tm(self, tm1, tm2, tm3):
        s = "(if %s then %s else %s)" % (str(tm1), str(tm2), str(tm3))
        self.ites[len(self.ites)] = s 
        return s

    def common_tm(self, tm1, tm2):
        if tm2.value in ("Real", "Int", "Bool"):
            tm2 = str(tm2).lower()
        if tm1.value[0] == "@":
            tm1 = str(tm1[1:])
        return "%s::%s" % (str(tm1), str(tm2))

    def let_pair(self, tm1, tm2):
        """Note: the let var used in body will be inserted a dollar symbol at first position."""
        T = hol_parser.parse_term(tm2).get_type()
        s = "(%s :: %s)" % (str(tm1), T.name)
        self.sorts[str(tm1)] = str(tm2)

    def let_tm1(self, *tms):
        return tms[-1]
    
    def concl_tm(self, *tms):
        hol_tms = [hol_parser.parse_term(str(tm)) for tm in tms]
        return Concl(*hol_tms)

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

type_parser = Lark(grammar, start="type", parser="lalr", transformer=TypeTransformer())

def term_parser(ctx):
    return Lark(grammar, start="proof", parser="lalr", transformer=TermTransformer(ctx=ctx))

def parse_step(s, ctx):
    """Parse a proof step."""
    try:
        return term_parser(ctx).parse(s)
    except (exceptions.UnexpectedCharacters, exceptions.UnexpectedToken) as e:
        print("When parsing:", s)
        raise e