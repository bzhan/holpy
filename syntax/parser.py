# Author: Bohua Zhan

from typing import Tuple, List
import copy
from lark import Lark, Transformer, v_args, exceptions

from kernel import type as hol_type
from kernel.type import Type, STVar, TVar, TConst, TFun, BoolType, NatType, TyInst
from kernel.term import SVar, Var, Const, Comb, Abs, Bound, Term, Not, And, Or, Implies, Binary, Inst
from kernel import macro
from kernel import term
from kernel.thm import Thm
from kernel.proof import ProofItem
from kernel import theory
from kernel import extension
from logic import context
from syntax import infertype


class ParserException(Exception):
    """Exceptions during parsing."""
    def __init__(self, str):
        self.str = str


grammar = r"""
    ?type: "'" CNAME  -> tvar              // Type variable
        | "?'" CNAME  -> stvar             // Schematic type variable
        | type ("=>"|"⇒") type -> funtype       // Function types
        | CNAME -> type                   // Type constants
        | type CNAME                      // Type constructor with one argument
        | "(" type ("," type)* ")" CNAME  // Type constructor with multiple arguments
        | "(" type ")"                    // Parenthesis

    ?atom: CNAME -> vname                 // Constant, variable, or bound variable
        | "?" CNAME -> sname              // Schematic variable
        | INT -> number                   // Numbers
        | ("%"|"λ") CNAME "::" type ". " term -> abs     // Abstraction
        | ("%"|"λ") CNAME ". " term           -> abs_notype
        | ("!"|"∀") CNAME "::" type ". " term -> all     // Forall quantification
        | ("!"|"∀") CNAME ". " term           -> all_notype
        | ("?"|"∃") CNAME "::" type ". " term -> exists  // Exists quantification
        | ("?"|"∃") CNAME ". " term           -> exists_notype
        | ("?!"|"∃!") CNAME "::" type ". " term -> exists1   // Exists unique
        | ("?!"|"∃!") CNAME ". " term         -> exists1_notype
        | "THE" CNAME "::" type ". " term -> the         // THE operator
        | "THE" CNAME ". " term -> the_notype
        | "[]"                     -> literal_list  // Empty list
        | "[" term ("," term)* "]" -> literal_list  // List
        | ("{}"|"∅")               -> literal_set   // Empty set
        | "{" term ("," term)* "}" -> literal_set   // Set
        | "{" CNAME "::" type ". " term "}" -> collect_set
        | "{" CNAME ". " term "}"          -> collect_set_notype
        | "'" ("_"|LETTER|DIGIT) "'"  -> char
        | "\"" CNAME "\""               -> string
        | "if" term "then" term "else" term  -> if_expr // if expression
        | "(" term ")(" term ":=" term ("," term ":=" term)* ")"   -> fun_upd // function update
        | "{" term ".." term "}"   -> nat_interval
        | "(" term ")"                    // Parenthesis
        | "(" term "::" type ")"   -> typed_term    // Term with specified type

    ?comb: comb atom | atom

    ?big_inter: ("INT"|"⋂") big_inter -> big_inter | comb         // Intersection: priority 90

    ?big_union: ("UN"|"⋃") big_union -> big_union | big_inter     // Union: priority 90

    ?uminus: "-" uminus -> uminus | big_union   // Unary minus: priority 80

    ?power: power "^" uminus | uminus   // Power: priority 81

    ?times_expr: times_expr "*" power -> times     // Multiplication: priority 70
        | times_expr "/" power -> real_divide      // Division: priority 70
        | times_expr "DIV" power -> nat_divide     // Division: priority 70
        | times_expr "MOD" power -> nat_modulus    // Modulus: priority 70
        | power

    ?inter: inter ("Int"|"∩") times_expr | times_expr     // Intersection: priority 70

    ?plus_expr: plus_expr "+" inter  -> plus     // Addition: priority 65
        | plus_expr "-" inter -> minus           // Subtraction: priority 65
        | inter                   

    ?append: plus_expr "@" append | plus_expr    // Append: priority 65

    ?cons: append "#" cons | append     // Cons: priority 65

    ?union: union ("Un"|"∪") cons | cons        // Union: priority 65

    ?comp_fun: union ("O"|"∘") comp_fun | union // Function composition: priority 60

    ?eq: eq "=" comp_fun | comp_fun             // Equality: priority 50

    ?mem: mem ("Mem"|"∈") mem | eq              // Membership: priority 50

    ?subset: subset ("Sub"|"⊆") subset | mem    // Subset: priority 50

    ?less_eq: less_eq ("<="|"≤") less_eq | subset  // Less-equal: priority 50

    ?less: less "<" less | less_eq      // Less: priority 50

    ?greater_eq: greater_eq (">="|"≥") greater_eq | less   // greater-equal: priority 50

    ?greater: greater ">" greater | greater_eq     // greater: priority 50

    ?neg: ("~"|"¬") neg -> neg | greater   // Negation: priority 40

    ?conj: neg ("&"|"∧") conj | neg     // Conjunction: priority 35

    ?disj: conj ("|"|"∨") disj | conj   // Disjunction: priority 30

    ?iff: disj ("<-->"|"⟷") iff | disj // Iff: priority 25

    ?imp: iff ("-->"|"⟶") imp | iff    // Implies: priority 20

    ?term: imp

    thm: ("|-"|"⊢") term
        | term ("," term)* ("|-"|"⊢") term

    term_pair: CNAME ":" term

    inst: "{}"
        | "{" term_pair ("," term_pair)* "}"

    type_pair: CNAME ":" type

    tyinst: "{}"
        | "{" type_pair ("," type_pair)* "}"

    instsp: tyinst "," inst
    
    var_decl: CNAME "::" type  // variable declaration

    ind_constr: CNAME ("(" CNAME "::" type ")")*  // constructor for inductive types

    named_thm: CNAME ":" term | term  // named theorem

    term_list: term ("," term)*   // list of terms

    %import common.CNAME
    %import common.WS
    %import common.INT
    %import common.LETTER
    %import common.DIGIT

    %ignore WS
"""


@v_args(inline=True)
class HOLTransformer(Transformer):
    def __init__(self):
        pass

    def tvar(self, s):
        return TVar(str(s))

    def stvar(self, s):
        return STVar(str(s))

    def type(self, *args):
        return TConst(str(args[-1]), *args[:-1])

    def funtype(self, t1, t2):
        return TFun(t1, t2)

    def sname(self, s):
        s = str(s)
        return SVar(s, None)

    def vname(self, s):
        s = str(s)
        if theory.thy.has_term_sig(s) or s in context.ctxt.defs:
            # s is the name of a constant in the theory
            return Const(s, None)
        else:
            # s not found, either bound or free variable
            return Var(s, None)

    def typed_term(self, t, T):
        if t.is_comb('of_nat', 1) and t.arg.is_binary() and t.arg.dest_binary() >= 2:
            t.fun.T = TFun(NatType, T)
        else:
            t.T = T
        return t

    def number(self, n):
        if int(n) == 0:
            return Const("zero", None)
        elif int(n) == 1:
            return Const("one", None)
        else:
            return Const("of_nat", None)(Binary(int(n)))

    def literal_list(self, *args):
        from data import list
        return list.mk_literal_list(args, None)

    def char(self, c):
        from data import string
        return string.mk_char(str(c))

    def string(self, s):
        from data import string
        return string.mk_string(str(s))

    def if_expr(self, P, x, y):
        return Const("IF", None)(P, x, y)

    def fun_upd(self, *args):
        def helper(*args):
            if len(args) == 3:
                f, a, b = args
                return Const("fun_upd", None)(f, a, b)
            elif len(args) > 3:
                return helper(helper(*args[:3]), *args[3:])
            else:
                raise TypeError
        return helper(*args)

    def comb(self, fun, arg):
        return Comb(fun, arg)

    def abs(self, var_name, T, body):
        return Abs(str(var_name), T, body.abstract_over(Var(var_name, None)))

    def abs_notype(self, var_name, body):
        return Abs(str(var_name), None, body.abstract_over(Var(var_name, None)))

    def all(self, var_name, T, body):
        all_t = Const("all", None)
        return all_t(Abs(str(var_name), T, body.abstract_over(Var(var_name, None))))

    def all_notype(self, var_name, body):
        all_t = Const("all", None)
        return all_t(Abs(str(var_name), None, body.abstract_over(Var(var_name, None))))

    def exists(self, var_name, T, body):
        exists_t = Const("exists", None)
        return exists_t(Abs(str(var_name), T, body.abstract_over(Var(var_name, None))))

    def exists_notype(self, var_name, body):
        exists_t = Const("exists", None)
        return exists_t(Abs(str(var_name), None, body.abstract_over(Var(var_name, None))))

    def exists1(self, var_name, T, body):
        exists1_t = Const("exists1", None)
        return exists1_t(Abs(str(var_name), T, body.abstract_over(Var(var_name, None))))

    def exists1_notype(self, var_name, body):
        exists1_t = Const("exists1", None)
        return exists1_t(Abs(str(var_name), None, body.abstract_over(Var(var_name, None))))

    def the(self, var_name, T, body):
        the_t = Const("The", None)
        return the_t(Abs(str(var_name), T, body.abstract_over(Var(var_name, None))))

    def the_notype(self, var_name, body):
        the_t = Const("The", None)
        return the_t(Abs(str(var_name), None, body.abstract_over(Var(var_name, None))))

    def collect_set(self, var_name, T, body):
        from data import set
        return set.collect(T)(Abs(str(var_name), T, body.abstract_over(Var(var_name, None))))

    def collect_set_notype(self, var_name, body):
        from data import set
        return set.collect(None)(Abs(str(var_name), None, body.abstract_over(Var(var_name, None))))

    def power(self, lhs, rhs):
        return Const("power", None)(lhs, rhs)

    def times(self, lhs, rhs):
        return Const("times", None)(lhs, rhs)

    def real_divide(self, lhs, rhs):
        return Const("real_divide", None)(lhs, rhs)

    def nat_divide(self, lhs, rhs):
        return Const("nat_divide", None)(lhs, rhs)

    def nat_modulus(self, lhs, rhs):
        return Const("nat_modulus", None)(lhs, rhs)

    def plus(self, lhs, rhs):
        return Const("plus", None)(lhs, rhs)

    def minus(self, lhs, rhs):
        return Const("minus", None)(lhs, rhs)

    def uminus(self, x):
        return Const("uminus", None)(x)

    def less_eq(self, lhs, rhs):
        return Const("less_eq", None)(lhs, rhs)

    def less(self, lhs, rhs):
        return Const("less", None)(lhs, rhs)

    def greater_eq(self, lhs, rhs):
        return Const("greater_eq", None)(lhs, rhs)

    def greater(self, lhs, rhs):
        return Const("greater", None)(lhs, rhs)

    def append(self, lhs, rhs):
        return Const("append", None)(lhs, rhs)

    def cons(self, lhs, rhs):
        return Const("cons", None)(lhs, rhs)

    def eq(self, lhs, rhs):
        return Const("equals", None)(lhs, rhs)

    def neg(self, t):
        return Not(t)

    def conj(self, s, t):
        return And(s, t)

    def disj(self, s, t):
        return Or(s, t)

    def imp(self, s, t):
        return Implies(s, t)

    def iff(self, s, t):
        return Const("equals", None)(s, t)

    def literal_set(self, *args):
        from data import set
        return set.mk_literal_set(args, None)

    def mem(self, x, A):
        return Const("member", None)(x, A)

    def subset(self, A, B):
        return Const("subset", None)(A, B)

    def inter(self, A, B):
        return Const("inter", None)(A, B)

    def union(self, A, B):
        return Const("union", None)(A, B)

    def big_inter(self, t):
        return Const("Inter", None)(t)

    def big_union(self, t):
        return Const("Union", None)(t)

    def comp_fun(self, f, g):
        return Const("comp_fun", None)(f, g)

    def nat_interval(self, m, n):
        from data import interval
        return interval.mk_interval(m, n)

    def thm(self, *args):
        return Thm(args[:-1], args[-1])

    def term_pair(self, name, T):
        return (str(name), T)

    def type_pair(self, name, T):
        return (str(name), T)

    def inst(self, *args):
        return dict(args)

    def tyinst(self, *args):
        return dict(args)

    def instsp(self, *args):
        return tuple(args)

    def ind_constr(self, *args):
        constrs = {}
        constrs['name'] = str(args[0])
        constrs['args'] = []
        constrs['type'] = []
        for id in range(1, len(args), 2):
            constrs['args'].append(str(args[id]))
            constrs['type'].append(args[id+1])
        return constrs

    def var_decl(self, name, T):
        return (str(name), T)

    def named_thm(self, *args):
        return tuple(args)

    def term_list(self, *args):
        return list(args)


def get_parser_for(start):
    return Lark(grammar, start=start, parser="lalr", transformer=HOLTransformer())

type_parser = get_parser_for("type")
term_parser = get_parser_for("term")
thm_parser = get_parser_for("thm")
inst_parser = get_parser_for("inst")
tyinst_parser = get_parser_for("tyinst")
named_thm_parser = get_parser_for("named_thm")
instsp_parser = get_parser_for("instsp")
var_decl_parser = get_parser_for("var_decl")
ind_constr_parser = get_parser_for("ind_constr")
term_list_parser = get_parser_for("term_list")

def parse_type(s, *, check_type=True):
    """Parse a type."""
    T = type_parser.parse(s)
    if check_type:
        theory.thy.check_type(T)
    return T

def parse_term(s):
    """Parse a term."""
    # Permit parsing a list of strings by concatenating them.
    if isinstance(s, list):
        s = " ".join(s)
    try:
        t = term_parser.parse(s)
        return infertype.type_infer(t)
    except (term.TermException, exceptions.UnexpectedToken, exceptions.UnexpectedCharacters, infertype.TypeInferenceException) as e:
        print("When parsing:", s)
        raise e

def parse_thm(s):
    """Parse a theorem (sequent)."""
    try:
        th = thm_parser.parse(s)
        th.hyps = tuple(infertype.type_infer(hyp) for hyp in th.hyps)
        th.prop = infertype.type_infer(th.prop)
    except (term.TermException, exceptions.UnexpectedToken, exceptions.UnexpectedCharacters, infertype.TypeInferenceException) as e:
        print("When parsing:", s)
        raise e
    return th

def parse_inst(s):
    """Parse a term instantiation."""
    inst = inst_parser.parse(s)
    for k in inst:
        inst[k] = infertype.type_infer(inst[k])
    return inst

def parse_tyinst(s):
    """Parse a type instantiation."""
    return tyinst_parser.parse(s)

def parse_named_thm(s):
    """Parse a named theorem."""
    res = named_thm_parser.parse(s)
    if len(res) == 1:
        return (None, infertype.type_infer(res[0]))
    else:
        return (str(res[0]), infertype.type_infer(res[1]))

def parse_instsp(s):
    """Parse type and term instantiations."""
    tyinst, inst = instsp_parser.parse(s)
    for k in inst:
        inst[k] = infertype.type_infer(inst[k])
    return tyinst, inst

def parse_ind_constr(s):
    """Parse a constructor for an inductive type definition."""
    return ind_constr_parser.parse(s)

def parse_var_decl(s):
    """Parse a variable declaration."""
    return var_decl_parser.parse(s)

def parse_term_list(s):
    """Parse a list of terms."""
    if s == "":
        return []

    ts = term_list_parser.parse(s)
    for i in range(len(ts)):
        ts[i] = infertype.type_infer(ts[i])
    return ts

def parse_args(sig, args):
    """Parse the argument according to the signature."""
    try:
        if sig == None:
            assert args == "", "rule expects no argument."
            return None
        elif sig == str:
            return args
        elif sig == Term:
            return parse_term(args)
        elif sig == macro.Inst:
            return parse_inst(args)
        elif sig == macro.TyInst:
            return parse_tyinst(args)
        elif sig == Tuple[str, Type]:
            s1, s2 = args.split(",", 1)
            return s1, parse_type(s2)
        elif sig == Tuple[str, Term]:
            s1, s2 = args.split(",", 1)
            return s1, parse_term(s2)
        elif sig == Tuple[str, macro.TyInst, macro.Inst]:
            s1, s2 = args.split(",", 1)
            tyinst, inst = parse_instsp(s2)
            tyinst = TyInst(tyinst)
            inst = Inst(inst)
            inst.tyinst = tyinst
            return s1, inst
        elif sig == List[Term]:
            return parse_term_list(args)
        else:
            raise TypeError
    except exceptions.UnexpectedToken as e:
        raise ParserException("When parsing %s, unexpected token %r at column %s.\n"
                              % (args, e.token, e.column))

def parse_proof_rule(data):
    """Parse a proof rule.

    data is a dictionary containing id, rule, args, prevs, and th.
    The result is a ProofItem object.

    This need to be written by hand because different proof rules
    require different parsing of the arguments.

    """
    id, rule = data['id'], data['rule']

    if rule == "":
        return ProofItem(id, "")

    if data['th'] == "":
        th = None
    else:
        th = parse_thm(data['th'])

    sig = theory.thy.get_proof_rule_sig(rule)
    args = parse_args(sig, data['args'])
    return ProofItem(id, rule, args=args, prevs=data['prevs'], th=th)


hol_type.type_parser = parse_type
term.term_parser = parse_term
