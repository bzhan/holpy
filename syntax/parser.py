# Author: Bohua Zhan

from lark import Lark, Transformer, v_args, exceptions

from kernel.type import TVar, Type, TFun, hol_bool
from kernel.term import Var, Const, Comb, Abs, Bound, Term
from kernel.macro import MacroSig
from kernel.thm import Thm
from kernel.proof import ProofItem
from kernel.extension import AxType, AxConstant, Theorem, TheoryExtension
from logic import induct, logic
from logic.nat import Nat
from logic.list import List

def _abstract_over_name(t, name, n):
    """Helper function for abstract_over_name. Here t is an open term.
    All atomic terms with the given name should be replaced by Bound n.

    """
    if t.ty == Term.VAR or t.ty == Term.CONST:
        if t.name == name:
            return Bound(n)
        else:
            return t
    elif t.ty == Term.COMB:
        return Comb(_abstract_over_name(t.fun, name, n), _abstract_over_name(t.arg, name, n))
    elif t.ty == Term.ABS:
        return Abs(t.var_name, t.T, _abstract_over_name(t.body, name, n+1))
    elif t.ty == Term.BOUND:
        return t
    else:
        raise TypeError()

def abstract_over_name(t, name, T):
    """Abstract over all atomic terms with the given name."""
    return Abs(name, T, _abstract_over_name(t, name, 0))


class ParserException(Exception):
    """Exceptions during parsing."""
    def __init__(self, str):
        self.str = str


grammar = r"""
    ?type: "'" CNAME -> tvar              // Type variable
        | type "=>" type -> funtype       // Function types
        | CNAME -> type                   // Type constants
        | type CNAME                      // Type constructor with one argument
        | "(" type ("," type)* ")" CNAME  // Type constructor with multiple arguments
        | "(" type ")"                    // Parenthesis

    ?atom: CNAME -> vname                 // Constant, variable, or bound variable
        | "0" -> zero                     // Zero (to be extended to numbers)
        | ("%"|"λ") CNAME "::" type ". " term -> abs     // Abstraction
        | ("!"|"∀") CNAME "::" type ". " term -> all     // Forall quantification
        | ("?"|"∃") CNAME "::" type ". " term -> exists   // Exists quantification
        | "(" term ")"                    // Parenthesis

    ?comb: comb atom | atom

    ?times: times "*" comb | comb       // Multiplication: priority 70

    ?plus: plus "+" times | times       // Addition: priority 65

    ?append: plus "@" append | plus     // Append: priority 65

    ?eq: eq "=" append | append         // Equality: priority 50

    ?neg: ("~"|"¬") neg -> neg | eq     // Negation: priority 40 

    ?conj: neg ("&"|"∧") conj | neg     // Conjunction: priority 35

    ?disj: conj ("|"|"∨") disj | conj   // Disjunction: priority 30

    ?imp: disj ("-->"|"⟶") imp | disj  // Implies: priority 25

    ?term: imp

    thm: ("|-"|"⊢") term
        | term ("," term)* ("|-"|"⊢") term

    term_pair: CNAME ":" term

    inst: "{}"
        | "{" term_pair ("," term_pair)* "}"

    type_pair: CNAME ":" type

    tyinst: "{}"
        | "{" type_pair ("," type_pair)* "}"

    var_decl: "var" CNAME "::" type

    %import common.CNAME
    %import common.WS

    %ignore WS
"""

type_parser = Lark(grammar, start="type", parser="lalr")
term_parser = Lark(grammar, start="term", parser="lalr")
thm_parser = Lark(grammar, start="thm", parser="lalr")
inst_parser = Lark(grammar, start="inst", parser="lalr")
tyinst_parser = Lark(grammar, start="tyinst", parser="lalr")
var_decl_parser = Lark(grammar, start="var_decl", parser="lalr")

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

    def zero(self):
        return Const("zero", Nat.nat)

    def comb(self, fun, arg):
        return Comb(fun, arg)

    def abs(self, var_name, T, body):
        # Bound variables should be represented by Var(var_name, None).
        # Abstract over it, and remember to change the type to T.
        t = abstract_over_name(body, var_name, T)
        return Abs(var_name, T, t.body)

    def all(self, var_name, T, body):
        # Similar parsing mechanism as for abs.
        all_t = Const("all", TFun(TFun(T, hol_bool), hol_bool))
        t = abstract_over_name(body, var_name, T)
        return all_t(t)

    def exists(self, var_name, T, body):
        # Similar parsing mechanism as for abs.
        exists_t = Const("exists", TFun(TFun(T, hol_bool), hol_bool))
        t = abstract_over_name(body, var_name, T)
        return exists_t(t)

    def times(self, lhs, rhs):
        return Nat.times(lhs, rhs)

    def plus(self, lhs, rhs):
        return Nat.plus(lhs, rhs)

    def append(self, lhs, rhs):
        return List.append(lhs, rhs)

    def eq(self, lhs, rhs):
        return Term.mk_equals(lhs, rhs)

    def neg(self, t):
        return logic.neg(t)

    def conj(self, s, t):
        return logic.mk_conj(s, t)

    def disj(self, s, t):
        return logic.mk_disj(s, t)

    def imp(self, s, t):
        return Term.mk_implies(s, t)

    def thm(self, *args):
        return Thm(args[:-1], args[-1])

    def term_pair(self, name, T):
        return (name, T)

    def type_pair(self, name, T):
        return (name, T)

    def inst(self, *args):
        return dict(args)

    def tyinst(self, *args):
        return dict(args)

    def var_decl(self, name, T):
        return (name, T)

def parse_type(thy, s):
    """Parse a type."""
    return HOLTransformer(thy).transform(type_parser.parse(s))

def parse_term(thy, ctxt, s):
    """Parse a term."""
    return HOLTransformer(thy, ctxt).transform(term_parser.parse(s))

def parse_thm(thy, ctxt, s):
    """Parse a theorem (sequent)."""
    return HOLTransformer(thy, ctxt).transform(thm_parser.parse(s))

def parse_inst(thy, ctxt, s):
    """Parse a term instantiation."""
    return HOLTransformer(thy, ctxt).transform(inst_parser.parse(s))

def parse_tyinst(thy, s):
    """Parse a type instantiation."""
    return HOLTransformer(thy).transform(tyinst_parser.parse(s))

def parse_var_decl(thy, s):
    """Parse a variable declaration."""
    return HOLTransformer(thy).transform(var_decl_parser.parse(s))

def split_proof_rule(s):
    """Split proof rule into parseable parts.

    Currently able to handle string of the form:
    [id]: [rule_name] [args] by [prevs]

    """
    if s.count(": ") > 0:
        id, rest = s.split(": ", 1)  # split off id
    else:
        raise ParserException("id not found: " + s)

    id = id.strip()
    if rest.count(" by ") > 0:
        th, rest = rest.split(" by ", 1)
    else:
        th, rest = "", rest

    if rest.count(" ") > 0:
        rule_name, rest = rest.split(" ", 1)  # split off name of rule
    else:
        rule_name, rest = rest, ""
    rule_name = rule_name.strip()

    if rest.count("from") > 0:
        args, rest = rest.split("from", 1)
        return (id, rule_name, args.strip(), [prev.strip() for prev in rest.split(",")], th)
    else:
        return (id, rule_name, rest.strip(), [], th)

def parse_proof_rule(thy, ctxt, s):
    """Parse a proof rule.

    This need to be written by hand because different proof rules
    require different parsing of the arguments.

    """
    (id, rule_name, args, prevs, th) = split_proof_rule(s)

    if rule_name == "":
        return ProofItem(id, "")

    if th == "":
        th = None
    else:
        th = parse_thm(thy, ctxt, th)

    try:
        sig = thy.get_proof_rule_sig(rule_name)
        if sig == MacroSig.NONE:
            assert args == "", "rule expects no argument."
            return ProofItem(id, rule_name, prevs=prevs, th=th)
        elif sig == MacroSig.STRING:
            return ProofItem(id, rule_name, args=args, prevs=prevs, th=th)
        elif sig == MacroSig.TERM:
            t = parse_term(thy, ctxt, args)
            return ProofItem(id, rule_name, args=t, prevs=prevs, th=th)
        elif sig == MacroSig.INST:
            inst = parse_inst(thy, ctxt, args)
            return ProofItem(id, rule_name, args=inst, prevs=prevs, th=th)
        elif sig == MacroSig.TYINST:
            tyinst = tyinst_parser(thy, ctxt).parse(args)
            return ProofItem(id, rule_name, args=tyinst, prevs=prevs, th=th)
        elif sig == MacroSig.STRING_TERM:
            s1, s2 = args.split(",", 1)
            t = parse_term(thy, ctxt, s2)
            return ProofItem(id, rule_name, args=(s1, t), prevs=prevs, th=th)
        elif sig == MacroSig.STRING_INST:
            s1, s2 = args.split(",", 1)
            inst = parse_inst(thy, ctxt, s2)
            return ProofItem(id, rule_name, args=(s1, inst), prevs=prevs, th=th)
        else:
            raise TypeError()
    except exceptions.UnexpectedToken as e:
        raise ParserException("When parsing %s, unexpected token %r at column %s.\n"
                              % (args, e.token, e.column))

def parse_vars(thy, vars_data):
    ctxt = {}
    for k, v in vars_data.items():
        ctxt[k] = parse_type(thy, v)
    return ctxt

def parse_extension(thy, data):
    if data['ty'] == 'def.ax':
        prop = parse_type(thy, data['T'])
        thy.extend_axiom_constant(
            AxConstant(data['name'], prop))
        return prop
    elif data['ty'] == 'thm':
        ctxt = parse_vars(thy, data['vars'])
        prop = parse_term(thy, ctxt, data['prop'])
        thy.add_theorem(data['name'], Thm([], prop))
        return prop
    elif data['ty'] == 'type.ind':
        constrs = []
        list = []
        for constr in data['constrs']:
            T = parse_type(thy, constr['type'])
            constrs.append((constr['name'], T, constr['args']))
            list.append(T)
        ext = induct.add_induct_type(data['name'], data['args'], constrs)
        thy.unchecked_extend(ext)
        return list
    elif data['ty'] == 'def.ind':
        T = parse_type(thy, data['type'])
        thy.add_term_sig(data['name'], T)  # Add this first, for parsing later.
        rules = []
        for rule in data['rules']:
            ctxt = parse_vars(thy, rule['vars'])
            prop = parse_term(thy, ctxt, rule['prop'])
            rules.append(prop)
        ext = induct.add_induct_def(data['name'], T, rules)
        thy.unchecked_extend(ext)
        return rules

def parse_extensions(thy, data):
    for ext_data in data:
        parse_extension(thy, ext_data)
