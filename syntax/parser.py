# Author: Bohua Zhan

from lark import Lark, Transformer, v_args, exceptions

from kernel.type import TVar, Type, TFun, hol_bool
from kernel.term import Var, Const, Comb, Abs, Bound, Term
from kernel.macro import MacroSig
from kernel.thm import Thm
from kernel.proof import ProofItem
from kernel import extension
from logic import induct
from logic import logic
from logic import nat
from logic import list
from syntax import infertype


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
        | INT -> number                   // Numbers
        | ("%"|"λ") CNAME "::" type ". " term -> abs     // Abstraction
        | ("%"|"λ") CNAME ". " term           -> abs_notype
        | ("!"|"∀") CNAME "::" type ". " term -> all     // Forall quantification
        | ("!"|"∀") CNAME ". " term           -> all_notype
        | ("?"|"∃") CNAME "::" type ". " term -> exists  // Exists quantification
        | ("?"|"∃") CNAME ". " term           -> exists_notype
        | "[]"                     -> literal_list  // Empty list
        | "[" term ("," term)* "]" -> literal_list  // List
        | "if" term "then" term "else" term  -> if_expr // if expression
        | "(" term ")"                    // Parenthesis
        | "(" term "::" type ")"   -> typed_term    // Term with specified type

    ?comb: comb atom | atom

    ?times: times "*" comb | comb       // Multiplication: priority 70

    ?plus: plus "+" times | times       // Addition: priority 65

    ?append: plus "@" append | plus     // Append: priority 65

    ?cons: append "#" cons | append     // Cons: priority 65

    ?eq: eq "=" cons | cons             // Equality: priority 50

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

    %import common.CNAME
    %import common.WS
    %import common.INT

    %ignore WS
"""

# Modifiable settings in the transformation part of the parser.
# This includes thy and ctxt.
parser_setting = dict()

@v_args(inline=True)
class HOLTransformer(Transformer):
    def __init__(self):
        pass

    def tvar(self, s):
        return TVar(s)

    def type(self, *args):
        return Type(str(args[-1]), *args[:-1])

    def funtype(self, t1, t2):
        return TFun(t1, t2)

    def vname(self, s):
        thy = parser_setting['thy']
        s = str(s)
        if thy.has_term_sig(s):
            # s is the name of a constant in the theory
            return Const(s, thy.get_term_sig(s))
        else:
            # s not found, either bound or free variable
            return Var(s, None)

    def typed_term(self, t, T):
        t.T = T
        return t

    def number(self, n):
        return nat.to_binary(int(n))

    def literal_list(self, *args):
        return list.mk_literal_list(args, None)

    def if_expr(self, P, x, y):
        return Const("IF", None)(P, x, y)

    def comb(self, fun, arg):
        return Comb(fun, arg)

    def abs(self, var_name, T, body):
        return Abs(var_name, T, body.abstract_over(Var(var_name, None)))

    def abs_notype(self, var_name, body):
        return Abs(var_name, None, body.abstract_over(Var(var_name, None)))

    def all(self, var_name, T, body):
        all_t = Const("all", None)
        return all_t(Abs(var_name, T, body.abstract_over(Var(var_name, None))))

    def all_notype(self, var_name, body):
        all_t = Const("all", None)
        return all_t(Abs(var_name, None, body.abstract_over(Var(var_name, None))))

    def exists(self, var_name, T, body):
        exists_t = Const("exists", None)
        return exists_t(Abs(var_name, T, body.abstract_over(Var(var_name, None))))

    def exists_notype(self, var_name, body):
        exists_t = Const("exists", None)
        return exists_t(Abs(var_name, None, body.abstract_over(Var(var_name, None))))

    def times(self, lhs, rhs):
        return nat.times(lhs, rhs)

    def plus(self, lhs, rhs):
        return nat.plus(lhs, rhs)

    def append(self, lhs, rhs):
        return Const("append", None)(lhs, rhs)

    def cons(self, lhs, rhs):
        return Const("cons", None)(lhs, rhs)

    def eq(self, lhs, rhs):
        return Const("equals", None)(lhs, rhs)

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

def get_parser_for(start):
    return Lark(grammar, start=start, parser="lalr", transformer=HOLTransformer())

type_parser = get_parser_for("type")
term_parser = get_parser_for("term")
thm_parser = get_parser_for("thm")
inst_parser = get_parser_for("inst")
tyinst_parser = get_parser_for("tyinst")

def parse_type(thy, s):
    """Parse a type."""
    parser_setting['thy'] = thy
    return type_parser.parse(s)

def parse_term(thy, ctxt, s):
    """Parse a term."""
    parser_setting['thy'] = thy
    t = term_parser.parse(s)
    return infertype.type_infer(thy, ctxt, t)

def parse_thm(thy, ctxt, s):
    """Parse a theorem (sequent)."""
    parser_setting['thy'] = thy
    th = thm_parser.parse(s)
    th.assums = set(infertype.type_infer(thy, ctxt, assum) for assum in th.assums)
    th.concl = infertype.type_infer(thy, ctxt, th.concl)
    return th

def parse_inst(thy, ctxt, s):
    """Parse a term instantiation."""
    parser_setting['thy'] = thy
    inst = inst_parser.parse(s)
    for k in inst:
        inst[k] = infertype.type_infer(thy, ctxt, inst[k])
    return inst

def parse_tyinst(thy, s):
    """Parse a type instantiation."""
    parser_setting['thy'] = thy
    return tyinst_parser.parse(s)

def split_proof_rule(s):
    """Split proof rule into parseable parts.

    Currently able to handle string of the form:
    [id]: [rule] [args] by [prevs]

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
        rule, rest = rest.split(" ", 1)  # split off name of rule
    else:
        rule, rest = rest, ""
    rule = rule.strip()

    if rest.count("from") > 0:
        args, rest = rest.split("from", 1)
        return {'id': id, 'rule': rule, 'args': args.strip(),
                'prevs': [prev.strip() for prev in rest.split(",")],
                'th': th}
    else:
        return {'id': id, 'rule': rule, 'args': rest.strip(),
                'prevs': [], 'th': th}

def parse_proof_rule_from_data(thy, ctxt, data):
    """Parse a proof rule.

    data is a dictionary as provided by split_proof_rule. The result
    is a ProofItem object.

    This need to be written by hand because different proof rules
    require different parsing of the arguments.

    """
    id, rule, args, prevs, th = data['id'], data['rule'], data['args'], data['prevs'], data['th']

    if rule == "":
        return ProofItem(id, "")

    if th == "":
        th = None
    else:
        th = parse_thm(thy, ctxt, th)

    try:
        sig = thy.get_proof_rule_sig(rule)
        if sig == MacroSig.NONE:
            assert args == "", "rule expects no argument."
            return ProofItem(id, rule, prevs=prevs, th=th)
        elif sig == MacroSig.STRING:
            return ProofItem(id, rule, args=args, prevs=prevs, th=th)
        elif sig == MacroSig.TERM:
            t = parse_term(thy, ctxt, args)
            return ProofItem(id, rule, args=t, prevs=prevs, th=th)
        elif sig == MacroSig.INST:
            inst = parse_inst(thy, ctxt, args)
            return ProofItem(id, rule, args=inst, prevs=prevs, th=th)
        elif sig == MacroSig.TYINST:
            tyinst = tyinst_parser(thy, ctxt).parse(args)
            return ProofItem(id, rule, args=tyinst, prevs=prevs, th=th)
        elif sig == MacroSig.STRING_TERM:
            s1, s2 = args.split(",", 1)
            t = parse_term(thy, ctxt, s2)
            return ProofItem(id, rule, args=(s1, t), prevs=prevs, th=th)
        elif sig == MacroSig.STRING_INST:
            s1, s2 = args.split(",", 1)
            inst = parse_inst(thy, ctxt, s2)
            return ProofItem(id, rule, args=(s1, inst), prevs=prevs, th=th)
        else:
            raise TypeError()
    except exceptions.UnexpectedToken as e:
        raise ParserException("When parsing %s, unexpected token %r at column %s.\n"
                              % (args, e.token, e.column))

def parse_proof_rule(thy, ctxt, s):
    data = split_proof_rule(s)
    return parse_proof_rule_from_data(thy, ctxt, data)

def parse_vars(thy, vars_data):
    ctxt = {}
    for k, v in vars_data.items():
        ctxt[k] = parse_type(thy, v)
    return ctxt

def parse_extension(thy, data):
    """Parse an extension in json format. Returns the resulting
    extension as well as applying it to thy.

    """
    if data['ty'] == 'def.ax':
        prop = parse_type(thy, data['T'])
        ext = extension.TheoryExtension()
        ext.add_extension(extension.AxConstant(data['name'], prop))

    elif data['ty'] == 'thm':
        ctxt = parse_vars(thy, data['vars'])
        prop = parse_term(thy, ctxt, data['prop'])
        ext = extension.TheoryExtension()
        ext.add_extension(extension.Theorem(data['name'], Thm([], prop)))

    elif data['ty'] == 'type.ind':
        constrs = []
        for constr in data['constrs']:
            T = parse_type(thy, constr['type'])
            constrs.append((constr['name'], T, constr['args']))
        ext = induct.add_induct_type(data['name'], data['args'], constrs)

    elif data['ty'] == 'def.ind':
        T = parse_type(thy, data['type'])
        thy.add_term_sig(data['name'], T)  # Add this first, for parsing later.
        rules = []
        for rule in data['rules']:
            ctxt = parse_vars(thy, rule['vars'])
            prop = parse_term(thy, ctxt, rule['prop'])
            rules.append(prop)
        ext = induct.add_induct_def(data['name'], T, rules)

    elif data['ty'] == 'macro':
        ext = extension.TheoryExtension()
        ext.add_extension(extension.Macro(data['name']))

    thy.unchecked_extend(ext)
    return ext

def parse_extensions(thy, data):
    """Parse a list of extensions to thy in sequence. Returns the
    resulting list of extensions.

    """
    exts = []
    for ext_data in data:
        exts.append(parse_extension(thy, ext_data))
    return exts

