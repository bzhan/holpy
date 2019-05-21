# Author: Bohua Zhan

from typing import Tuple
from lark import Lark, Transformer, v_args, exceptions

from kernel.type import HOLType, TVar, Type, TFun, boolT
from kernel.term import Var, Const, Comb, Abs, Bound, Term
from kernel import macro
from kernel.thm import Thm
from kernel.proof import ProofItem, id_force_tuple
from kernel import extension
from logic import induct
from logic import logic
from logic import nat
from logic import list
from logic import function
from logic import set
from syntax import infertype

# import sys,io
# sys.stdout = io.TextIOWrapper(sys.stdout.buffer,encoding='utf-8')


class ParserException(Exception):
    """Exceptions during parsing."""
    def __init__(self, str):
        self.str = str


grammar = r"""
    ?type: "'" CNAME  -> tvar              // Type variable
        | type ("=>"|"⇒") type -> funtype       // Function types
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
        | ("{}"|"∅")               -> empty_set     // Empty set
        | "if" term "then" term "else" term  -> if_expr // if expression
        | "(" term ")(" term ":=" term ("," term ":=" term)* ")"   -> fun_upd // function update
        | "(" term ")"                    // Parenthesis
        | "(" term "::" type ")"   -> typed_term    // Term with specified type

    ?comb: comb atom | atom

    ?times: times "*" comb | comb       // Multiplication: priority 70

    ?inter: inter ("INTER"|"∩") times | times     // Intersection: priority 70

    ?plus: plus "+" inter | inter       // Addition: priority 65

    ?append: plus "@" append | plus     // Append: priority 65

    ?cons: append "#" cons | append     // Cons: priority 65

    ?union: union ("UNION"|"∪") cons | cons       // Union: priority 65

    ?eq: eq "=" union | union           // Equality: priority 50

    ?mem: mem ("MEM"|"∈") mem | eq              // Membership: priority 50

    ?subset: subset ("SUB"|"⊆") subset | mem    // Subset: priority 50

    ?neg: ("~"|"¬") neg -> neg | subset // Negation: priority 40

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

    instsp: tyinst "," inst
    
    type_ind: CNAME ("(" CNAME "::" type ")")*
    
    thm_vars: CNAME "::" type
    

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
            return Const(s, None)
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

    def fun_upd(self, *args):
        def helper(*args):
            if len(args) == 3:
                f, a, b = args
                return Const("fun_upd", None)(f, a, b)
            elif len(args) > 3:
                return helper(helper(*args[:3]), *args[3:])
            else:
                raise TypeError()
        return helper(*args)

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

    def empty_set(self):
        return set.empty_set(None)

    def mem(self, x, A):
        return Const("member", None)(x, A)

    def subset(self, A, B):
        return Const("subset", None)(A, B)

    def inter(self, A, B):
        return Const("inter", None)(A, B)

    def union(self, A, B):
        return Const("union", None)(A, B)

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

    def instsp(self, *args):
        return tuple(args)

    def type_ind(self, *args):
        constrs, vars_list, temp_list = {}, [], []
        constrs['name'] = str(args[0])
        for id in range(1, len(args), 2):
            vars_list.append(str(args[id]))
        constrs['args'] = vars_list
        for id in range(2, len(args), 2):
            temp_list.append(args[id])
        constrs['type'] = temp_list
        return constrs

    def thm_vars(self, *args):
        return (str(args[0]), str(args[1]))

    # def fun_name(self, *args):
    #     return args


def get_parser_for(start):
    return Lark(grammar, start=start, parser="lalr", transformer=HOLTransformer())

type_parser = get_parser_for("type")
term_parser = get_parser_for("term")
thm_parser = get_parser_for("thm")
inst_parser = get_parser_for("inst")
tyinst_parser = get_parser_for("tyinst")
instsp_parser = get_parser_for("instsp")
type_ind_parser = get_parser_for("type_ind")
thm_vars_parser = get_parser_for("thm_vars")
# fun_name_parser = get_parser_for("fun_name")

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
    th.hyps = tuple(infertype.type_infer(thy, ctxt, hyp) for hyp in th.hyps)
    th.prop = infertype.type_infer(thy, ctxt, th.prop)
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

def parse_instsp(thy, ctxt, s):
    """Parse type and term instantiations."""
    parser_setting['thy'] = thy
    tyinst, inst = instsp_parser.parse(s)
    for k in inst:
        inst[k] = infertype.type_infer(thy, ctxt, inst[k])
    return tyinst, inst

def parse_type_ind(thy, s):
    """Parse an inductive definition."""
    parser_setting['thy'] = thy
    return type_ind_parser.parse(s)

def parse_thm_vars(thy, s):
    parser_setting['thy'] = thy
    return thm_vars_parser.parse(s)
#
# def parse_fun_name(thy, s):
#     parser_setting['thy'] = thy
#     return fun_name_parser.parse(s)

def parse_args(thy, ctxt, sig, args):
    """Parse the argument according to the signature."""
    try:
        if sig == None:
            assert args == "", "rule expects no argument."
            return None
        elif sig == str:
            return args
        elif sig == Term:
            return parse_term(thy, ctxt, args)
        elif sig == macro.Inst:
            return parse_inst(thy, ctxt, args)
        elif sig == macro.TyInst:
            return parse_tyinst(thy, args)
        elif sig == Tuple[str, HOLType]:
            s1, s2 = args.split(",", 1)
            return s1, parse_type(thy, s2)
        elif sig == Tuple[str, Term]:
            s1, s2 = args.split(",", 1)
            return s1, parse_term(thy, ctxt, s2)
        elif sig == Tuple[str, macro.TyInst, macro.Inst]:
            s1, s2 = args.split(",", 1)
            tyinst, inst = parse_instsp(thy, ctxt, s2)
            return s1, tyinst, inst
        else:
            raise TypeError()
    except exceptions.UnexpectedToken as e:
        raise ParserException("When parsing %s, unexpected token %r at column %s.\n"
                              % (args, e.token, e.column))

def parse_proof_rule(thy, ctxt, data):
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
        th = parse_thm(thy, ctxt, data['th'])

    sig = thy.get_proof_rule_sig(rule)
    args = parse_args(thy, ctxt, sig, data['args'])
    return ProofItem(id, rule, args=args, prevs=data['prevs'], th=th)

def parse_vars(thy, vars_data):
    ctxt = {}
    for k, v in vars_data.items():
        ctxt[k] = parse_type(thy, v)
    return ctxt

def parse_extension(thy, data):
    """Parse an extension in json format. Returns the resulting
    extension as well as applying it to thy.

    """
    ext = None

    if data['ty'] == 'type.ax':
        ext = extension.TheoryExtension()
        ext.add_extension(extension.AxType(data['name'], len(data['args'])))

    elif data['ty'] == 'def.ax':
        T = parse_type(thy, data['type'])
        ext = extension.TheoryExtension()
        ext.add_extension(extension.AxConstant(data['name'], T))

    elif data['ty'] == 'def':
        T = parse_type(thy, data['type'])
        thy.add_term_sig(data['name'], T)  # Add this first, for parsing later.
        ctxt = parse_vars(thy, data['vars'])
        prop = parse_term(thy, ctxt, data['prop'])
        ext = extension.TheoryExtension()
        ext.add_extension(extension.AxConstant(data['name'], T))
        ext.add_extension(extension.Theorem(data['name'] + "_def", Thm([], prop)))
        ext.add_extension(extension.Attribute(data['name'] + "_def", 'hint_rewrite'))

    elif data['ty'] == 'thm' or data['ty'] == 'thm.ax':
        ctxt = parse_vars(thy, data['vars'])
        prop = parse_term(thy, ctxt, data['prop'])
        ext = extension.TheoryExtension()
        ext.add_extension(extension.Theorem(data['name'], Thm([], prop)))
        if 'hint_backward' in data and data['hint_backward'] == "true":
            ext.add_extension(extension.Attribute(data['name'], 'hint_backward'))
        if 'hint_rewrite' in data and data['hint_rewrite'] == "true":
            ext.add_extension(extension.Attribute(data['name'], 'hint_rewrite'))
        if 'hint_forward' in data and data['hint_forward'] == 'true':
            ext.add_extension(extension.Attribute(data['name'], 'hint_forward'))

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

    elif data['ty'] == 'def.pred':
        T = parse_type(thy, data['type'])
        thy.add_term_sig(data['name'], T)  # Add this first, for parsing later.
        rules = []
        for rule in data['rules']:
            ctxt = parse_vars(thy, rule['vars'])
            prop = parse_term(thy, ctxt, rule['prop'])
            rules.append((rule['name'], prop))
        ext = induct.add_induct_predicate(data['name'], T, rules)

    elif data['ty'] == 'macro':
        ext = extension.TheoryExtension()
        ext.add_extension(extension.Macro(data['name']))

    elif data['ty'] == 'method':
        ext = extension.TheoryExtension()
        ext.add_extension(extension.Method(data['name']))

    if ext:
        thy.unchecked_extend(ext)

    return None

def parse_extensions(thy, data):
    """Parse a list of extensions to thy in sequence."""
    for ext_data in data:
        parse_extension(thy, ext_data)
