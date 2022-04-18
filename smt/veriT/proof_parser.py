from typing import Iterable
from lark import Lark, Transformer, v_args, exceptions
from smt.veriT.command import Assume, Step, Anchor
from logic.logic import mk_if
from kernel import term as hol_term
from kernel import type as hol_type
from data import list as hol_list

class VeriTParseException(Exception):
    def __init__(self, tm_name, message) -> None:
        self.tm_name = tm_name
        self.message = message
    
    def __str__(self) -> str:
        return "%s: %s" % (self.tm_name, self.message)

def str_to_hol_type(s):
        """Convert string to HOL type."""
        s = str(s)
        if s == "Bool":
            return hol_type.BoolType
        elif s == "Int":
            return hol_type.IntType
        elif s == "Real":
            return hol_type.RealType
        else:
            # All other types are converted to type variables.
            return hol_type.TVar(s)


# Grammar of SMT-LIB language
smt_decl_grammar = r"""
    VNAME: ("_" | LETTER | "|" | "*" | "+" | "-" | "<" | ">" | "/" | "=" | ":" | "@")("_"|LETTER|DIGIT|"$"|"." | "|" | "*" | "+" | "-" | "<" | ">" | "/" | "=" | ":" | "@")*

    ?term: "(declare-fun" VNAME "()" VNAME ")" -> mk_tm
        | "(declare-fun" VNAME "(" VNAME+ ")" VNAME ")" -> mk_fun

    %import common.CNAME
    %import common.INT
    %import common.DIGIT
    %import common.LETTER
    %import common.DECIMAL
    %import common.WS
    %import common.NUMBER
    %ignore WS
"""
@v_args(inline=True)
class DeclTransformer(Transformer):
    """A parser for declaration in SMT-LIB."""
    def __init__(self):
        pass

    def mk_tm(self, name, ty):
        "Make a term: name :: ty"
        return {name.value: str_to_hol_type(ty)}

    def mk_fun(self, name, *args):
        """Make a function term, which type is arg1 -> ... argn."""
        return {name.value: hol_type.TFun(*(str_to_hol_type(t) for t in args))}

decl_parser = Lark(smt_decl_grammar, start="term", parser="lalr", transformer=DeclTransformer())

def parse_decl(s):
    return decl_parser.parse(s)
# Grammar of Alethe proof
veriT_grammar = r"""
    VNAME: ("_" | LETTER | "|" | "*" | "+" | "-" | "<" | ">" | "/" | "=")("_"|LETTER|DIGIT|"$"|"." | "|" | "*" | "+" | "-" | "<" | ">" | "/" | "=")*

    ANCHOR_NAME: "?" CNAME | "veriT_" CNAME

    ?proof_command : "(assume" step_id proof_term ")" -> mk_assume
                    | "(step" step_id clause ":rule" CNAME step_annotation? ")" -> mk_step
                    | "(anchor :step" step_id ":args" "(" single_context+ ")" ")" -> mk_anchor
                    | "(anchor :step" step_id ")" -> mk_empty_anchor
    ?clause : "(cl" proof_term* ")" -> mk_clause
    
    ?single_context :  "(:=" "(" ANCHOR_NAME VNAME ")" (term|VNAME) ")" -> add_context
                    | "(" CNAME VNAME ")" -> add_trivial_ctx

    ?step_arg_pair : "(:=" "veriT_"  CNAME VNAME")" -> mk_arg_pair

    ?step_annotation : ":premises" "(" step_id+ ")" -> mk_step_premises
                    | ":args" "(" step_arg_pair+ ")" -> mk_step_args
                    | ":discharge" "(" CNAME* ")" -> mk_discharge

    ?proof_term : term

    ?let_pair : "(" "?" CNAME term ")" -> mk_let_pair

    ?quant_pair : "(" "?" CNAME VNAME ")" -> mk_quant_pair_assume
                | "(" "veriT_" CNAME VNAME ")" -> mk_quant_pair_step

    ?term :   "true" -> mk_true
            | "false" -> mk_false
            | "(not" term ")" -> mk_neg_tm
            | "(or" term+ ")" -> mk_disj_tm
            | "(and" term+ ")" -> mk_conj_tm
            | "(=>" term term ")" -> mk_impl_tm
            | "(=" term term ")" -> mk_eq_tm
            | "(!" term ":named" "@" CNAME ")" -> mk_annot_tm
            | "(let" "(" let_pair* ")" term ")" -> mk_let_tm
            | "(distinct" term term+ ")" -> mk_distinct_tm
            | "(" term ")" -> mk_par_tm
            | "(" term+ ")" -> mk_app_tm
            | "(ite" term term term ")" -> mk_ite_tm
            | "(forall" "(" quant_pair+ ")" term ")" -> mk_forall
            | "(exists" "(" quant_pair+ ")" term ")" -> mk_exists
            | name

    ?step_id : VNAME ("." VNAME)* -> mk_step_id

    ?name : "@" CNAME -> ret_annot_tm
            | "?" CNAME -> ret_let_tm
            | VNAME -> ret_tm

    %import common.CNAME
    %import common.INT
    %import common.DIGIT
    %import common.LETTER
    %import common.DECIMAL
    %import common.WS
    %import common.NUMBER
    %ignore WS
"""

@v_args(inline=True)
class ProofTransformer(Transformer):
    """A parser for alethe proof grammar.
    
    ctx: map symbols to higher-order terms
    """
    def __init__(self, smt_file_ctx):
        # context derived from .smt2 file.
        self.smt_file_ctx = smt_file_ctx

        # map from annotation to term
        # annotation is just syntactic substitution
        self.annot_tm = dict()

        # map from local variables to terms
        self.let_tm = dict()

        # store anchor context
        self.proof_ctx = []

        # Map from step name to its context
        self.step_ctx = dict()

        # current subproof id
        self.cur_subprf_id = []

        # map from quantified variable name to variable
        self.quant_ctx = dict()

        # map from (quantified) verit_-prefix name to term
        self.verit_ctx = dict()

        # map from anchor variable to term
        self.anchor_ctx = dict()

    def add_context(self, var, ty, tm_name):
        """return the new variables and the assigned term
        var is the variable name, ty is its type, tm_name is
        the term name (may not occur in previous context)
        """
        
        hol_ty = str_to_hol_type(ty.value)
        if isinstance(tm_name, hol_term.Term):
            tm = tm_name
        else:
            tm = hol_term.Var(tm_name.value, hol_ty)
            self.anchor_ctx[tm_name] = tm
        
        var_name = var.value
            
        assert tm.get_type() == hol_ty
        return var_name, tm

    def add_trivial_ctx(self, var, ty):
        return tuple()

    def ret_annot_tm(self, name):
        """Return the term which is represented by a unique @-prefix name."""
        name = "@" + str(name)
        return self.annot_tm[name]

    def ret_let_tm(self, name):
        """There are two kinds of occursion of ?name in proof.
        1. let expression : (let (?x 1) ?x + 1)
        2. anchor context: (:= (?x I) term)
        3. quantified variable: (forall (?x t). ?x)
        We first search ?name in let scope then in quantified variables, then in context, 
        this is correct since if ?name is not a binding var, the let scope would be empty. 
        """
        name = "?" + str(name)
        if len(self.let_tm) > 0 and name in self.let_tm:
            return self.let_tm[name]
        
        elif len(self.quant_ctx) > 0 and name in self.quant_ctx:
            return self.quant_ctx[name]
        else:
            for ctx in self.proof_ctx:
                if name in ctx:
                    return hol_term.Var(name, ctx[name].get_type())

        raise VeriTParseException("ret_let_tm", "can't find ?var_name")

    def ret_tm(self, tm):
        tm = str(tm)
        if tm.startswith("veriT_"):
            if tm in self.verit_ctx:
                return self.verit_ctx[tm]
            elif tm in self.anchor_ctx:
                return self.anchor_ctx[tm]
            else:
                print(self.verit_ctx)
                print(self.anchor_ctx)
                raise KeyError(tm)
        if tm in self.smt_file_ctx:
            return hol_term.Var(tm, self.smt_file_ctx[str(tm)])
        raise ValueError(tm)

    def mk_par_tm(self, tm):
        return tm

    def mk_app_tm(self, *tms):
        return tms[0](*tms[1:])

    def mk_quant_pair_assume(self, var_name, ty):
        var_name = "?" + str(var_name)
        hol_var = hol_term.Var(var_name, hol_type.TVar(str(ty)))
        self.quant_ctx[var_name] = hol_var
        return hol_var

    def mk_quant_pair_step(self, var_name, ty):
        var_name = "veriT_" + str(var_name)
        hol_var = hol_term.Var(var_name, hol_type.TVar(str(ty)))
        self.verit_ctx[var_name] = hol_var
        return hol_var

    def mk_forall(self, *tms):
        self.quant_ctx.clear()
        return hol_term.Forall(*tms)

    def mk_exists(self, *tms):
        self.quant_ctx.clear()
        try:
            return hol_term.Exists(*tms)
        except:
            print("tms")
            for tm in tms:
                print(repr(tm))
            raise NotImplementedError

    def mk_let_pair(self, name, tm):
        """Make the let scope."""
        name = "?" + str(name)
        T = tm.get_type()
        bound_var = hol_term.Var(name, T)
        self.let_tm[name] = bound_var
        return bound_var, T, tm

    def mk_step_args(self, name, tm):
        assert str(name) in self.verit_ctx  and str(tm) in self.smt_file_ctx
        return self.verit_ctx[str(name)] and self.smt_file_ctx[str(tm)]

    def mk_let_tm(self, *tms):
        """Represent the let expression as a lambda term.
        
        - bounds: a list of binding pairs
        - lbd_tm: the function body
        The let scope will be cleared when the let-expression is closed.
        """
        self.let_tm.clear()
        return tms[-1]

    def mk_distinct_tm(self, *tms):
        assert tms  # tms cannot be empty
        return hol_list.distinct(hol_list.mk_literal_list(tms, tms[0].get_type()))

    def mk_true(self):
        return hol_term.true

    def mk_false(self):
        return hol_term.false

    def mk_neg_tm(self, tm):
        return hol_term.Not(tm)

    def mk_annot_tm(self, tm, name):
        name = "@" + str(name)
        self.annot_tm[name] = tm
        return tm

    def mk_disj_tm(self, *tms):
        disj_tm = hol_term.Or(*tms)
        disj_tm.arity = len(tms)
        return disj_tm

    def mk_conj_tm(self, *tms):
        conj_tm = hol_term.And(*tms)
        conj_tm.arity = len(tms)
        return conj_tm

    def mk_impl_tm(self, *tms):
        return hol_term.Implies(*tms)

    def mk_eq_tm(self, *tms):
        return hol_term.Eq(*tms)

    def mk_ite_tm(self, P, x, y):
        return mk_if(P, x, y)

    def mk_step_id(self, *step_id):
        return ''.join(step_id)

    def mk_assume(self, assm_id, tm):
        assm_step = Assume(assm_id, tm)
        self.quant_ctx.clear()
        return assm_step

    def mk_anchor(self, id, *ctx):
        """Every anchor (with ctx) will create a new context."""
        new_ctx = {}
        for var, tm in ctx:
            new_ctx[var] = tm
            new_ctx[str(tm)] = tm
        self.proof_ctx.append(new_ctx)
        prf_ctx = {var_name : tm for ctx in self.proof_ctx for var_name, tm in ctx.items()}
        step = Anchor(str(id), prf_ctx)
        self.cur_subprf_id.append(str(id))
        return step

    def mk_empty_anchor(self, id):
        self.proof_ctx.append(dict())
        step = Anchor(str(id), dict())
        self.cur_subprf_id.append(str(id))
        return step

    def mk_step(self, step_id, cl, rule_name, pm=None):
        # make context of current step
        # Context created by anchor
        step_ctx = {var_name:tm for ctx in self.proof_ctx for var_name, tm in ctx.items()}
        
        # if current step meets subproof id, pop the last context
        if len(self.cur_subprf_id) and self.cur_subprf_id[-1] == step_id:
            self.cur_subprf_id.pop()
            self.proof_ctx.pop()

        # if there is no anchor context, the step should not be in a subproof
        assert self.cur_subprf_id or len(self.proof_ctx) == 0

        # clear quantifier context
        self.verit_ctx.clear()
        self.anchor_ctx.clear()

        # Make new step
        return Step(step_id, rule_name, cl, pm, step_ctx)

    def mk_clause(self, *tm):
        return tm

    def mk_step_premises(self, *pm):
        return pm

    def mk_step_args(self, *args):
        return args

    def mk_discharge(self, *steps):
        return steps

def proof_parser(ctx):
    return Lark(veriT_grammar, start="proof_command", parser="lalr", transformer=ProofTransformer(smt_file_ctx=ctx))

