from typing import Iterable, Union
from lark import Lark, Transformer, v_args, exceptions
from smt.veriT.command import Assume, Step, Anchor
from logic import logic
from kernel import term as hol_term
from kernel import type as hol_type
from data import list as hol_list
from fractions import Fraction

PREMISES, ARGS, DISCHARGE = range(3)

class VeriTParseException(Exception):
    def __init__(self, tm_name, message) -> None:
        self.tm_name = tm_name
        self.message = message
    
    def __str__(self) -> str:
        return "%s: %s" % (self.tm_name, self.message)

def str_to_hol_type(s: Union[hol_type.Type, str]) -> hol_type.Type:
        """Convert string to HOL type."""
        if isinstance(s, hol_type.Type):
            return s
        s = str(s)
        if s == "Bool":
            return hol_type.BoolType
        elif s == "Int":
            return hol_type.IntType
        elif s == "Real":
            return hol_type.RealType
        elif s == "ArrayIntInt":
            return hol_type.TFun(hol_type.IntType, hol_type.IntType)
        else:
            # All other types are converted to type variables.
            return hol_type.TVar(s)


# Grammar of SMT-LIB language
smt_decl_grammar = r"""
    VNAME: (LETTER|"~"|"!"|"$"|"%"|"^"|"&"|"*"|"_"|"-"|"+"|"="|"<"|">"|"."|"/")(LETTER|DIGIT|"~"|"!"|"@"|"$"|"%"|"^"|"&"|"*"|"_"|"-"|"+"|"="|"<"|">"|"."|"?"|"/")*

    QUOTED_VNAME: "|" (LETTER|DIGIT|"~"|"!"|"@"|"$"|"%"|"^"|"&"|"*"|"_"|"-"|"+"|"="|"<"|">"|"."|"?"|"/"|"("|")"|":"|"["|"]"|"#"|","|"'"|" ")* "|"

    ?vname: VNAME -> mk_vname
        | QUOTED_VNAME -> mk_quoted_vname
        | "(Array " VNAME VNAME ")" -> mk_array

    ?term: "(declare-fun" vname "()" vname ")" -> mk_tm
        | "(declare-fun" vname "(" vname+ ")" vname ")" -> mk_fun

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

    def mk_vname(self, name):
        return str(name)

    def mk_quoted_vname(self, name):
        name = str(name)
        assert name[0] == '|' and name[-1] == '|'
        return name[1:-1]

    def mk_tm(self, name, ty):
        "Make a term: name :: ty"
        return {name: str_to_hol_type(ty)}

    def mk_fun(self, name, *args):
        """Make a function term, which type is arg1 -> ... argn."""
        return {name: hol_type.TFun(*(str_to_hol_type(t) for t in args))}

    def mk_array(self, domain, codomain):
        return hol_type.TFun(str_to_hol_type(domain), str_to_hol_type(codomain))

decl_parser = Lark(smt_decl_grammar, start="term", parser="lalr", transformer=DeclTransformer())

def parse_decl(s):
    return decl_parser.parse(s)

# Grammar of Alethe proof
veriT_grammar = r"""
    VNAME: (LETTER|"~"|"!"|"$"|"%"|"^"|"&"|"*"|"_"|"-"|"+"|"="|"<"|">"|"."|"/")(LETTER|DIGIT|"~"|"!"|"@"|"$"|"%"|"^"|"&"|"*"|"_"|"-"|"+"|"="|"<"|">"|"."|"?"|"/")*

    QUOTED_VNAME: "|"(LETTER|DIGIT|"~"|"!"|"@"|"$"|"%"|"^"|"&"|"*"|"_"|"-"|"+"|"="|"<"|">"|"."|"?"|"/"|"("|")"|":"|"["|"]"|"#"|","|"'"|" ")*"|"

    ?at_name : "@" CNAME -> mk_at_name

    ?vname: VNAME -> mk_vname
        | QUOTED_VNAME -> mk_quoted_vname
    
    ?qname: "?" VNAME -> mk_qname

    ?anchor_name: qname | vname

    ?proof_command : "(assume" step_id proof_term ")" -> mk_assume
                    | "(step" step_id clause ":rule" CNAME step_annotation* ")" -> mk_step
                    | "(anchor :step" step_id ":args" "(" single_context+ ")" ")" -> mk_anchor
                    | "(anchor :step" step_id ")" -> mk_empty_anchor

    ?clause : "(cl " proof_term* ")" -> mk_clause
            | "(cl)" -> mk_empty_clause
    
    ?single_context :  "(:=" "(" anchor_name vname ")" (term|vname) ")" -> add_context
                    | "(" anchor_name vname ")" -> add_trivial_ctx

    ?step_arg_pair : "(:=" CNAME term")" -> mk_forall_inst_args
                   | term* -> mk_la_generic_args

    ?step_annotation : ":premises" "(" step_id+ ")" -> mk_step_premises
                    | ":args" "(" step_arg_pair+ ")" -> mk_step_args
                    | ":discharge" "(" CNAME* ")" -> mk_discharge

    ?proof_term : term

    ?let_pair : "(" (vname|qname) term ")" -> mk_let_pair

    ?quant_pair : "(" (qname|vname) vname ")" -> mk_quant_pair

    ?term :   "true" -> mk_true
            | "false" -> mk_false
            | "(not " term ")" -> mk_neg_tm
            | "(or " term+ ")" -> mk_disj_tm
            | "(and " term+ ")" -> mk_conj_tm
            | "(=>" term term ")" -> mk_impl_tm
            | "(=" term term ")" -> mk_eq_tm
            | "(+" term* ")" -> mk_plus_tm
            | "(-" term term ")" -> mk_minus_tm
            | "(-" term ")" -> mk_uminus_tm
            | "(*" term* ")" -> mk_mul_tm
            | "(/" term term ")" -> mk_div_tm
            | "(div " term term ")" -> mk_div_tm
            | "(<" term term ")" -> mk_less_tm
            | "(>" term term ")" -> mk_greater_tm
            | "(<=" term term ")" -> mk_less_eq_tm
            | "(>=" term term ")" -> mk_greater_eq_tm
            | "(! " term ":named" (at_name|CNAME) ")" -> mk_annot_tm
            | "(let " "(" let_pair* ")" term ")" -> mk_let_tm
            | "(distinct " term term+ ")" -> mk_distinct_tm
            | "(xor " term term ")" -> mk_xor_tm
            | "(store " term term term ")" -> mk_store
            | "(select " term term ")" -> mk_select
            | "(" term ")" -> mk_par_tm
            | "(" term+ ")" -> mk_app_tm
            | "(ite " term term term ")" -> mk_ite_tm
            | "(forall " "(" quant_pair+ ")" term ")" -> mk_forall
            | "(exists " "(" quant_pair+ ")" term ")" -> mk_exists
            | "(choice " "(" quant_pair+ ")" term ")" -> mk_choice
            | "(! " term (":pattern " term)+ ")" -> mk_pat_term
            | INT -> mk_int
            | DECIMAL -> mk_decimal
            | name

    ?step_id : vname ("." vname)* -> mk_step_id

    ?name : "@" CNAME -> ret_annot_tm
            | qname -> ret_let_tm
            | vname -> ret_tm


    ?smt_term : term -> mk_smt_term

    ?smt_file_assert : "(assert " smt_term ")" -> mk_assertion

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
        self.quant_ctx = []

        # map from anchor variable to term
        self.anchor_ctx = dict()

        # indicate whether we are parsing a real term
        self.is_real = False
        for _, T in self.smt_file_ctx.items():
            if T == hol_type.RealType:
                self.is_real = True
                break


    def add_context(self, var, ty, tm_name):
        """return the new variables and the assigned term
        var is the variable name, ty is its type, tm_name is
        the term name (may not occur in previous context)
        """

        hol_ty = str_to_hol_type(ty)
        if isinstance(tm_name, hol_term.Term):
            tm = tm_name
        else:
            tm = hol_term.Var(tm_name, hol_ty)
            self.step_ctx[tm_name] = tm
        var_name = var
            
        assert tm.get_type() == hol_ty
        self.anchor_ctx[var_name] = hol_term.Var(var_name, hol_ty)
        return var_name, tm

    def add_trivial_ctx(self, var_name, ty):
        var_name = str(var_name)
        var = hol_term.Var(var_name, str_to_hol_type(str(ty)))
        self.anchor_ctx[var_name] = var
        return str(var_name), var

    def mk_vname(self, name):
        return str(name)
    
    def mk_qname(self, name):
        return "?" + str(name)

    def mk_quoted_vname(self, name):
        name = str(name)
        assert name[0] == '|' and name[-1] == '|'
        return name[1:-1]

    def ret_annot_tm(self, name):
        """Return the term which is represented by a unique @-prefix name."""
        name = "@" + str(name)
        return self.annot_tm[name]

    def ret_let_tm(self, name):
        """There are three kinds of occursion of ?name in proof.
        1. let expression : (let (?x 1) ?x + 1)
        2. anchor context: (:= (?x I) term)
        3. quantified variable: (forall (?x t). ?x)
        We first search ?name in let scope then in quantified variables, then in context, 
        this is correct since if ?name is not a binding var, the let scope would be empty. 
        """
        name = str(name)
        if name in self.let_tm:
            return self.let_tm[name]
        for p in reversed(self.quant_ctx):
            if name == p[0]:
                return p[1]
        for ctx in reversed(self.proof_ctx):
            if name in ctx:
                return hol_term.Var(name, ctx[name].get_type())
        if name in self.anchor_ctx:
            return self.anchor_ctx[name]

        print('let_tm', self.let_tm)
        print('quant_ctx', self.quant_ctx)
        print("anchor_ctx", self.anchor_ctx)
        raise VeriTParseException("ret_let_tm", "can't find %s" % str(name))

    def ret_tm(self, tm):
        tm = str(tm)
        for p in reversed(self.quant_ctx):
            if tm == p[0]:
                return p[1]
        if tm in self.step_ctx:
            return self.step_ctx[tm]
        if tm in self.smt_file_ctx:
            return hol_term.Var(tm, self.smt_file_ctx[tm])
        for ctx in reversed(self.proof_ctx):
            if tm in ctx:
                return hol_term.Var(tm, ctx[tm].get_type())
        if tm in self.let_tm:
            return self.let_tm[tm]
        # If not found in all these contexts, raise error
        raise ValueError(tm)

    def mk_par_tm(self, tm):
        return tm

    def mk_app_tm(self, *tms):
        return tms[0](*tms[1:])

    def mk_quant_pair(self, var_name, ty):
        var_name = str(var_name)
        hol_var = hol_term.Var(var_name, str_to_hol_type(str(ty)))
        self.quant_ctx.append((var_name, hol_var))
        return hol_var

    def mk_forall(self, *tms):
        for tm in reversed(tms[:-1]):
            assert tm.name == self.quant_ctx[-1][0]
            del self.quant_ctx[-1]
        return hol_term.Forall(*tms)

    def mk_exists(self, *tms):
        for tm in reversed(tms[:-1]):
            assert tm.name == self.quant_ctx[-1][0]
            del self.quant_ctx[-1]
        return hol_term.Exists(*tms)

    def mk_choice(self, *tms):
        for tm in reversed(tms[:-1]):
            assert tm.name == self.quant_ctx[-1][0]
            del self.quant_ctx[-1]
        return logic.mk_some(*tms)

    def mk_let_pair(self, name, tm):
        """Make the let scope."""
        name = str(name)
        T = tm.get_type()
        bound_var = hol_term.Var(name, T)
        self.let_tm[name] = bound_var
        return bound_var, T, tm

    def mk_forall_inst_args(self, name, tm):
        return str(name), tm

    def mk_la_generic_args(self, *tms):
        return tms

    def mk_let_tm(self, *tms):
        """Represent the let expression as a lambda term.
        
        - bounds: a list of binding pairs
        - lbd_tm: the function body
        The let scope will be cleared when the let-expression is closed.
        """
        for tm in tms[:-1]:
            assert tm[0].name in self.let_tm
            del self.let_tm[tm[0].name]
        res = tms[-1]
        for p in reversed(tms[:-1]):
            v, _, t = p
            res = hol_term.Let(v, t, res)
        return res

    def mk_distinct_tm(self, *tms):
        assert tms  # tms cannot be empty
        return hol_list.distinct(hol_list.mk_literal_list(tms, tms[0].get_type()))

    def mk_xor_tm(self, tm1, tm2):
        return logic.mk_xor(tm1, tm2)

    def mk_true(self):
        return hol_term.true

    def mk_false(self):
        return hol_term.false

    def mk_neg_tm(self, tm):
        return hol_term.Not(tm)

    def mk_annot_tm(self, tm, name):
        name = str(name)
        self.annot_tm[name] = tm
        return tm

    def mk_disj_tm(self, *tms):
        return hol_term.Or(*tms)

    def mk_conj_tm(self, *tms):
        return hol_term.And(*tms)

    def mk_impl_tm(self, *tms):
        return hol_term.Implies(*tms)

    def mk_eq_tm(self, *tms):
        return hol_term.Eq(*tms)

    def mk_ite_tm(self, P, x, y):
        return logic.mk_if(P, x, y)

    def mk_store(self, arr, i, v):
        arr_ty = arr.get_type()
        idx_ty = i.get_type()
        val_ty = v.get_type()
        store_tm = hol_term.Const("store", hol_term.TFun(arr_ty, idx_ty, val_ty, arr_ty))
        return store_tm(arr, i, v)

    def mk_select(self, f, arg):
        fun_ty = f.get_type()
        arg_ty = arg.get_type()
        return hol_term.Const("select", hol_term.TFun(fun_ty, arg_ty, fun_ty.args[1]))(f, arg)

    def mk_int(self, num):
        if self.is_real:
            return hol_term.Real(Fraction(num))
        else:
            return hol_term.Int(int(num))

    def mk_decimal(self, num):
        return hol_term.Real(Fraction(num))

    def mk_plus_tm(self, *ts):
        res = ts[0]
        for t in ts[1:]:
            res = res + t
        return res

    def mk_minus_tm(self, t1, t2):
        return t1 - t2

    def mk_uminus_tm(self, t1):
        return -t1

    def mk_mul_tm(self, *ts):
        res = ts[0]
        for t in ts[1:]:
            res = res * t
        return res

    def mk_div_tm(self, t1, t2):
        return t1 / t2

    def mk_less_tm(self, t1, t2):
        return t1 < t2

    def mk_greater_tm(self, t1, t2):
        return t1 > t2

    def mk_less_eq_tm(self, t1, t2):
        return t1 <= t2

    def mk_greater_eq_tm(self, t1, t2):
        return t1 >= t2

    def mk_step_id(self, *step_id):
        return ''.join(step_id)

    def mk_assume(self, assm_id, tm):
        return Assume(assm_id, tm)

    def mk_anchor(self, id, *ctx):
        """Every anchor (with ctx) will create a new context."""
        new_ctx = {}
        for var, tm in ctx:
            new_ctx[str(var)] = tm
        self.proof_ctx.append(new_ctx)
        prf_ctx = {var_name : tm for ctx in self.proof_ctx for var_name, tm in ctx.items()}
        step = Anchor(str(id), prf_ctx)
        self.cur_subprf_id.append(str(id))
        self.anchor_ctx.clear()
        return step

    def mk_empty_anchor(self, id):
        self.proof_ctx.append(dict())
        step = Anchor(str(id), dict())
        self.cur_subprf_id.append(str(id))
        return step

    def mk_step(self, step_id, cl, rule_name, *args):
        # make context of current step
        # Context created by anchor
        step_ctx = {var_name:tm for ctx in self.proof_ctx for var_name, tm in ctx.items()}
        
        # if current step meets subproof id, pop the last context
        if len(self.cur_subprf_id) and self.cur_subprf_id[-1] == step_id:
            self.cur_subprf_id.pop()
            self.proof_ctx.pop()

        # if there is no anchor context, the step should not be in a subproof
        assert self.cur_subprf_id or len(self.proof_ctx) == 0

        # Make new step
        step = Step(step_id, rule_name, cl, ctx=step_ctx)
        for arg_name, arg in args:
            if arg_name == PREMISES:
                step.pm = arg
            elif arg_name == ARGS:
                step.args = arg
            elif arg_name == DISCHARGE:
                step.discharge = arg
            else:
                raise ValueError(arg_name)
        return step

    def mk_clause(self, *tm):
        return tm

    def mk_empty_clause(self):
        return tuple()

    def mk_step_premises(self, *pm):
        return PREMISES, pm

    def mk_step_args(self, *args):
        return ARGS, args

    def mk_discharge(self, *steps):
        return DISCHARGE, steps

    def mk_assertion(self, tm):
        return tm

    def mk_smt_term(self, tm):
        return tm

    def mk_pat_term(self, tm, *pat):
        return tm

    def mk_at_name(self, name):
        return "@"+str(name)


def proof_parser(ctx):
    return Lark(veriT_grammar, start="proof_command", parser="lalr", transformer=ProofTransformer(smt_file_ctx=ctx))

def smt_assertion_parser(ctx):
    return Lark(veriT_grammar, start="smt_file_assert", parser="lalr", transformer=ProofTransformer(smt_file_ctx=ctx))
