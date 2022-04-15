from lark import Lark, Transformer, v_args, exceptions
from smt.veriT.command import Assume, Step, Anchor
from logic.logic import mk_if
from kernel import term as hol_term
from kernel import type as hol_type
from syntax import parser as hol_parser

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
    VNAME: ("_"|LETTER)("_"|LETTER|DIGIT|"$"|".")*

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
    VNAME: ("_"|LETTER)("_"|LETTER|DIGIT|"$"|".")*

    ?proof_command : "(assume" step_id proof_term ")" -> mk_assume
                    | "(step" step_id clause ":rule" CNAME step_annotation? ")" -> mk_step
                    | "(anchor :step" step_id ":args" "(" single_context+ ")" ")" -> mk_anchor
 
    ?clause : "(cl" proof_term* ")" -> mk_clause
    
    ?single_context : "(:=" "(" "?" CNAME CNAME ")" term ")" -> mk_context

    ?step_annotation : ":premises" "(" step_id+ ")" -> mk_premises

    ?proof_term : term

    ?let_pair : "(" "?" CNAME term ")" -> mk_let_pair

    ?term :   "true" -> mk_true
            | "false" -> mk_false
            | "(not" term ")" -> mk_neg_tm
            | "(or" term+ ")" -> mk_disj_tm
            | "(and" term+ ")" -> mk_conj_tm
            | "(=>" term term ")" -> mk_impl_tm
            | "(=" term term ")" -> mk_eq_tm
            | "(!" term ":named" "@" CNAME ")" -> mk_annot_tm
            | "(let" "(" let_pair+ ")" term ")" -> mk_let_tm
            | "(distinct" term term+ ")" -> mk_distinct_tm
            | "(" term ")" -> mk_par_tm
            | "(" term+ ")" -> mk_app_tm
            | "(ite" term term term ")" -> mk_ite_tm
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
        # Context from the SMT problem description file.
        self.smt_file_ctx = smt_file_ctx

        # Map from annotation to the term
        self.annot_tm = dict()

        # map from local variables to term
        self.let_tm = dict()

        # Proof context: map from variables to terms
        self.proof_ctx = dict()

    def mk_context(self, var, ty, tm):
        hol_ty = str_to_hol_type(ty.value)
        hol_var = hol_term.Var(var.value, hol_ty)
        self.proof_ctx[hol_var] = tm

    def mk_anchor(self, id, *ctx):
        return Anchor(str(id), ctx)

    def ret_annot_tm(self, name):
        name = "@" + str(name)
        return self.annot_tm[name]

    def ret_let_tm(self, name):
        name = "?" + str(name)
        return self.let_tm[name]

    def mk_par_tm(self, tm):
        return tm

    def mk_app_tm(self, *tms):
        return tms[0](*tms[1:])

    def mk_let_pair(self, name, tm):
        name = "?" + str(name)
        
        self.let_tm[name] = tm

    def mk_let_tm(self, *tms):
        return tms[-1]

    def ret_tm(self, tm):
        # if str(tm) in self.annot_tm:
        #     return self.annot_tm[str(tm)]
        # if str(tm) in self.let_tm:
        #     return self.let_tm[str(tm)]
        tm = str(tm)
        if tm not in self.smt_file_ctx:
            raise ValueError(tm)      
        return hol_term.Var(tm, self.smt_file_ctx[str(tm)])

    def mk_distinct_tm(self, *tms):
        neq_tm = []
        for i in range(len(tms)):
            for j in range(i+1, len(tms)):
                neq_tm.append(hol_term.Not(hol_term.Eq(tms[i], tms[j])))

        return hol_term.And(*neq_tm)

    def mk_true(self):
        return hol_term.true

    def mk_false(self):
        return hol_term.false

    def mk_neg_tm(self, tm):
        # if tm in self.annot_tm:
        #     tm = self.annot_tm[str(tm)]
        # print(str(tm))
        return hol_term.Not(tm)

    def mk_annot_tm(self, tm, name):
        name = "@" + str(name)
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
        return mk_if(P, x, y)

    def mk_step_id(self, *step_id):
        return ''.join(step_id)

    def mk_assume(self, assm_id, tm):
        return Assume(assm_id, tm)

    def mk_step(self, step_id, cl, rule_name, pm=None):
        if pm is not None:
            pm = [p for p in pm]
        return Step(step_id, rule_name, cl, pm)

    def mk_clause(self, *tm):
        if len(tm) == 0:
            return hol_term.false
        return hol_term.Or(*tm)

    def mk_premises(self, *pm):
        return pm

def proof_parser(ctx):
    return Lark(veriT_grammar, start="proof_command", parser="lalr", transformer=ProofTransformer(smt_file_ctx=ctx))

