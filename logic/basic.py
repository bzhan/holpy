# Author: Bohua Zhan

from kernel.type import TVar, Type, TFun, hol_bool
from kernel.term import Var, Const, Term
from kernel.thm import Thm
from kernel.proof import Proof
from kernel.theory import Theory
from kernel.macro import MacroSig, ProofMacro
from logic.matcher import Matcher
from logic.proofterm import ProofTerm
from logic.conv import beta_conv, top_conv

class OperatorData():
    """Represents information for one operator."""
    
    LEFT_ASSOC, RIGHT_ASSOC = range(2)
    UNARY, BINARY = range(2)

    def __init__(self, fun_name, priority, *, assoc = None, arity = BINARY, ascii_op = None, unicode_op = None):
        """Instantiate data for an operator."""
        self.fun_name = fun_name
        self.priority = priority
        self.assoc = assoc
        self.arity = arity
        self.ascii_op = ascii_op
        self.unicode_op = unicode_op

class OperatorTable():
    """Represents information for operators.
    
    For each operator, we record its corresponding function, priority,
    and left/right associativity.
    
    """
    def __init__(self):
        LEFT, RIGHT = OperatorData.LEFT_ASSOC, OperatorData.RIGHT_ASSOC
        self.data = [
            OperatorData("equals", 50, assoc = LEFT, ascii_op = "="),
            OperatorData("implies", 25, assoc = RIGHT, ascii_op = "-->", unicode_op = "⟶"),
            OperatorData("conj", 35, assoc = RIGHT, ascii_op = "&", unicode_op = "∧"),
            OperatorData("disj", 30, assoc = RIGHT, ascii_op = "|", unicode_op = "∨"),
            OperatorData("neg", 40, arity = OperatorData.UNARY, ascii_op = "~", unicode_op = "¬"),
            OperatorData("plus", 65, assoc = LEFT, ascii_op = "+"),
            OperatorData("times", 70, assoc = LEFT, ascii_op = "*"),
        ]        

    def get_info_for_fun(self, t):
        """Returns data associated to a function term. The result is None
        if the function is not found.

        """
        if t.ty == Term.CONST:
            for d in self.data:
                if d.fun_name == t.name:
                    return d

        return None

class arg_combination_macro(ProofMacro):
    """Given theorem x = y and term f, return f x = f y."""

    def __init__(self):
        self.level = 1
        self.sig = MacroSig.TERM
        self.has_theory = False

    def __call__(self, f, th):
        assert th.concl.is_equals(), "arg_combination"
        return Thm.combination(Thm.reflexive(f), th)

    def expand(self, depth, f, *prevs):
        id, th = prevs[0]
        assert th.concl.is_equals(), "arg_combination"

        prf = Proof()
        prf.add_item((depth, "S1"), "reflexive", args = f)
        prf.add_item("C", "combination", prevs = [(depth, "S1"), id])
        return prf

class fun_combination_macro(ProofMacro):
    """Given theorem f = g and term x, return f x = g x."""

    def __init__(self):
        self.level = 1
        self.sig = MacroSig.TERM
        self.has_theory = False

    def __call__(self, x, th):
        assert th.concl.is_equals(), "fun_combination"
        return Thm.combination(th, Thm.reflexive(x))

    def expand(self, depth, x, *prevs):
        id, th = prevs[0]
        assert th.concl.is_equals(), "fun_combination"

        prf = Proof()
        prf.add_item((depth, "S1"), "reflexive", args = x)
        prf.add_item("C", "combination", prevs = [id, (depth, "S1")])
        return prf

class beta_norm_macro(ProofMacro):
    """Given theorem th, return the normalization of th."""

    def __init__(self):
        self.level = 1
        self.sig = MacroSig.NONE
        self.has_theory = False

    def __call__(self, th):
        cv = top_conv(beta_conv())
        eq_th = cv(th.concl)
        return Thm(th.assums, eq_th.concl.arg)

    def expand(self, depth, *prevs):
        id, th = prevs[0]
        cv = top_conv(beta_conv())
        pt = cv.get_proof_term(th.concl)
        pt2 = ProofTerm.equal_elim(pt, ProofTerm.atom(id, th))
        return pt2.export(depth)

class apply_theorem_macro(ProofMacro):
    """Apply existing theorem in the theory to a list of current
    results in the proof.

    """
    def __init__(self):
        self.level = 1
        self.sig = MacroSig.STRING
        self.has_theory = True

    def __call__(self, thy, name, *prevs):
        th = thy.get_theorem(name)
        inst = dict()

        As, C = th.concl.strip_implies()
        for idx, arg in enumerate(prevs):
            Matcher.first_order_match_incr(As[idx], arg.concl, inst)
        return Thm(th.assums, C.subst(inst))

    def expand(self, depth, thy, name, *prevs):
        th = thy.get_theorem(name)
        inst = dict()

        As, C = th.concl.strip_implies()
        for idx, (_, arg) in enumerate(prevs):
            Matcher.first_order_match_incr(As[idx], arg.concl, inst)

        pt = ProofTerm.substitution(inst, ProofTerm.theorem(thy, name))
        for idx, (id, prev) in enumerate(prevs):
            pt = ProofTerm.implies_elim(pt, ProofTerm.atom(id, prev))
        return pt.export(depth)

class Logic():
    """Utility functions for logic."""

    conj = Const("conj", TFun(hol_bool, hol_bool, hol_bool))
    disj = Const("disj", TFun(hol_bool, hol_bool, hol_bool))
    neg = Const("neg", TFun(hol_bool, hol_bool))
    true = Const("true", hol_bool)
    false = Const("false", hol_bool)
        
    @staticmethod
    def is_conj(t):
        """Whether t is of the form A & B."""
        return self.is_binop() and self.get_head() == Logic.conj

    @staticmethod
    def mk_conj(s, t):
        """Construct the term s & t."""
        return Logic.conj(s, t)

    @staticmethod
    def is_disj(t):
        """Whether t is of the form A | B."""
        return self.is_binop() and self.get_head() == Logic.disj

    @staticmethod
    def mk_disj(s, t):
        """Construct the term s | t."""
        return Logic.disj(s, t)

    @staticmethod
    def is_neg(t):
        """Whether t is of the form ~ A."""
        return self.ty == Term.COMB and self.fun == Logic.neg

    @staticmethod
    def is_exists(t):
        """Whether t is of the form ?x. P x."""
        return t.ty == Term.COMB and t.fun.ty == Term.CONST and \
            t.fun.name == "exists" and t.arg.ty == Term.ABS

    @staticmethod
    def mk_exists(x, body, *, var_name = None, T = None):
        """Given a variable x and a term t possibly depending on x, return
        the term ?x. t.

        """
        if T is None:
            T = x.T

        exists_t = Const("exists", TFun(TFun(T, hol_bool), hol_bool))
        return exists_t(Term.mk_abs(x, body, var_name = var_name, T = T))

class Nat():
    """Utility functions for natural number arithmetic."""

    nat = Type("nat")
    zero = Const("0", nat)
    Suc = Const("Suc", TFun(nat, nat))
    one = Suc(zero)
    plus = Const("plus", TFun(nat, nat, nat))
    times = Const("times", TFun(nat, nat, nat))

def BasicTheory():
    thy = Theory.EmptyTheory()

    # Operators
    thy.add_data_type("operator", OperatorTable())

    # Logical terms
    thy.add_term_sig("conj", TFun(hol_bool, hol_bool, hol_bool))
    thy.add_term_sig("disj", TFun(hol_bool, hol_bool, hol_bool))
    thy.add_term_sig("neg", TFun(hol_bool, hol_bool))
    thy.add_term_sig("true", hol_bool)
    thy.add_term_sig("false", hol_bool)
    thy.add_term_sig("exists", TFun(TFun(TVar("a"), hol_bool), hol_bool))

    A = Var("A", hol_bool)
    B = Var("B", hol_bool)
    C = Var("C", hol_bool)
    imp = Term.mk_implies
    eq = Term.mk_equals

    # Axioms for conjugation
    conjAB = Logic.mk_conj(A, B)
    thy.add_theorem("conjI", Thm([], imp(A, B, conjAB)))
    thy.add_theorem("conjD1", Thm([], imp(conjAB, A)))
    thy.add_theorem("conjD2", Thm([], imp(conjAB, B)))

    # Axioms for disjunction
    disjAB = Logic.mk_disj(A, B)
    thy.add_theorem("disjI1", Thm([], imp(A, disjAB)))
    thy.add_theorem("disjI2", Thm([], imp(B, disjAB)))
    thy.add_theorem("disjE", Thm([], imp(imp(A, C), imp(B, C), imp(disjAB, C))))

    # Axioms for negation
    thy.add_theorem("negI", Thm([], imp(imp(A, Logic.false), Logic.neg(A))))
    thy.add_theorem("negE", Thm([], imp(Logic.neg(A), A, Logic.false)))

    # Axioms for true
    thy.add_theorem("trueI", Thm([], Logic.true))

    # Axioms for false
    thy.add_theorem("falseE", Thm([], imp(Logic.false, A)))

    # Axioms for exists
    P = Var("P", TFun(TVar("a"), hol_bool))
    a = Var("a", TVar("a"))
    thy.add_theorem("exI", Thm([], imp(P(a), Logic.mk_exists(a, P(a)))))
    thy.add_theorem("exE", Thm([], imp(Logic.mk_exists(a, P(a)), Term.mk_all(a, imp(P(a), C)), C)))

    # Classical axiom
    thy.add_theorem("classical", Thm([], Logic.disj(A, Logic.neg(A))))

    # Natural numbers
    nat = Nat.nat
    thy.add_type_sig("nat", 0)
    thy.add_term_sig("0", nat)
    thy.add_term_sig("Suc", TFun(nat, nat))

    m = Var("m", nat)
    n = Var("n", nat)
    P = Var("P", TFun(nat, hol_bool))
    S = Nat.Suc
    thy.add_theorem("nat.Suc_inject", Thm([], imp(eq(S(m), S(n)), eq(m, n))))
    thy.add_theorem("nat.Suc_not_zero", Thm([], Logic.neg(eq(S(m), Nat.zero))))
    thy.add_theorem("nat.induct", Thm([], imp(P(Nat.zero), Term.mk_all(n, imp(P(n), P(S(n)))), P(n))))

    # Addition on natural numbers
    plus = Nat.plus
    thy.add_term_sig("plus", TFun(nat, nat, nat))
    thy.add_theorem("nat.add_0", Thm([], eq(plus(Nat.zero, n), n)))
    thy.add_theorem("nat.add_Suc", Thm([], eq(plus(S(m), n), S(plus(m, n)))))

    # Multiplication on natural numbers
    times = Nat.times
    thy.add_term_sig("times", TFun(nat, nat, nat))
    thy.add_theorem("nat.mult_0", Thm([], eq(times(Nat.zero, n), Nat.zero)))
    thy.add_theorem("nat.mult_Suc", Thm([], eq(times(S(m), n), plus(n, times(m, n)))))

    # Basic macros
    thy.add_proof_macro("arg_combination", arg_combination_macro())
    thy.add_proof_macro("fun_combination", fun_combination_macro())
    thy.add_proof_macro("beta_norm", beta_norm_macro())
    thy.add_proof_macro("apply_theorem", apply_theorem_macro())
    return thy
