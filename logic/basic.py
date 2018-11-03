# Author: Bohua Zhan

from kernel.type import TFun, hol_bool
from kernel.term import Var, Const, Term
from kernel.thm import Thm
from kernel.proof import Proof
from kernel.theory import Theory
from kernel.macro import ProofMacro

class OperatorData():
    """Represents information for one operator."""
    
    LEFT_ASSOC, RIGHT_ASSOC = range(2)

    def __init__(self, fun_name, priority, *, assoc = None, ascii_op = None, unicode_op = None):
        self.fun_name = fun_name
        self.priority = priority
        self.assoc = assoc
        self.ascii_op = ascii_op
        self.unicode_op = unicode_op

class OperatorTable():
    """Represents information for operators.
    
    For each operator, we record its corresponding function, priority,
    and left/right associativity.
    
    """
    def __init__(self):
        self.data = [
            OperatorData("equals", 50, assoc = OperatorData.LEFT_ASSOC, ascii_op = "="),
            OperatorData("implies", 25, assoc = OperatorData.RIGHT_ASSOC, ascii_op = "-->"),
            OperatorData("conj", 35, assoc = OperatorData.RIGHT_ASSOC, ascii_op = "&"),
            OperatorData("disj", 30, assoc = OperatorData.RIGHT_ASSOC, ascii_op = "|"),
        ]

    def get_info_for_op(self, op_str):
        """Returns data associated to an operator. The result is None
        if the operator is not found.
        
        """
        for d in self.data:
            if d.ascii_op == op_str or d.unicode_op == op_str:
                return d

        return None

    def get_info_for_fun(self, t):
        """Returns data associated to a function term. The result is None
        if the function is not found.

        """
        if t.ty == Term.CONST:
            for d in self.data:
                if d.fun_name == t.name:
                    return d

        return None

def arg_combination_macro():
    """Given theorem x = y and term f, return f x = f y."""
    def eval(th, f):
        assert th.concl.is_equals(), "arg_combination"
        return Thm.combination(Thm.reflexive(f), th)

    def expand(depth, ids, th, f):
        assert th.concl.is_equals(), "arg_combination"

        prf = Proof()
        prf.add_item((depth, "S1"), "reflexive", args = f)
        prf.add_item("C", "combination", prevs = [(depth, "S1"), ids[0]])
        return prf

    return ProofMacro("arg_combination", eval, expand, level = 1)

def fun_combination_macro():
    """Given theorem f = g and term x, return f x = g x."""
    def eval(th, f):
        assert th.concl.is_equals(), "fun_combination"
        return Thm.combination(th, Thm.reflexive(f))

    def expand(depth, ids, th, f):
        assert th.concl.is_equals(), "fun_combination"

        prf = Proof()
        prf.add_item((depth, "S1"), "reflexive", args = f)
        prf.add_item("C", "combination", prevs = [ids[0], (depth, "S1")])
        return prf

    return ProofMacro("fun_combination", eval, expand, level = 1)

class Logic():
    """Utility functions for logic."""

    conj = Const("conj", TFun(hol_bool, hol_bool, hol_bool))
    disj = Const("disj", TFun(hol_bool, hol_bool, hol_bool))
        
    @staticmethod
    def is_conj(t):
        """Whether t is of the form s & t."""
        return self.is_binop() and self.get_head() == Logic.conj

    @staticmethod
    def mk_conj(s, t):
        """Construct the term s & t."""
        return Logic.conj(s, t)

    @staticmethod
    def is_disj(t):
        """Whether t is of the form s | t."""
        return self.is_binop() and self.get_head() == Logic.disj

    @staticmethod
    def mk_disj(s, t):
        """Construct the term s | t."""
        return Logic.disj(s, t)

def BasicTheory():
    thy = Theory.EmptyTheory()

    # Operators
    thy.add_data_type("operator", OperatorTable())

    # Logical terms
    thy.add_term_sig("conj", TFun(hol_bool, hol_bool, hol_bool))
    thy.add_term_sig("disj", TFun(hol_bool, hol_bool, hol_bool))

    A = Var("A", hol_bool)
    B = Var("B", hol_bool)
    C = Var("C", hol_bool)
    imp = Term.mk_implies

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

    # Basic macros
    thy.add_proof_macro(arg_combination_macro())
    thy.add_proof_macro(fun_combination_macro())
    return thy
