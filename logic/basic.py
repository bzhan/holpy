# Author: Bohua Zhan

from kernel.type import TFun, hol_bool
from kernel.term import Var, Const, Term
from kernel.thm import Thm
from kernel.proof import Proof
from kernel.theory import Theory
from kernel.macro import ProofMacro

class OperatorData():
    """Represents information for operators.
    
    For each operator, we record its corresponding function, priority,
    and left/right associativity.
    
    """
    LEFT_ASSOC, RIGHT_ASSOC = range(2)

    def __init__(self):
        data = [
            ("=", "equals", 50, OperatorData.LEFT_ASSOC),
            ("-->", "implies", 25, OperatorData.RIGHT_ASSOC),
            ("&", "conj", 35, OperatorData.RIGHT_ASSOC),
            ("|", "disj", 30, OperatorData.RIGHT_ASSOC),
        ]

        self.op_dict = dict()
        self.fun_dict = dict()

        for op_str, fun_name, priority, assoc in data:
            self.op_dict[op_str] = (fun_name, priority, assoc)
            self.fun_dict[fun_name] = (op_str, priority, assoc)

    def get_info_for_op(self, op_str):
        """Returns (priority, fun_name) associated to an operator. The
        result is None if the operator is not found.
        
        """
        if op_str in self.op_dict:
            return self.op_dict[op_str]
        else:
            return None

    def get_info_for_fun(self, t):
        """Returns (priority, op_str) associated to a function term. The
        result is None if the function is not found.

        """
        if t.ty == Term.CONST and t.name in self.fun_dict:
            return self.fun_dict[t.name]
        else:
            return None

def arg_combination_macro():
    """Given theorem x = y and term f, return f x = f y."""
    def eval(th, f):
        assert th.concl.is_equals(), "arg_combination"
        return Thm.combination(Thm.reflexive(f), th)

    def expand(depth, ids, th, f):
        assert th.concl.is_equals(), "arg_combination"

        th1 = Thm.reflexive(f)
        th2 = Thm.combination(th1, th)
        prf = Proof()
        prf.add_item((depth, "S1"), th1, "reflexive", args = f)
        prf.add_item("C", th2, "combination", prevs = [(depth, "S1"), ids[0]])
        return prf

    return ProofMacro("arg_combination", eval, expand, level = 1)

def fun_combination_macro():
    """Given theorem f = g and term x, return f x = g x."""
    def eval(th, f):
        assert th.concl.is_equals(), "fun_combination"
        return Thm.combination(th, Thm.reflexive(f))

    def expand(depth, ids, th, f):
        assert th.concl.is_equals(), "fun_combination"

        th1 = Thm.reflexive(f)
        th2 = Thm.combination(th, th1)
        prf = Proof()
        prf.add_item((depth, "S1"), th1, "reflexive", args = f)
        prf.add_item("C", th2, "combination", prevs = [ids[0], (depth, "S1")])
        return prf

    return ProofMacro("fun_combination", eval, expand, level = 1)

def BasicTheory():
    thy = Theory.EmptyTheory()

    # Operators
    thy.add_data_type("operator", OperatorData())

    # Logical terms
    thy.add_term_sig("conj", TFun(hol_bool, hol_bool, hol_bool))
    thy.add_term_sig("disj", TFun(hol_bool, hol_bool, hol_bool))

    # Basic macros
    thy.add_proof_macro(arg_combination_macro())
    thy.add_proof_macro(fun_combination_macro())
    return thy

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
