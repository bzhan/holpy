# Author: Bohua Zhan

from kernel.type import Type, TFun, hol_bool
from kernel.term import Const
from kernel.thm import Thm
from logic import nat
from logic.nat import natT
from logic.proofterm import ProofTermMacro, ProofTerm, ProofTermDeriv
from logic import logic_macro

"""Automation for arithmetic expressions."""

aexpT = Type("aexp")

N = Const("N", TFun(natT, aexpT))
V = Const("V", TFun(natT, aexpT))
Plus = Const("Plus", TFun(aexpT, aexpT, aexpT))
Times = Const("Times", TFun(aexpT, aexpT, aexpT))

avalI = Const("avalI", TFun(TFun(natT, natT), aexpT, natT, hol_bool))

class prove_avalI_macro(ProofTermMacro):
    """Given a state s and an expression t, return a theorem of
    the form avalI s t n, where n is a constant natural number.

    """
    def __init__(self):
        pass

    def get_proof_term(self, thy, args, *pts):
        s, t = args
        f, args = t.strip_comb()
        apply_thm = logic_macro.apply_theorem_macro()
        if f == N:
            n = args[0]
            return ProofTerm.substitution({"s": s, "n": n}, ProofTerm.theorem(thy, "avalI_const"))
        elif f == V:
            x = args[0]
            return ProofTerm.substitution({"s": s, "x": x}, ProofTerm.theorem(thy, "avalI_var"))
        elif f == Plus:
            a1, a2 = args
            pt1 = self.get_proof_term(thy, (s, a1))
            pt2 = self.get_proof_term(thy, (s, a2))
            _, args1 = pt1.th.concl.strip_comb()
            _, args2 = pt2.th.concl.strip_comb()
            return ProofTermDeriv(apply_thm(thy, "avalI_plus", pt1.th, pt2.th),
                   "apply_theorem", "avalI_plus", [pt1, pt2])
        elif f == Times:
            a1, a2 = args
            pt1 = self.get_proof_term(thy, (s, a1))
            pt2 = self.get_proof_term(thy, (s, a2))
            _, args1 = pt1.th.concl.strip_comb()
            _, args2 = pt2.th.concl.strip_comb()
            return ProofTermDeriv(apply_thm(thy, "avalI_times", pt1.th, pt2.th),
                   "apply_theorem", "avalI_times", [pt1, pt2])
        else:
            raise NotImplementedError
