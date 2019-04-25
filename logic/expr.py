# Author: Bohua Zhan

from kernel.type import Type, TFun, boolT
from kernel.term import Term, Const
from kernel.thm import Thm
from kernel.macro import global_macros
from logic import logic
from logic import nat
from logic import function
from logic.nat import natT
from logic.conv import arg_conv
from logic.proofterm import ProofTermMacro, ProofTerm
from logic.logic_macro import apply_theorem

"""Automation for arithmetic expressions."""

aexpT = Type("aexp")

N = Const("N", TFun(natT, aexpT))
V = Const("V", TFun(natT, aexpT))
Plus = Const("Plus", TFun(aexpT, aexpT, aexpT))
Times = Const("Times", TFun(aexpT, aexpT, aexpT))

avalI = Const("avalI", TFun(TFun(natT, natT), aexpT, natT, boolT))

class prove_avalI_macro(ProofTermMacro):
    """Prove a theorem of the form avalI s t n."""
    def __init__(self):
        self.level = 10
        self.sig = Term

    def get_avalI_th(self, thy, s, t):
        def helper(t):
            if t.head == N:
                n, = t.args
                return apply_theorem(thy, "avalI_const", concl=avalI(s, N(n), n))
            elif t.head == V:
                x, = t.args
                pt = apply_theorem(thy, "avalI_var", concl=avalI(s, V(x), s(x)))
                return pt.on_arg(thy, function.fun_upd_eval_conv())
            elif t.head == Plus:
                a1, a2 = t.args
                pt = apply_theorem(thy, "avalI_plus", helper(a1), helper(a2))
                return pt.on_arg(thy, nat.nat_conv())
            elif t.head == Times:
                a1, a2 = t.args
                pt = apply_theorem(thy, "avalI_times", helper(a1), helper(a2))
                return pt.on_arg(thy, nat.nat_conv())
        return helper(t)

    def get_proof_term(self, thy, args, pts):
        assert len(pts) == 0, "prove_avalI_macro"
        f, (s, t, n) = args.strip_comb()
        pt = self.get_avalI_th(thy, s, t)
        assert n == pt.prop.arg, "prove_avalI_macro: wrong result."
        return pt

global_macros.update({
    "prove_avalI": prove_avalI_macro(),
})
