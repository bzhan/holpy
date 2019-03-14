# Author: Bohua Zhan

from kernel.type import Type, TFun, hol_bool
from kernel.term import Const
from kernel.macro import MacroSig, global_macros
from logic import nat
from logic.proofterm import ProofTermMacro
from logic.logic_macro import init_theorem, apply_theorem


"""Automation for Hoare logic."""

def comT(T):
    return Type("com", T)

def Assign(Ta, Tb):
    return Const("Assign", TFun(Ta, Tb, comT(TFun(Ta, Tb))))

def Seq(T):
    return Const("Seq", TFun(comT(T), comT(T), comT(T)))

def Sem(T):
    return Const("Sem", TFun(comT(T), T, T, hol_bool))

class eval_Sem_macro(ProofTermMacro):
    """Prove a theorem of the form Sem com st st2."""
    def __init__(self):
        self.level = 10
        self.sig = MacroSig.TERM
        self.has_theory = True
        self.use_goal = True

    def eval_Sem(self, thy, com, st):
        """Evaluates the effect of program com on state st."""
        f, args = com.strip_comb()
        if f.is_const_with_name("Assign"):
            a, b = args
            Ta = a.get_type()
            Tb = b.get_type()
            return init_theorem(thy, "Sem_Assign", tyinst={"a": Ta, "b": Tb}, inst={"a": a, "b": b, "s": st})
        elif f.is_const_with_name("Seq"):
            c1, c2 = args
            pt1 = self.eval_Sem(thy, c1, st)
            st2 = pt1.th.concl.arg
            pt2 = self.eval_Sem(thy, c2, st2)
            return apply_theorem(thy, "Sem_seq", pt1, pt2)
        else:
            raise NotImplementedError

    def get_proof_term(self, thy, args, *pts):
        assert len(pts) == 0, "eval_Sem_macro"
        f, args = args.strip_comb()
        com, st, st2 = args
        pt = self.eval_Sem(thy, com, st)
        res_st2 = pt.th.concl.arg
        assert st2 == res_st2, "eval_Sem_macro: wrong result."
        return pt

global_macros.update({
    "eval_Sem": eval_Sem_macro(),
})
