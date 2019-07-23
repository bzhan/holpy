# Author: Bohua Zhan

from kernel.type import Type, TFun, boolT
from kernel.term import Term, Const
from kernel.thm import Thm
from kernel.macro import global_macros
from kernel.theory import Method, global_methods
from logic import logic
from logic.logic import apply_theorem
from data import nat
from data import function
from data.nat import natT
from logic.conv import arg_conv
from logic.proofterm import ProofTermMacro, ProofTerm
from server.tactic import MacroTactic
from syntax import printer, settings

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
        """Given state s and expression t, return the proof of a theorem
        of the form avalI s t n.

        """
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

    def get_avalI(self, thy, s, t):
        """Given state s and expression t, return the integer n such that
        avalI s t n holds.

        """
        def helper(t):
            if t.head == N:
                return nat.from_binary_nat(t.args[0])
            elif t.head == V:
                x, = t.args
                res = function.fun_upd_eval_conv().eval(thy, s(x)).prop.rhs
                assert nat.is_binary_nat(res), "get_avalI"
                return nat.from_binary_nat(res)
            elif t.head == Plus:
                a1, a2 = t.args
                return helper(a1) + helper(a2)
            elif t.head == Times:
                a1, a2 = t.args
                return helper(a1) * helper(a2)

        return helper(t)

    def eval(self, thy, goal, ths):
        assert isinstance(goal, Term), "prove_avalI_macro"
        assert len(ths) == 0, "prove_avalI_macro"
        s, t, n = goal.args
        res = self.get_avalI(thy, s, t)
        assert n == nat.to_binary_nat(res), "prove_avalI_macro: wrong result"
        return Thm([], goal)

    def can_eval(self, thy, goal):
        assert isinstance(goal, Term), "prove_avalI_macro"
        if goal.head != avalI or len(goal.args) != 3:
            return False
        s, t, n = goal.args
        try:
            res = self.get_avalI(thy, s, t)
        except AssertionError:
            return False

        return n == nat.to_binary_nat(res)

    def get_proof_term(self, thy, goal, pts):
        assert isinstance(goal, Term), "prove_avalI_macro"
        assert len(pts) == 0, "prove_avalI_macro"
        s, t, n = goal.args
        pt = self.get_avalI_th(thy, s, t)
        assert n == pt.prop.arg, "prove_avalI_macro: wrong result."
        return pt

class prove_avalI_method(Method):
    """Apply prove_avalI macro."""
    def __init__(self):
        self.sig = []

    def search(self, state, id, prevs):
        if len(prevs) != 0:
            return []

        cur_th = state.get_proof_item(id).th
        if prove_avalI_macro().can_eval(state.thy, cur_th.prop):
            return [{}]
        else:
            return []

    @settings.with_settings
    def display_step(self, state, id, data, prevs):
        return printer.N("prove_avalI: (solves)")

    def apply(self, state, id, data, prevs):
        assert len(prevs) == 0, "prove_avalI_method"
        state.apply_tactic(id, MacroTactic('prove_avalI'))


global_macros.update({
    "prove_avalI": prove_avalI_macro(),
})

global_methods.update({
    "prove_avalI": prove_avalI_method(),
})