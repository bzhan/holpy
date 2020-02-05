# Author: Bohua Zhan

from kernel.type import TConst, TFun, BoolType, NatType
from kernel.term import Term, Const, Nat
from kernel.thm import Thm
from kernel.macro import Macro
from kernel.theory import register_macro
from logic import logic
from logic.logic import apply_theorem
from data import nat
from data import function
from logic.conv import arg_conv
from kernel.proofterm import ProofTerm
from server.method import Method, global_methods
from server.tactic import MacroTactic
from syntax import pprint, settings

"""Automation for arithmetic expressions."""

aexpT = TConst("aexp")

N = Const("N", TFun(NatType, aexpT))
V = Const("V", TFun(NatType, aexpT))
Plus = Const("Plus", TFun(aexpT, aexpT, aexpT))
Times = Const("Times", TFun(aexpT, aexpT, aexpT))

avalI = Const("avalI", TFun(TFun(NatType, NatType), aexpT, NatType, BoolType))


@register_macro('prove_avalI')
class prove_avalI_macro(Macro):
    """Prove a theorem of the form avalI s t n."""
    def __init__(self):
        self.level = 10
        self.sig = Term
        self.limit = 'avalI_times'

    def get_avalI_th(self, s, t):
        """Given state s and expression t, return the proof of a theorem
        of the form avalI s t n.

        """
        def helper(t):
            if t.head == N:
                n, = t.args
                return apply_theorem("avalI_const", concl=avalI(s, N(n), n))
            elif t.head == V:
                x, = t.args
                pt = apply_theorem("avalI_var", concl=avalI(s, V(x), s(x)))
                return pt.on_arg(function.fun_upd_eval_conv())
            elif t.head == Plus:
                a1, a2 = t.args
                pt = apply_theorem("avalI_plus", helper(a1), helper(a2))
                return pt.on_arg(nat.nat_conv())
            elif t.head == Times:
                a1, a2 = t.args
                pt = apply_theorem("avalI_times", helper(a1), helper(a2))
                return pt.on_arg(nat.nat_conv())
        return helper(t)

    def get_avalI(self, s, t):
        """Given state s and expression t, return the integer n such that
        avalI s t n holds.

        """
        def helper(t):
            if t.head == N:
                return t.args[0].dest_number()
            elif t.head == V:
                x, = t.args
                res = function.fun_upd_eval_conv().eval(s(x)).prop.rhs
                assert res.is_number(), "get_avalI"
                return res.dest_number()
            elif t.head == Plus:
                a1, a2 = t.args
                return helper(a1) + helper(a2)
            elif t.head == Times:
                a1, a2 = t.args
                return helper(a1) * helper(a2)

        return helper(t)

    def eval(self, goal, ths):
        assert isinstance(goal, Term), "prove_avalI_macro"
        assert len(ths) == 0, "prove_avalI_macro"
        s, t, n = goal.args
        res = self.get_avalI(s, t)
        assert n == Nat(res), "prove_avalI_macro: wrong result"
        return Thm([], goal)

    def can_eval(self, goal):
        assert isinstance(goal, Term), "prove_avalI_macro"
        if goal.head != avalI or len(goal.args) != 3:
            return False
        s, t, n = goal.args
        try:
            res = self.get_avalI(s, t)
        except AssertionError:
            return False

        return n == Nat(res)

    def get_proof_term(self, goal, pts):
        assert isinstance(goal, Term), "prove_avalI_macro"
        assert len(pts) == 0, "prove_avalI_macro"
        s, t, n = goal.args
        pt = self.get_avalI_th(s, t)
        assert n == pt.prop.arg, "prove_avalI_macro: wrong result."
        return pt

class prove_avalI_method(Method):
    """Apply prove_avalI macro."""
    def __init__(self):
        self.sig = []
        self.limit = 'avalI_times'

    def search(self, state, id, prevs, data=None):
        if data:
            return [data]

        if len(prevs) != 0:
            return []

        cur_th = state.get_proof_item(id).th
        if prove_avalI_macro().can_eval(cur_th.prop):
            return [{}]
        else:
            return []

    def display_step(self, state, data):
        return pprint.N("prove_avalI: (solves)")

    def apply(self, state, id, data, prevs):
        assert len(prevs) == 0, "prove_avalI_method"
        state.apply_tactic(id, MacroTactic('prove_avalI'))


global_methods.update({
    "prove_avalI": prove_avalI_method(),
})