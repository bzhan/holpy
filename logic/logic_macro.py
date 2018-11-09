# Author: Bohua Zhan

from kernel.macro import MacroSig, ProofMacro
from kernel.proof import Proof
from kernel.thm import Thm
from logic.conv import beta_conv, top_conv
from logic.matcher import Matcher
from logic.proofterm import ProofTerm

"""Standard macros in logic."""

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
