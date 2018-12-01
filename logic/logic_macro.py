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

    If with_concl is set, the signature is (th_name, concl), where
    th_name is the name of the theorem, concl is the expected conclusion.

    If with_concl is not set, the signature is th_name, where th_name
    is the name of the theorem.

    """
    def __init__(self, *, with_concl=False):
        self.level = 1
        self.with_concl = with_concl
        self.sig = MacroSig.STRING_TERM if with_concl else MacroSig.STRING
        self.has_theory = True

    def __call__(self, thy, args, *prevs):
        if self.with_concl:
            name, concl = args
        else:
            name = args
        th = thy.get_theorem(name)
        inst = dict()

        As, C = th.concl.strip_implies()
        for idx, prev_th in enumerate(prevs):
            Matcher.first_order_match_incr(As[idx], prev_th.concl, inst)
        if self.with_concl:
            Matcher.first_order_match_incr(C, concl, inst)
        return Thm(th.assums, C.subst_norm(inst))

    def expand(self, depth, thy, args, *prevs):
        if self.with_concl:
            name, concl = args
        else:
            name = args
        th = thy.get_theorem(name)
        inst = dict()

        As, C = th.concl.strip_implies()
        for idx, (_, arg) in enumerate(prevs):
            Matcher.first_order_match_incr(As[idx], arg.concl, inst)
        if self.with_concl:
            Matcher.first_order_match_incr(C, concl, inst)

        pt = ProofTerm.substitution(inst, ProofTerm.theorem(thy, name))
        cv = top_conv(beta_conv())
        pt2 = cv.get_proof_term(pt.th.concl)
        pt3 = ProofTerm.equal_elim(pt2, pt)
        for idx, (id, prev) in enumerate(prevs):
            pt3 = ProofTerm.implies_elim(pt3, ProofTerm.atom(id, prev))

        return pt3.export(depth)
