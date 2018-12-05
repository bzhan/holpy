# Author: Bohua Zhan

from kernel.term import Term
from kernel.macro import MacroSig, ProofMacro
from kernel.proof import Proof
from kernel.thm import Thm
from logic.conv import beta_conv, top_conv, rewr_conv
from logic.matcher import Matcher
from logic.proofterm import ProofTerm
from logic.logic import Logic

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

    def expand(self, depth, f, prev):
        id, th = prev
        assert th.concl.is_equals(), "arg_combination"

        prf = Proof()
        prf.add_item((depth, "S1"), "reflexive", args=f)
        prf.add_item("C", "combination", prevs=[(depth, "S1"), id])
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

    def expand(self, depth, x, prev):
        id, th = prev
        assert th.concl.is_equals(), "fun_combination"

        prf = Proof()
        prf.add_item((depth, "S1"), "reflexive", args=x)
        prf.add_item("C", "combination", prevs=[id, (depth, "S1")])
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

    def expand(self, depth, prev):
        id, th = prev
        cv = top_conv(beta_conv())
        pt = cv.get_proof_term(th.concl)
        pt2 = ProofTerm.equal_elim(pt, ProofTerm.atom(id, th))
        return pt2.export(depth)

class apply_theorem_macro(ProofMacro):
    """Apply existing theorem in the theory to a list of current
    results in the proof.

    If with_inst is set, the signature is (th_name, concl), where
    th_name is the name of the theorem, concl is the expected conclusion.

    If with_inst is not set, the signature is th_name, where th_name
    is the name of the theorem.

    """
    def __init__(self, *, with_inst=False):
        self.level = 1
        self.with_inst = with_inst
        self.sig = MacroSig.STRING_INST if with_inst else MacroSig.STRING
        self.has_theory = True

    def __call__(self, thy, args, *prevs):
        inst = dict()
        if self.with_inst:
            name, inst = args
        else:
            name = args
        th = thy.get_theorem(name)

        if not self.with_inst:
            As, _ = th.concl.strip_implies()
            for idx, prev_th in enumerate(prevs):
                Matcher.first_order_match_incr(As[idx], prev_th.concl, inst)

        As, C = Logic.subst_norm(th.concl, inst).strip_implies()
        new_concl = Term.mk_implies(*(As[len(prevs):] + [C]))

        return Thm(th.assums, new_concl)

    def expand(self, depth, thy, args, *prevs):
        inst = dict()
        if self.with_inst:
            name, inst = args
        else:
            name = args
        th = thy.get_theorem(name)

        if not self.with_inst:
            As, _ = th.concl.strip_implies()
            for idx, (_, arg) in enumerate(prevs):
                Matcher.first_order_match_incr(As[idx], arg.concl, inst)

        pt = ProofTerm.substitution(inst, ProofTerm.theorem(thy, name))
        cv = top_conv(beta_conv())
        pt2 = cv.get_proof_term(pt.th.concl)
        pt3 = ProofTerm.equal_elim(pt2, pt)
        for idx, (id, prev) in enumerate(prevs):
            pt3 = ProofTerm.implies_elim(pt3, ProofTerm.atom(id, prev))

        return pt3.export(depth)

class rewrite_goal_macro(ProofMacro):
    """Apply an existing equality theorem to rewrite a goal.

    The signature is (name, goal), where name is the name of the
    equality theorem. Goal is the statement of the goal.

    Rewrite the goal using the equality theorem. The result must
    be equal to prev.
    
    backward - whether to apply the given equality in the backward
    direction.

    """
    def __init__(self, *, backward=False):
        self.level = 1
        self.backward = backward
        self.sig = MacroSig.STRING_TERM
        self.has_theory = True

    def __call__(self, thy, args, th):
        assert isinstance(args, tuple) and len(args) == 2 and \
               isinstance(args[0], str) and isinstance(args[1], Term), "rewrite_goal_macro: signature"

        # Simply produce the goal
        _, goal = args
        return Thm(th.assums, goal)

    def expand(self, depth, thy, args, prev):
        assert isinstance(args, tuple) and len(args) == 2 and \
               isinstance(args[0], str) and isinstance(args[1], Term), "rewrite_goal_macro: signature"

        name, goal = args
        id, th = prev
        eq_pt = ProofTerm.theorem(thy, name)
        if self.backward:
            eq_pt = ProofTerm.symmetric(eq_pt)
        cv = top_conv(rewr_conv(eq_pt))
        pt = cv.get_proof_term(goal)  # goal = th.concl
        pt2 = ProofTerm.symmetric(pt)  # th.concl = goal
        pt3 = ProofTerm.equal_elim(pt2, ProofTerm.atom(id, th))
        return pt3.export(depth)
