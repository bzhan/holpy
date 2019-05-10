# Author: Bohua Zhan

from typing import Tuple

from kernel.term import Term
from kernel import macro
from kernel.proof import Proof
from kernel.thm import Thm
from logic import logic, matcher
from logic.conv import then_conv, beta_conv, top_conv, rewr_conv, top_sweep_conv
from logic.proofterm import ProofTerm, ProofTermMacro, ProofTermDeriv, refl

"""Standard macros in logic."""

class arg_combination_macro(ProofTermMacro):
    """Given theorem x = y and term f, return f x = f y."""

    def __init__(self):
        self.level = 1
        self.sig = Term

    def eval(self, thy, f, ths):
        assert ths[0].prop.is_equals(), "arg_combination"
        return Thm.combination(Thm.reflexive(f), ths[0])

    def get_proof_term(self, thy, f, pts):
        assert pts[0].prop.is_equals(), "arg_combination"
        return ProofTerm.combination(refl(f), pts[0])

class fun_combination_macro(ProofTermMacro):
    """Given theorem f = g and term x, return f x = g x."""

    def __init__(self):
        self.level = 1
        self.sig = Term

    def eval(self, thy, x, ths):
        assert ths[0].prop.is_equals(), "fun_combination"
        return Thm.combination(ths[0], Thm.reflexive(x))

    def get_proof_term(self, thy, x, pts):
        assert pts[0].prop.is_equals(), "fun_combination"
        return ProofTerm.combination(pts[0], refl(x))

class beta_norm_macro(ProofTermMacro):
    """Given theorem th, return the normalization of th."""

    def __init__(self):
        self.level = 1
        self.sig = None

    def eval(self, thy, args, ths):
        assert args is None, "beta_norm_macro"
        cv = top_conv(beta_conv())
        eq_th = cv.eval(thy, ths[0].prop)
        return Thm(ths[0].hyps, eq_th.prop.arg)

    def get_proof_term(self, thy, args, pts):
        assert args is None, "beta_norm_macro"
        return top_conv(beta_conv()).apply_to_pt(thy, pts[0])

class intros_macro(ProofTermMacro):
    """Introduce assumptions and variables."""
    def get_proof_term(self, thy, args, prevs):
        assert len(prevs) >= 2, "intros_macro"
        pt, intros = prevs[-1], prevs[:-1]        
        for intro in reversed(intros):
            if intro.th.is_reflexive():
                pt = ProofTerm.forall_intr(intro.prop.rhs, pt)
            else:
                pt = ProofTerm.implies_intr(intro.prop, pt)
        return pt

class apply_theorem_macro(ProofTermMacro):
    """Apply existing theorem in the theory to a list of current
    results in the proof.

    If with_inst is set, the signature is (th_name, tyinst, inst),
    where th_name is the name of the theorem, and tyinst, inst are
    the instantiations of type and term variables.

    If with_inst is not set, the signature is th_name, where th_name
    is the name of the theorem.

    """
    def __init__(self, *, with_inst=False):
        self.level = 1
        self.with_inst = with_inst
        self.sig = Tuple[str, macro.TyInst, macro.Inst] if with_inst else str

    def eval(self, thy, args, prevs):
        tyinst, inst = dict(), dict()
        if self.with_inst:
            name, tyinst, inst = args
        else:
            name = args
        th = thy.get_theorem(name)

        if not self.with_inst:
            As = th.assums
            assert len(prevs) <= len(As), "apply_theorem_macro: too many prevs."
            for idx, prev_th in enumerate(prevs):
                matcher.first_order_match_incr(As[idx], prev_th.prop, (tyinst, inst))

        As, C = logic.subst_norm(th.prop, (tyinst, inst)).strip_implies()
        new_prop = Term.mk_implies(*(As[len(prevs):] + [C]))

        prev_hyps = sum([prev.hyps for prev in prevs], ())
        return Thm(th.hyps + prev_hyps, new_prop)

    def get_proof_term(self, thy, args, pts):
        tyinst, inst = dict(), dict()
        if self.with_inst:
            name, tyinst, inst = args
        else:
            name = args
        th = thy.get_theorem(name)

        if not self.with_inst:
            As = th.assums
            for idx, pt in enumerate(pts):
                matcher.first_order_match_incr(As[idx], pt.prop, (tyinst, inst))

        pt = ProofTerm.substitution(inst,
                ProofTerm.subst_type(tyinst, ProofTerm.theorem(thy, name)))
        if pt.prop.beta_norm() == pt.prop:
            pt2 = pt
        else:
            pt2 = top_conv(beta_conv()).apply_to_pt(thy, pt)
        for pt in pts:
            pt2 = ProofTerm.implies_elim(pt2, pt)

        return pt2

class rewrite_goal_macro(ProofTermMacro):
    """Apply an existing equality theorem to rewrite a goal.

    The signature is (name, goal), where name is the name of the
    equality theorem. Goal is the statement of the goal.

    Rewrite the goal using the equality theorem. The result must
    be equal to prev[0].

    The remainder of prev are theorems to be used to discharge
    assumptions in conversion.
    
    backward - whether to apply the given equality in the backward
    direction.

    """
    def __init__(self, *, backward=False):
        self.level = 1
        self.backward = backward
        self.sig = Tuple[str, Term]

    def eval(self, thy, args, ths):
        assert isinstance(args, tuple) and len(args) == 2 and \
               isinstance(args[0], str) and isinstance(args[1], Term), "rewrite_goal_macro: signature"

        # Simply produce the goal
        _, goal = args
        return Thm(sum([th.hyps for th in ths], ()), goal)

    def get_proof_term(self, thy, args, pts):
        assert isinstance(args, tuple) and len(args) == 2 and \
               isinstance(args[0], str) and isinstance(args[1], Term), "rewrite_goal_macro: signature"

        name, goal = args
        eq_pt = ProofTerm.theorem(thy, name)
        if self.backward:
            eq_pt = ProofTerm.symmetric(eq_pt)
        cv = then_conv(top_conv(rewr_conv(eq_pt)), top_conv(beta_conv()))
        pt = cv.get_proof_term(thy, goal)  # goal = th.prop
        pt = ProofTerm.symmetric(pt)  # th.prop = goal
        if Term.is_equals(pt.prop.lhs) and pt.prop.lhs.lhs == pt.prop.lhs.rhs:
            pt = ProofTerm.equal_elim(pt, ProofTerm.reflexive(pt.prop.lhs.lhs))
        else:
            pt = ProofTerm.equal_elim(pt, pts[0])  # goal
            pts = pts[1:]

        for A in pts:
            pt = ProofTerm.implies_elim(ProofTerm.implies_intr(A.prop, pt), A)
        return pt

class rewrite_fact_macro(ProofTermMacro):
    def __init__(self):
        self.level = 1
        self.sig = str

    def get_proof_term(self, thy, args, pts):
        assert len(pts) == 1 and isinstance(args, str), "rewrite_fact_macro: signature"

        th_name = args
        eq_pt = ProofTerm.theorem(thy, th_name)
        cv = then_conv(top_sweep_conv(rewr_conv(eq_pt)), top_conv(beta_conv()))
        return pts[0].on_prop(thy, cv)

class rewrite_goal_with_prev_macro(ProofTermMacro):
    def __init__(self, *, backward=False):
        self.level = 1
        self.backward = backward
        self.sig = Term

    def get_proof_term(self, thy, args, pts):
        assert isinstance(args, Term), "rewrite_goal_macro: signature"

        goal = args
        eq_pt = pts[0]
        pts = pts[1:]
        if self.backward:
            eq_pt = ProofTerm.symmetric(eq_pt)
        cv = then_conv(top_sweep_conv(rewr_conv(eq_pt, match_vars=False)),
                       top_conv(beta_conv()))
        pt = cv.get_proof_term(thy, goal)  # goal = th.prop
        pt = ProofTerm.symmetric(pt)  # th.prop = goal
        if Term.is_equals(pt.prop.lhs) and pt.prop.lhs.lhs == pt.prop.lhs.rhs:
            pt = ProofTerm.equal_elim(pt, ProofTerm.reflexive(pt.prop.lhs.rhs))
        else:
            pt = ProofTerm.equal_elim(pt, pts[0])
            pts = pts[1:]

        for A in pts:
            pt = ProofTerm.implies_elim(ProofTerm.implies_intr(A.prop, pt), A)
        return pt

def apply_theorem(thy, th_name, *pts, concl=None, tyinst=None, inst=None):
    """Wrapper for apply_theorem and apply_theorem_for macros.

    The function takes optional arguments concl, tyinst, and inst. Matching
    always starts with tyinst and inst. If conclusion is specified, it is
    matched next. Finally, the assumptions are matched.

    """
    if concl is None and tyinst is None and inst is None:
        # Normal case, can use apply_theorem
        return ProofTermDeriv("apply_theorem", thy, th_name, pts)
    else:
        pt = ProofTerm.theorem(thy, th_name)
        if tyinst is None:
            tyinst = dict()
        if inst is None:
            inst = dict()
        if concl is not None:
            matcher.first_order_match_incr(pt.concl, concl, (tyinst, inst))
        pt = ProofTermDeriv("apply_theorem_for", thy, (th_name, tyinst, inst), pts)
        if pt.prop.beta_norm() == pt.prop:
            return pt
        else:
            return ProofTermDeriv("beta_norm", thy, None, [pt])

class imp_conj_macro(ProofTermMacro):
    def __init__(self):
        self.level = 1
        self.sig = Term

    def eval(self, thy, args, ths):
        raise NotImplementedError

    def get_proof_term(self, thy, args, pts):
        return ProofTerm.assume(args)


macro.global_macros.update({
    "arg_combination": arg_combination_macro(),
    "fun_combination": fun_combination_macro(),
    "beta_norm": beta_norm_macro(),
    "intros": intros_macro(),
    "apply_theorem": apply_theorem_macro(),
    "apply_theorem_for": apply_theorem_macro(with_inst=True),
    "rewrite_goal": rewrite_goal_macro(),
    "rewrite_back_goal": rewrite_goal_macro(backward=True),
    "rewrite_goal_with_prev": rewrite_goal_with_prev_macro(),
    "rewrite_back_goal_with_prev": rewrite_goal_with_prev_macro(backward=True),
    "rewrite_fact": rewrite_fact_macro(),
})
