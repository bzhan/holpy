# Author: Bohua Zhan

from typing import Tuple, List

from kernel import term
from kernel.term import Term
from kernel import macro
from kernel.proof import Proof
from kernel.thm import Thm
from logic import logic, matcher
from logic.conv import then_conv, beta_conv, top_conv, rewr_conv, top_sweep_conv
from logic.proofterm import ProofTerm, ProofTermMacro, ProofTermDeriv, refl

"""Standard macros in logic."""

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
    def __init__(self):
        self.level = 1
        self.sig = List[Term]

    def get_proof_term(self, thy, args, prevs):
        assert len(prevs) >= 2, "intros_macro"
        if args is None:
            args = []
        pt, intros = prevs[-1], prevs[:-1]        
        for intro in reversed(intros):
            if intro.th.prop.is_VAR():  # variable case
                pt = ProofTerm.forall_intr(intro.prop.arg, pt)
            elif len(args) > 0 and intro.th.prop == args[0]:  # exists case
                assert logic.is_exists(intro.prop), "intros_macro"
                pt = apply_theorem(thy, 'exE', intro, pt)
                args = args[1:]
            else:  # assume case
                assert len(intro.th.hyps) == 1 and intro.th.hyps[0] == intro.th.prop, \
                    "intros_macro"
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

        pt = ProofTerm.theorem(thy, name)
        if tyinst:
            pt = ProofTerm.subst_type(tyinst, pt)
        if inst:
            pt = ProofTerm.substitution(inst, pt)
        if pt.prop.beta_norm() != pt.prop:
            pt = top_conv(beta_conv()).apply_to_pt(thy, pt)
        for prev_pt in pts:
            pt = ProofTerm.implies_elim(pt, prev_pt)

        return pt

class apply_fact_macro(ProofTermMacro):
    """Apply a given fact to a list of facts."""
    def __init__(self):
        self.level = 1
        self.sig = None

    def get_proof_term(self, thy, args, pts):
        pt, pt_prevs = pts[0], pts[1:]

        # First, obtain the patterns
        vars = term.get_vars(pt.prop)
        new_names = logic.get_forall_names(pt.prop)
        assert {v.name for v in vars}.isdisjoint(set(new_names)), "apply_fact: name conflict"
        new_vars, As, C = logic.strip_all_implies(pt.prop, new_names)
        assert len(pt_prevs) <= len(As), "apply_fact: too many prevs"

        tyinst, inst = dict(), {v.name: v for v in vars}
        for idx, pt_prev in enumerate(pt_prevs):
            matcher.first_order_match_incr(As[idx], pt_prev.prop, (tyinst, inst))

        if tyinst:
            pt = ProofTerm.subst_type(tyinst, pt)
        for new_name in new_names:
            pt = ProofTerm.forall_elim(inst[new_name], pt)
        if pt.prop.beta_norm() != pt.prop:
            pt = top_conv(beta_conv()).apply_to_pt(thy, pt)
        for prev_pt in pt_prevs:
            pt = ProofTerm.implies_elim(pt, prev_pt)

        return pt

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
    """Given an input equality theorem and a goal, the macro rewrites
    the goal to a new form. The new goal, if it is not a reflexivity, is
    resolved using the second input theorem. The remaining input theorems
    are used to resolve conditions that arise when applying the equality.

    """
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

class rewrite_fact_with_prev_macro(ProofTermMacro):
    """This macro is provided with two input theorems. The first input
    theorem is an equality, which is used to rewrite the second input
    theorem.

    """
    def __init__(self):
        self.level = 1
        self.sig = None

    def get_proof_term(self, thy, args, pts):
        eq_pt, pt = pts
        cv = then_conv(top_sweep_conv(rewr_conv(eq_pt, match_vars=False)),
                       top_conv(beta_conv()))
        return pt.on_prop(thy, cv)


class trivial_macro(ProofTermMacro):
    """Prove a proposition of the form A_1 --> ... --> A_n --> B, where
    B agrees with one of A_i.

    """
    def __init__(self):
        self.level = 1
        self.sig = Term

    def can_eval(self, thy, args):
        As, C = args.strip_implies()
        return C in As

    def get_proof_term(self, thy, args, pts):
        As, C = args.strip_implies()
        assert C in As, "trivial_macro"

        pt = ProofTerm.assume(C)
        for A in reversed(As):
            pt = ProofTerm.implies_intr(A, pt)
        return pt

class resolve_theorem_macro(ProofTermMacro):
    """Given a theorem of the form ~A, and a fact A, prove any goal."""
    def __init__(self):
        self.level = 1
        self.sig = Tuple[str, Term]

    def get_proof_term(self, thy, args, pts):
        th_name, goal = args
        pt = ProofTerm.theorem(thy, th_name)
        assert logic.is_neg(pt.prop), "resolve_theorem_macro"

        # Match for variables in pt.
        tyinst, inst = matcher.first_order_match(pt.prop.arg, pts[0].prop)
        if tyinst:
            pt = ProofTerm.subst_type(tyinst, pt)
        if inst:
            pt = ProofTerm.substitution(inst, pt)

        pt = apply_theorem(thy, 'negE', pt, pts[0])  # false
        return apply_theorem(thy, 'falseE', pt, concl=goal)


def apply_theorem(thy, th_name, *pts, concl=None, tyinst=None, inst=None):
    """Wrapper for apply_theorem and apply_theorem_for macros.

    The function takes optional arguments concl, tyinst, and inst. Matching
    always starts with tyinst and inst. If conclusion is specified, it is
    matched next. Finally, the assumptions are matched.

    """
    assert isinstance(pts, tuple) and all(isinstance(pt, ProofTerm) for pt in pts), \
        "apply_theorem: *pts must be a list of theorems."
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
        return ProofTermDeriv("apply_theorem_for", thy, (th_name, tyinst, inst), pts)


class imp_conj_macro(ProofTermMacro):
    def __init__(self):
        self.level = 1
        self.sig = Term

    def eval(self, thy, args, ths):
        def strip(t):
            if logic.is_conj(t):
                return strip(t.arg1).union(strip(t.arg))
            else:
                return {t}

        As, C = args.strip_implies()
        assert len(As) == 1, 'imp_conj_macro'
        assert strip(C).issubset(strip(As[0])), 'imp_conj_macro'
        return Thm([], args)

    def get_proof_term(self, thy, args, pts):
        dct = dict()

        def traverse_A(pt):
            # Given proof term showing a conjunction, put proof terms
            # showing atoms of the conjunction in dct.
            if logic.is_conj(pt.prop):
                traverse_A(apply_theorem(thy, 'conjD1', pt))
                traverse_A(apply_theorem(thy, 'conjD2', pt))
            else:
                dct[pt.prop] = pt

        def traverse_C(t):
            # Return proof term with conclusion t
            if logic.is_conj(t):
                left = traverse_C(t.arg1)
                right = traverse_C(t.arg)
                return apply_theorem(thy, 'conjI', left, right)
            else:
                assert t in dct.keys(), 'imp_conj_macro'
                return dct[t]

        As, C = args.strip_implies()
        assert len(As) == 1, 'imp_conj_macro'
        A = As[0]

        traverse_A(ProofTerm.assume(A))
        concl = traverse_C(C)
        return ProofTerm.implies_intr(A, concl)


macro.global_macros.update({
    "beta_norm": beta_norm_macro(),
    "intros": intros_macro(),
    "apply_theorem": apply_theorem_macro(),
    "apply_theorem_for": apply_theorem_macro(with_inst=True),
    "resolve_theorem": resolve_theorem_macro(),
    "apply_fact": apply_fact_macro(),
    "rewrite_goal": rewrite_goal_macro(),
    "rewrite_back_goal": rewrite_goal_macro(backward=True),
    "rewrite_goal_with_prev": rewrite_goal_with_prev_macro(),
    "rewrite_back_goal_with_prev": rewrite_goal_with_prev_macro(backward=True),
    "rewrite_fact": rewrite_fact_macro(),
    "rewrite_fact_with_prev": rewrite_fact_with_prev_macro(),
    "trivial": trivial_macro(),
})
