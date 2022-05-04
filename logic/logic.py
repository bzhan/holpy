# Author: Bohua Zhan

from typing import List, Tuple

from kernel.type import TVar, TFun, TyInst, BoolType
from kernel import term
from kernel.term import Term, SVar, Var, Const, Abs, Inst, Implies, Lambda, \
    Not, And, Or, Eq, true, false
from kernel.thm import Thm, InvalidDerivationException
from kernel import term_ord
from kernel import theory
from kernel.theory import register_macro
from kernel.macro import Macro
from logic.conv import Conv, then_conv, all_conv, arg_conv, binop_conv, rewr_conv, \
    top_conv, top_sweep_conv, beta_conv, beta_norm_conv, has_rewrite
from kernel.proofterm import ProofTerm, refl
from logic import matcher
from util import name
from util import typecheck


"""Utility functions for logic."""

def is_exists1(t):
    """Whether t is of the form ?!x. P x."""
    return t.is_comb('exists1', 1)

def mk_exists1(x, body):
    """Given a variable x and a term P possibly depending on x, return
    the term ?!x. P.

    """
    assert x.is_var(), "mk_exists1"
    exists1_t = Const("exists1", TFun(TFun(x.T, BoolType), BoolType))
    return exists1_t(Lambda(x, body))

def is_the(t):
    """Whether t is of the form THE x. P x."""
    return t.is_comb('The', 1)

def mk_the(x, body):
    """Given a variable x and a term P possibly depending on x, return
    the term THE x. P.

    """
    assert x.is_var(), "mk_the"
    the_t = Const("The", TFun(TFun(x.T, BoolType), x.T))
    return the_t(Lambda(x, body))

def is_some(t):
    """Whether t is of the form SOME x. P x."""
    return t.is_comb('Some', 1)

def mk_some(x, body):
    """Given a variable x and a term P possibly depending on x, return
    the term SOME x. P.

    """
    assert x.is_var(), "mk_some"
    some_t = Const("Some", TFun(TFun(x.T, BoolType), x.T))
    return some_t(Lambda(x, body))

def if_t(T):
    return Const("IF", TFun(BoolType, T, T, T))

def is_if(t):
    """Whether t is of the form if P then x else y."""
    return t.is_comb("IF", 3)

def mk_if(P, x, y):
    """Obtain the term if P then x else y."""
    return if_t(x.get_type())(P, x, y)

def get_forall_names(t, svar=True):
    """Given a term of the form

    !x_1 ... x_k. A_1 --> ... --> A_n --> C.

    return the names x_1, ... x_k.

    """
    def helper(t):
        if t.is_forall():
            return [t.arg.var_name] + helper(t.arg.body)
        else:
            return []
    old_names = []
    if not svar:
        old_names = [v.name for v in t.get_vars()]
    return name.get_variant_names(helper(t), old_names)

def strip_all_implies(t, names, svar=True):
    """Given a term of the form

    !x_1 ... x_k. A_1 --> ... --> A_n --> C.

    Return the triple ([v_1, ..., v_k], [A_1, ... A_n], C), where
    v_1, ..., v_k are new variables with the given names, and
    A_1, ..., A_n, C are the body of the input term, with bound variables
    substituted for v_1, ..., v_k.

    """
    if t.is_forall():
        assert len(names) > 0, "strip_all_implies: not enough names input."
        assert isinstance(names[0], str), "strip_all_implies: names must be strings."
        if svar:
            v = SVar(names[0], t.arg.var_T)
        else:
            v = Var(names[0], t.arg.var_T)
        vars, As, C = strip_all_implies(t.arg.subst_bound(v), names[1:], svar=svar)
        return ([v] + vars, As, C)
    else:
        assert len(names) == 0, "strip_all_implies: too many names input."
        As, C = t.strip_implies()
        return ([], As, C)

def strip_exists(t, names):
    """Given a term of the form

    ?x_1 ... x_k. C

    Return the pair ([v_1, ..., v_k], C), where C is the body of the
    input term, with bound variables substituted for v_1, ..., v_k.

    """
    if t.is_exists() and len(names) > 0:
        assert isinstance(names[0], str), "strip_exists: names must be strings."
        v = Var(names[0], t.arg.var_T)
        vars, body = strip_exists(t.arg.subst_bound(v), names[1:])
        return ([v] + vars, body)
    else:
        return ([], t)

def mk_xor(x: Term, y: Term) -> Term:
    assert x.get_type() == BoolType and y.get_type() == BoolType
    return Const("xor", TFun(BoolType, BoolType, BoolType))(x, y)

def is_xor(t: Term):
    return t.is_comb('xor', 2)

"""Normalization rules for logic."""

class norm_bool_expr(Conv):
    """Normalize a boolean expression."""
    def get_proof_term(self, t):
        if t.is_not():
            if t.arg == true:
                return rewr_conv("not_true").get_proof_term(t)
            elif t.arg == false:
                return rewr_conv("not_false").get_proof_term(t)
            else:
                return refl(t)
        else:
            return refl(t)

class norm_conj_assoc_clauses(Conv):
    """Normalize (A_1 & ... & A_n) & (B_1 & ... & B_n)."""
    def get_proof_term(self, t):
        if t.arg1.is_conj():
            return then_conv(
                rewr_conv("conj_assoc", sym=True),
                arg_conv(norm_conj_assoc_clauses())
            ).get_proof_term(t)
        else:
            return all_conv().get_proof_term(t)

class norm_conj_assoc(Conv):
    """Normalize conjunction with respect to associativity."""
    def get_proof_term(self, t):
        if t.is_conj():
            return then_conv(
                binop_conv(norm_conj_assoc()),
                norm_conj_assoc_clauses()
            ).get_proof_term(t)
        else:
            return all_conv().get_proof_term(t)

"""Standard macros in logic."""

class beta_norm_macro(Macro):
    """Given theorem th, return the normalization of th."""
    def __init__(self):
        self.level = 1
        self.sig = None
        self.limit = None

    def eval(self, args, ths):
        assert args is None, "beta_norm_macro"
        eq_th = beta_norm_conv().eval(ths[0].prop)
        return Thm(eq_th.prop.arg, ths[0].hyps)

    def get_proof_term(self, args, pts):
        assert args is None, "beta_norm_macro"
        return pts[0].on_prop(beta_norm_conv())

class intros_macro(Macro):
    """Introduce assumptions and variables."""
    def __init__(self):
        self.level = 1
        self.sig = List[Term]
        self.limit = None

    def get_proof_term(self, args, prevs):
        assert len(prevs) >= 1, "intros_macro"
        if args is None:
            args = []
        pt, intros = prevs[-1], prevs[:-1]
        if len(prevs) == 1:
            return apply_theorem('trivial', pt)

        for intro in reversed(intros):
            if intro.th.prop.is_VAR():  # variable case
                pt = pt.forall_intr(intro.prop.arg)
            elif len(args) > 0 and intro.th.prop == args[0]:  # exists case
                assert intro.prop.is_exists(), "intros_macro"
                pt = apply_theorem('exE', intro, pt)
                args = args[1:]
            else:  # assume case
                assert len(intro.th.hyps) == 1 and intro.th.hyps[0] == intro.th.prop, \
                    "intros_macro"
                pt = pt.implies_intr(intro.prop)
        return pt

class apply_theorem_macro(Macro):
    """Apply existing theorem in the theory to a list of current
    results in the proof.

    If with_inst is set, the signature is (th_name, inst),
    where th_name is the name of the theorem, and inst are
    the instantiations of type and term variables.

    If with_inst is not set, the signature is th_name, where th_name
    is the name of the theorem.

    """
    def __init__(self, *, with_inst=False):
        self.level = 1
        self.with_inst = with_inst
        self.sig = Tuple[str, Inst] if with_inst else str
        self.limit = None

    def eval(self, args, prevs):
        if self.with_inst:
            name, inst = args
        else:
            name = args
            inst = Inst()
        th = theory.get_theorem(name)
        As, C = th.prop.strip_implies()

        assert len(prevs) <= len(As), "apply_theorem: too many prevs."

        # First attempt to match type variables
        svars = th.prop.get_svars()
        for v in svars:
            if v.name in inst:
                v.T.match_incr(inst[v.name].get_type(), inst.tyinst)

        pats = As[:len(prevs)]
        ts = [prev_th.prop for prev_th in prevs]
        inst = matcher.first_order_match_list(pats, ts, inst)

        # Check that all type variables are instantiated
        for stvar in th.prop.get_stvars():
            assert stvar.name in inst.tyinst, "apply_theorem: unmatched type variable %s" % stvar

        # If theorem is a first-order pattern, there is no need for beta_norm.
        if matcher.is_fo_pattern(th.prop):
            As, C = th.prop.subst(inst).strip_implies()
        else:
            As, C = th.prop.subst_norm(inst).strip_implies()
        new_prop = Implies(*(As[len(prevs):] + [C]))

        th = Thm(new_prop, th.hyps, *(prev.hyps for prev in prevs))

        # Obtain list of remaining schematic variables
        remain_svars = [t.subst_type(inst.tyinst) for t in svars if t.name not in inst]
        for v in reversed(remain_svars):
            th = Thm.forall_intr(v, th)
        return th

    def get_proof_term(self, args, pts):
        if self.with_inst:
            name, inst = args
        else:
            name = args
            inst = Inst()
        th = theory.get_theorem(name)
        As, C = th.prop.strip_implies()

        assert len(pts) <= len(As), "apply_theorem: too many prevs."

        # First attempt to match type variables
        svars = th.prop.get_svars()
        for v in svars:
            if v.name in inst:
                v.T.match_incr(inst[v.name].get_type(), inst.tyinst)

        pats = As[:len(pts)]
        ts = [pt.prop for pt in pts]
        inst = matcher.first_order_match_list(pats, ts, inst)

        pt = ProofTerm.theorem(name)
        pt = pt.subst_type(inst.tyinst).substitution(inst)

        # Apply beta_norm when theorem is a first-order pattern.
        if not matcher.is_fo_pattern(th.prop):
            pt = pt.on_prop(beta_norm_conv())
        pt = pt.implies_elim(*pts)

        assert len(pt.prop.get_stvars()) == 0, "apply_theorem: unmatched type variables."
        vars = pt.prop.get_svars()
        for v in reversed(vars):
            pt = pt.forall_intr(v)

        return pt

class apply_fact_macro(Macro):
    """Apply a given fact to a list of facts. The first input fact is
    in the forall-implies form. Apply this fact to the remaining
    input facts. If with_inst is set, use the given sequence of terms
    as the instantiation.
    
    """
    def __init__(self, *, with_inst=False):
        self.level = 1
        self.with_inst = with_inst
        self.sig = List[Term] if with_inst else None
        self.limit = None

    def get_proof_term(self, args, pts):
        if not self.with_inst:
            assert len(pts) >= 2, "apply fact: too few prevs"

        pt, pt_prevs = pts[0], pts[1:]

        # First, obtain the patterns
        new_names = get_forall_names(pt.prop)

        new_vars, As, C = strip_all_implies(pt.prop, new_names)
        assert len(pt_prevs) <= len(As), "apply_fact: too many prevs"

        if self.with_inst:
            assert len(args) == len(new_names), "apply_fact_macro: wrong number of args."
            inst = Inst({nm: v for nm, v in zip(new_names, args)})
        else:
            inst = Inst()
            for idx, pt_prev in enumerate(pt_prevs):
                inst = matcher.first_order_match(As[idx], pt_prev.prop, inst)

        pt = pt.subst_type(inst.tyinst)
        for new_var in new_vars:
            if new_var.name in inst:
                pt = pt.forall_elim(inst[new_var.name])
            else:
                pt = pt.forall_elim(new_var)
        if pt.prop.beta_norm() != pt.prop:
            pt = pt.on_prop(beta_norm_conv())
        for prev_pt in pt_prevs:
            if prev_pt.prop != pt.assums[0]:
                prev_pt = prev_pt.on_prop(beta_norm_conv())
            pt = pt.implies_elim(prev_pt)
        for new_var in new_vars:
            if new_var.name not in inst:
                pt = pt.forall_intr(new_var)

        return pt

class rewrite_goal_macro(Macro):
    """Apply an existing equality theorem to rewrite a goal.

    The signature is (name, goal), where name is the name of the
    equality theorem. Goal is the statement of the goal.

    Rewrite the goal using the equality theorem. The result must
    be equal to prev[0].

    The remainder of prev are theorems to be used to discharge
    assumptions in conversion.
    
    sym - whether to apply the given equality in the backward direction.

    """
    def __init__(self, *, sym=False):
        self.level = 1
        self.sym = sym
        self.sig = Tuple[str, Term]
        self.limit = None

    def eval(self, args, ths):
        assert isinstance(args, tuple) and len(args) == 2 and \
               isinstance(args[0], str) and isinstance(args[1], Term), "rewrite_goal: signature"

        # Simply produce the goal
        _, goal = args
        return Thm(goal, *(th.hyps for th in ths))

    def get_proof_term(self, args, pts):
        assert isinstance(args, tuple) and len(args) == 2 and \
               isinstance(args[0], str) and isinstance(args[1], Term), "rewrite_goal: signature"

        name, goal = args
        eq_pt = ProofTerm.theorem(name)

        if len(pts) == len(eq_pt.assums):
            rewr_cv = rewr_conv(eq_pt, sym=self.sym, conds=pts)
        else:
            assert len(pts) == len(eq_pt.assums) + 1, "rewrite_goal: wrong number of prevs"
            rewr_cv = rewr_conv(eq_pt, sym=self.sym, conds=pts[1:])

        cv = then_conv(top_sweep_conv(rewr_cv), beta_norm_conv())
        pt = cv.get_proof_term(goal)  # goal = th.prop
        pt = pt.symmetric()           # th.prop = goal
        if pt.prop.lhs.is_equals() and pt.prop.lhs.lhs == pt.prop.lhs.rhs:
            pt = pt.equal_elim(refl(pt.prop.lhs.lhs))
        else:
            pt = pt.equal_elim(pts[0])  # goal

        return pt

class rewrite_fact_macro(Macro):
    """Rewrite a fact in the proof using a theorem."""
    def __init__(self, *, sym=False):
        self.level = 1
        self.sym = sym
        self.sig = str
        self.limit = None

    def get_proof_term(self, args, pts):
        assert isinstance(args, str), "rewrite_fact_macro: signature"

        th_name = args
        eq_pt = ProofTerm.theorem(th_name)

        assert len(pts) == len(eq_pt.assums) + 1, "rewrite_fact_macro: signature"

        # Check rewriting using the theorem has an effect
        if not has_rewrite(th_name, pts[0].prop, sym=self.sym, conds=pts[1:]):
            raise InvalidDerivationException("rewrite_fact using %s" % th_name)

        cv = then_conv(top_sweep_conv(rewr_conv(eq_pt, sym=self.sym, conds=pts[1:])),
                       beta_norm_conv())
        res = pts[0].on_prop(cv)
        if res == pts[0]:
            raise InvalidDerivationException("rewrite_fact using %s" % th_name)
        return res

class rewrite_goal_with_prev_macro(Macro):
    """Given an input equality theorem and a goal, the macro rewrites
    the goal to a new form. The new goal, if it is not a reflexivity, is
    resolved using the second input theorem. The remaining input theorems
    are used to resolve conditions that arise when applying the equality.

    """
    def __init__(self, *, sym=False):
        self.level = 1
        self.sym = sym
        self.sig = Term
        self.limit = None

    def get_proof_term(self, args, pts):
        assert isinstance(args, Term), "rewrite_goal_macro: signature"

        goal = args
        eq_pt = pts[0]

        new_names = get_forall_names(eq_pt.prop)
        new_vars, _, _ = strip_all_implies(eq_pt.prop, new_names)

        for new_var in new_vars:
            eq_pt = eq_pt.forall_elim(new_var)

        pts = pts[1:]

        cv = then_conv(top_sweep_conv(rewr_conv(eq_pt, sym=self.sym)),
                       beta_norm_conv())
        pt = cv.get_proof_term(goal)  # goal = th.prop
        pt = pt.symmetric()           # th.prop = goal
        if pt.prop.lhs.is_reflexive():
            pt = pt.equal_elim(refl(pt.prop.lhs.rhs))
        else:
            pt = pt.equal_elim(pts[0])
            pts = pts[1:]

        for A in pts:
            pt = pt.implies_intr(A.prop).implies_elim(A)
        return pt

class rewrite_fact_with_prev_macro(Macro):
    """This macro is provided with two input theorems. The first input
    theorem is an equality, which is used to rewrite the second input
    theorem.

    """
    def __init__(self):
        self.level = 1
        self.sig = None
        self.limit = None

    def get_proof_term(self, args, pts):
        assert len(pts) == 2, "rewrite_fact_with_prev"

        eq_pt, pt = pts

        # In general, we assume eq_pt has forall quantification
        # First, obtain the patterns
        new_names = get_forall_names(eq_pt.prop)
        new_vars, eq_As, eq_C = strip_all_implies(eq_pt.prop, new_names)

        # First fact must be an equality
        assert len(eq_As) == 0 and eq_C.is_equals(), "rewrite_fact_with_prev"

        for new_var in new_vars:
            eq_pt = eq_pt.forall_elim(new_var)

        # Check rewriting using eq_pt has an effect
        cv1 = top_sweep_conv(rewr_conv(eq_pt))
        assert not cv1.eval(pt.prop).is_reflexive(), "rewrite_fact_with_prev"

        cv = then_conv(cv1, beta_norm_conv())
        return pt.on_prop(cv)

class forall_elim_gen_macro(Macro):
    """Apply forall elimination."""
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def get_proof_term(self, args, pts):
        assert len(pts) == 1, "forall_elim_gen"
        assert isinstance(args, Term), "forall_elim_gen"
        s = args  # term to instantiate

        pt = pts[0].forall_elim(s)
        if pt.prop.beta_norm() != pt.prop:
            pt = pt.on_prop(beta_norm_conv())
        return pt

class trivial_macro(Macro):
    """Prove a proposition of the form A_1 --> ... --> A_n --> B, where
    B agrees with one of A_i.

    """
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def can_eval(self, args):
        new_names = get_forall_names(args)
        vars, As, C = strip_all_implies(args, new_names)
        return C in As

    def get_proof_term(self, args, pts):
        new_names = get_forall_names(args)
        vars, As, C = strip_all_implies(args, new_names)
        assert C in As, "trivial_macro"

        pt = ProofTerm.assume(C)
        for A in reversed(As):
            pt = pt.implies_intr(A)
        for v in reversed(vars):
            pt = pt.forall_intr(v)
        return pt

class resolve_theorem_macro(Macro):
    """Given a theorem of the form ~A, and a fact A, prove any goal."""
    def __init__(self):
        self.level = 1
        self.sig = Tuple[str, Term]
        self.limit = None

    def get_proof_term(self, args, pts):
        th_name, goal = args
        pt = ProofTerm.theorem(th_name)
        assert pt.prop.is_not(), "resolve_theorem_macro"

        # Match for variables in pt.
        inst = matcher.first_order_match(pt.prop.arg, pts[0].prop)
        pt = pt.subst_type(inst.tyinst).substitution(inst)
        pt = apply_theorem('negE', pt, pts[0])  # false
        return apply_theorem('falseE', pt, concl=goal)


def apply_theorem(th_name, *pts, concl=None, inst=None):
    """Wrapper for apply_theorem and apply_theorem_for macros.

    The function takes optional arguments concl, inst. Matching
    always starts with inst. If conclusion is specified, it is
    matched next. Finally, the assumptions are matched.

    """
    typecheck.checkinstance('apply_theorem', pts, [ProofTerm])
    if concl is None and inst is None:
        # Normal case, can use apply_theorem
        return ProofTerm("apply_theorem", th_name, pts)
    else:
        pt = ProofTerm.theorem(th_name)
        if inst is None:
            inst = Inst()
        if concl is not None:
            inst = matcher.first_order_match(pt.concl, concl, inst)
        for i, prev in enumerate(pts):
            inst = matcher.first_order_match(pt.assums[i], prev.prop, inst)
        return ProofTerm("apply_theorem_for", (th_name, inst), pts)

def conj_thms(*pts):
    assert len(pts) > 0, 'conj_thms: input list is empty.'
    if len(pts) == 1:
        return pts[0]
    else:
        return apply_theorem('conjI', pts[0], conj_thms(*pts[1:]))


@register_macro('imp_conj')
class imp_conj_macro(Macro):
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def eval(self, goal, ths):
        # goal: A --> B
        A, B = goal.arg1, goal.arg
        conjA = set(strip_conj(A)) - {true}
        conjB = set(strip_conj(B)) - {true}
        assert conjB <= conjA, "imp_conj: subset relation does not hold"
        return Thm(goal)

    def get_proof_term(self, goal, pts):
        dct = dict()

        def traverse_A(pt):
            # Given proof term showing a conjunction, put proof terms
            # showing atoms of the conjunction in dct.
            if pt.prop.is_conj():
                traverse_A(apply_theorem('conjD1', pt))
                traverse_A(apply_theorem('conjD2', pt))
            elif pt.prop == true:
                pass
            else:
                dct[pt.prop] = pt

        def traverse_C(t):
            # Return proof term with conclusion t
            if t.is_conj():
                left = traverse_C(t.arg1)
                right = traverse_C(t.arg)
                return apply_theorem('conjI', left, right)
            elif t == true:
                return apply_theorem('trueI')
            else:
                assert t in dct.keys(), 'imp_conj_macro'
                return dct[t]

        A = goal.arg1
        traverse_A(ProofTerm.assume(A))
        return traverse_C(goal.arg).implies_intr(A)

def imp_conj_iff(goal: Term) -> ProofTerm:
    """Goal is of the form A_1 & ... & A_m <--> B_1 & ... & B_n, where
    the sets {A_1, ..., A_m} and {B_1, ..., B_n} are equal."""
    pt1 = ProofTerm('imp_conj', Implies(goal.lhs, goal.rhs))
    pt2 = ProofTerm('imp_conj', Implies(goal.rhs, goal.lhs))
    return ProofTerm.equal_intr(pt1, pt2)


@register_macro('imp_disj')
class imp_disj_macro(Macro):
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def eval(self, goal, pts):
        # goal: A --> B
        A, B = goal.arg1, goal.arg
        disjA = set(strip_disj(A))
        disjB = set(strip_disj(B))
        assert disjA <= disjB, "imp_disj: subset relation does not hold"
        return Thm(goal)

    def get_proof_term(self, goal, pts):
        """Goal is of the form A_1 | ... | A_m --> B_1 | ...| B_n, where
        {A_1, ..., A_m} is a subset of {B_1, ..., B_n}."""

        # Dictionary from B_i to B_i --> B_1 | ... | B_n
        pts_B = dict()
        
        # Fills up pts_B.
        def traverse_C(pt):
            if pt.prop.arg1.is_disj():
                pt1 = apply_theorem('disjI1', concl=pt.prop.arg1)
                pt2 = apply_theorem('disjI2', concl=pt.prop.arg1)
                traverse_C(apply_theorem('syllogism', pt1, pt))
                traverse_C(apply_theorem('syllogism', pt2, pt))
            else:
                pts_B[pt.prop.arg1] = pt
        
        # Use pts_B to prove the implication
        def traverse_A(t):
            if t.is_disj():
                pt1 = traverse_A(t.arg1)
                pt2 = traverse_A(t.arg)
                return apply_theorem('disjE2', pt1, pt2)
            else:
                assert t in pts_B, "imp_disj: %s not found in conclusion" % t
                return pts_B[t]
            
        triv = apply_theorem('trivial', inst=Inst(A=goal.arg))
        traverse_C(triv)
        return traverse_A(goal.arg1)

def imp_disj_iff(goal: Term):
    """Goal is of the form A_1 | ... | A_m <--> B_1 | ... | B_n, where
    the sets {A_1, ..., A_m} and {B_1, ..., B_n} are equal."""
    pt1 = ProofTerm('imp_disj', Implies(goal.lhs, goal.rhs))
    pt2 = ProofTerm('imp_disj', Implies(goal.rhs, goal.lhs))
    return ProofTerm.equal_intr(pt1, pt2)

def strip_disj(t):
    res = []
    def helper(t):
        if t.is_disj():
            ts = t.strip_disj()
            for sub_t in ts:
                helper(sub_t)
        else:
            res.append(t)
    helper(t)
    return res

def strip_conj(t):
    res = []
    def helper(t):
        if t.is_conj():
            ts = t.strip_conj()
            for sub_t in ts:
                helper(sub_t)
        else:
            res.append(t)
    helper(t)
    return res

class disj_norm(Conv):
    """Normalize an disjunction."""
    def get_proof_term(self, t):
        goal = Eq(t, Or(*term_ord.sorted_terms(strip_disj(t))))
        return imp_disj_iff(goal)

class conj_norm(Conv):
    """Normalize an conjunction."""
    def get_proof_term(self, t):
        goal = Eq(t, And(*term_ord.sorted_terms(strip_conj(t))))
        return imp_conj_iff(goal)

@register_macro('resolution')
class resolution_macro(Macro):
    def __init__(self):
        self.level = 1
        self.sig = None
        self.limit = 'resolution_right'

    def get_proof_term(self, arg, pts):
        """Input proof terms are A_1 | ... | A_m and B_1 | ... | B_n, where
        there is some i, j such that B_j = ~A_i or A_i = ~B_j."""
        
        # First, find the pair i, j such that B_j = ~A_i or A_i = ~B_j, the
        # variable side records the side of the positive literal.
        pt1, pt2 = pts
        disj1 = strip_disj(pt1.prop)
        disj2 = strip_disj(pt2.prop)
        
        side = None
        for i, t1 in enumerate(disj1):
            for j, t2 in enumerate(disj2):
                if t2 == Not(t1):
                    side = 'left'
                    break
                elif t1 == Not(t2):
                    side = 'right'
                    break
            if side is not None:
                break
                
        assert side is not None, "resolution: literal not found"
        
        # If side is wrong, just swap:
        if side == 'right':
            return self.get_proof_term(arg, [pt2, pt1])
        
        # Move items i and j to the front
        disj1 = [disj1[i]] + disj1[:i] + disj1[i+1:]
        disj2 = [disj2[j]] + disj2[:j] + disj2[j+1:]
        eq_pt1 = imp_disj_iff(Eq(pt1.prop, Or(*disj1)))
        eq_pt2 = imp_disj_iff(Eq(pt2.prop, Or(*disj2)))
        pt1 = eq_pt1.equal_elim(pt1)
        pt2 = eq_pt2.equal_elim(pt2)
        
        if len(disj1) > 1 and len(disj2) > 1:
            pt = apply_theorem('resolution', pt1, pt2)
        elif len(disj1) > 1 and len(disj2) == 1:
            pt = apply_theorem('resolution_left', pt1, pt2)
        elif len(disj1) == 1 and len(disj2) > 1:
            pt = apply_theorem('resolution_right', pt1, pt2)
        else:
            pt = apply_theorem('negE', pt2, pt1)

        return pt.on_prop(disj_norm())

def resolution(pt1, pt2):
    return ProofTerm('resolution', None, [pt1, pt2])


theory.global_macros.update({
    "beta_norm": beta_norm_macro(),
    "intros": intros_macro(),
    "apply_theorem": apply_theorem_macro(),
    "apply_theorem_for": apply_theorem_macro(with_inst=True),
    "resolve_theorem": resolve_theorem_macro(),
    "apply_fact": apply_fact_macro(),
    "apply_fact_for": apply_fact_macro(with_inst=True),
    "rewrite_goal": rewrite_goal_macro(),
    "rewrite_goal_sym": rewrite_goal_macro(sym=True),
    "rewrite_goal_with_prev": rewrite_goal_with_prev_macro(),
    "rewrite_goal_with_prev_sym": rewrite_goal_with_prev_macro(sym=True),
    "rewrite_fact": rewrite_fact_macro(),
    "rewrite_fact_sym": rewrite_fact_macro(sym=True),
    "rewrite_fact_with_prev": rewrite_fact_with_prev_macro(),
    "forall_elim_gen": forall_elim_gen_macro(),
    "trivial": trivial_macro(),
})
