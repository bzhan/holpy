# Author: Bohua Zhan

from kernel.term import Term, Var
from kernel import macro
from logic import logic
from logic import matcher
from logic.logic import apply_theorem
from logic.proofterm import ProofTerm, ProofTermMacro
from syntax import printer
from util import name


"""Setup for generic automation.

Generic automation is organized as a mapping from head terms
to proof procedures. Each proof procedure takes as arguments the
current theory, a term (the goal), and a list of conditions
(as proof terms), and either returns a proof term or fails.

"""

# Mapping from head terms to the corresponding automatic procedure.
global_autos = dict()

# Mapping from negation of head terms to the corresponding automatic
# procedure.
global_autos_neg = dict()

def add_global_autos(head, f):
    if head not in global_autos:
        global_autos[head] = [f]
    else:
        global_autos[head].append(f)

def add_global_autos_neg(head, f):
    if head not in global_autos_neg:
        global_autos_neg[head] = [f]
    else:
        global_autos_neg[head].append(f)

def solve(thy, goal, pts=None):
    """The main automation function.
    
    If the function succeeds, it should return a proof term whose
    proposition is the goal.

    """
    if pts is None:
        pts = []

    # First handle the case where goal matches one of the conditions.
    for pt in pts:
        if goal == pt.prop:
            return pt

    # Next, consider the situation where one of the assumptions is
    # a conjunction or a disjunction.
    for i, pt in enumerate(pts):
        if logic.is_conj(pt.prop):
            pt1 = apply_theorem(thy, 'conjD1', pt)
            pt2 = apply_theorem(thy, 'conjD2', pt)
            return solve(thy, goal, [pt1, pt2] + pts[:i] + pts[i+1:])
    
        if logic.is_disj(pt.prop):
            a1, a2 = pt.prop.args
            assume_pt1 = ProofTerm.assume(a1)
            assume_pt2 = ProofTerm.assume(a2)
            pt1 = solve(thy, goal, [assume_pt1] + pts[:i] + pts[i+1:])
            pt1 = ProofTerm.implies_intr(a1, pt1)
            pt2 = solve(thy, goal, [assume_pt2] + pts[:i] + pts[i+1:])
            pt2 = ProofTerm.implies_intr(a2, pt2)
            return apply_theorem(thy, 'disjE', pt, pt1, pt2)

    # Handle various logical connectives.
    if logic.is_conj(goal):
        a1, a2 = goal.args
        pt1 = solve(thy, a1, pts)
        pt2 = solve(thy, a2, pts)
        return apply_theorem(thy, 'conjI', pt1, pt2)
    
    if logic.is_disj(goal):
        a1, a2 = goal.args
        try:
            pt1 = solve(thy, a1, pts)
            return apply_theorem(thy, 'disjI1', pt1, concl=goal)
        except Exception:
            pt2 = solve(thy, a2, pts)
            return apply_theorem(thy, 'disjI2', pt2, concl=goal)
    
    if goal.is_implies():
        a1, a2 = goal.args
        assume_pt = ProofTerm.assume(a1)
        pt = solve(thy, a2, [assume_pt] + pts)
        pt = ProofTerm.implies_intr(a1, pt)
        return pt
    
    if goal.is_all():
        var_names = [v.name for v in term.get_vars([goal] + [pt.prop for pt in props])]
        nm = name.get_variant_name(goal.arg.var_name, var_names)
        v = Var(nm, goal.arg.var_T)
        t = goal.arg.subst_bound(v)
        pt = solve(thy, t, pts)
        pt = ProofTerm.forall_intr(v, pt)
        return pt

    # Call registered functions
    if logic.is_neg(goal) and goal.arg.head in global_autos_neg:
        for f in global_autos_neg[goal.arg.head]:
            try:
                pt = f(thy, goal, pts)
                return pt
            except Exception:
                pass

    if goal.head in global_autos:
        for f in global_autos[goal.head]:
            try:
                pt = f(thy, goal, pts)
                return pt
            except Exception as e:
                pass

    raise NotImplementedError


def solve_rules(th_names):
    """Return a solve function that tries to apply each of the theorems
    in th_names.

    """ 
    def solve_fun(thy, goal, pts):
        for th_name in th_names:
            try:
                th = thy.get_theorem(th_name, svar=True)
                instsp = matcher.first_order_match(th.concl, goal)
                As, _ = logic.subst_norm(th.prop, instsp).strip_implies()
                pts = [solve(thy, A, pts) for A in As]
                return apply_theorem(thy, th_name, *pts)
            except Exception:
                pass

        # Not solved
        raise NotImplementedError

class auto_macro(ProofTermMacro):
    """Macro applying auto.solve."""
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def get_proof_term(self, thy, args, pts):
        return solve(thy, args, pts)


macro.global_macros.update({
    "auto": auto_macro()
})
