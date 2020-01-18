# Author: Bohua Zhan

from kernel import term
from kernel.term import Term, Var
from kernel import macro
from logic import logic
from logic.logic import apply_theorem, TacticException
from logic import matcher
from logic.conv import Conv, ConvException, refl
from logic.proofterm import ProofTerm, ProofTermMacro, ProofTermDeriv
from syntax import printer
from util import name


"""Setup for generic automation.

Generic automation is organized as a mapping from head terms
to proof procedures. Each proof procedure takes as arguments the
current theory, a term (the goal), and a list of conditions
(as proof terms), and either returns a proof term or fails.

"""
# Turn on / off debugging information
debug_auto = False

# Mapping from head terms to the corresponding automatic procedure.
global_autos = dict()

# Mapping from negation of head terms to the corresponding automatic
# procedure.
global_autos_neg = dict()

# Mapping from head term to the normalization / simplification
# procedure
global_autos_norm = dict()


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

def add_global_autos_norm(head, f):
    if head not in global_autos_norm:
        global_autos_norm[head] = [f]
    else:
        global_autos_norm[head].append(f)


def solve(thy, goal, pts=None):
    """The main automation function.
    
    If the function succeeds, it should return a proof term whose
    proposition is the goal.

    """
    if debug_auto:
        print("Solve:", printer.print_term(thy, goal))

    if pts is None:
        pts = []
    elif isinstance(pts, tuple):
        pts = list(pts)

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
        except TacticException:
            pt2 = solve(thy, a2, pts)
            return apply_theorem(thy, 'disjI2', pt2, concl=goal)
    
    if goal.is_implies():
        a1, a2 = goal.args
        assume_pt = ProofTerm.assume(a1)
        pt = solve(thy, a2, [assume_pt] + pts)
        pt = ProofTerm.implies_intr(a1, pt)
        return pt
    
    if goal.is_all():
        var_names = [v.name for v in term.get_vars([goal] + [pt.prop for pt in pts])]
        nm = name.get_variant_name(goal.arg.var_name, var_names)
        v = Var(nm, goal.arg.var_T)
        t = goal.arg.subst_bound(v)
        pt = solve(thy, t, pts)
        pt = ProofTerm.forall_intr(v, pt)
        return pt

    # Normalize goal
    eq_pt = norm(thy, goal, pts)
    goal = eq_pt.rhs

    # Call registered functions
    if logic.is_neg(goal) and goal.arg.head in global_autos_neg:
        for f in global_autos_neg[goal.arg.head]:
            try:
                pt = f(thy, goal, pts)
                return ProofTerm.equal_elim(ProofTerm.symmetric(eq_pt), pt)
            except TacticException:
                pass

    if goal.head in global_autos:
        for f in global_autos[goal.head]:
            try:
                pt = f(thy, goal, pts)
                return ProofTerm.equal_elim(ProofTerm.symmetric(eq_pt), pt)
            except TacticException:
                pass

    raise TacticException


def solve_rules(th_names):
    """Return a solve function that tries to apply each of the theorems
    in th_names.

    """ 
    def solve_fun(thy, goal, pts):
        for th_name in th_names:
            if thy.has_theorem(th_name):
                th = thy.get_theorem(th_name, svar=True)
            try:
                instsp = matcher.first_order_match(th.concl, goal)
            except matcher.MatchException:
                continue

            As, _ = logic.subst_norm(th.prop, instsp).strip_implies()
            try:
                pts = [solve(thy, A, pts) for A in As]
            except TacticException:
                continue

            return apply_theorem(thy, th_name, *pts, concl=goal)

        # Not solved
        raise TacticException

    return solve_fun


def norm(thy, t, pts=None):
    """The main normalization function.
    
    The function should always succeed. It returns an equality whose left
    side is t. If no normalization is available, it returns t = t.

    """
    if debug_auto:
        print("Norm:", printer.print_term(thy, t))

    if not t.is_comb():
        return refl(t)

    eq_pt = refl(t.head)

    # First normalize each argument
    for arg in t.args:
        eq_pt = ProofTerm.combination(eq_pt, norm(thy, arg, pts))

    # Next, apply each normalization rule
    if t.head in global_autos_norm:
        ori_rhs = eq_pt.rhs
        for f in global_autos_norm[t.head]:
            try:
                if isinstance(f, Conv):
                    eq_pt = eq_pt.on_rhs(thy, f)
                else:
                    eq_pt = ProofTerm.transitive(eq_pt, f(thy, eq_pt.rhs, pts))
            except ConvException:
                continue

        if eq_pt.rhs == ori_rhs:
            # Unchanged, normalization stops here
            return eq_pt
        else:
            # Head changed, continue apply norm
            return ProofTerm.transitive(eq_pt, norm(thy, eq_pt.rhs, pts))
    else:
        # No normalization rule available for this head
        return eq_pt
    
def norm_rules(th_names):
    """Return a normalization function that tries to apply each of the
    rewriting rules.

    """
    def norm_fun(thy, t, pts):
        for th_name in th_names:
            if thy.has_theorem(th_name):
                th = thy.get_theorem(th_name, svar=True)
            else:
                continue

            try:
                instsp = matcher.first_order_match(th.concl.lhs, t)
            except matcher.MatchException:
                continue

            As, C = logic.subst_norm(th.prop, instsp).strip_implies()
            try:
                pts = [solve(thy, A, pts) for A in As]
            except TacticException:
                continue

            return apply_theorem(thy, th_name, *pts, concl=C)

        # No rewriting available
        return refl(t)

    return norm_fun

class auto_macro(ProofTermMacro):
    """Macro applying auto.solve."""
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def get_proof_term(self, thy, args, pts):
        if args.is_equals():
            # Equality: use normalization
            eq1 = norm(thy, args.lhs, pts)
            eq2 = norm(thy, args.rhs, pts)
            if eq1.rhs != eq2.rhs:
                raise TacticException
            return ProofTerm.transitive(eq1, ProofTerm.symmetric(eq2))
        else:
            # Otherwise, use solve function
            return solve(thy, args, pts)


def auto_solve(thy, t, pts=None):
    return ProofTermDeriv('auto', thy, args=t, prevs=pts)

class auto_conv(Conv):
    """Applies auto macro in conversion."""
    def __init__(self, conds=None):
        if conds is None:
            conds = []
        self.conds = conds

    def get_proof_term(self, thy, t):
        eq_t = norm(thy, t, self.conds)
        if t == eq_t.rhs:
            return refl(t)
        else:
            return ProofTermDeriv('auto', thy, args=eq_t.prop, prevs=self.conds, th=eq_t.th)


macro.global_macros.update({
    "auto": auto_macro()
})
