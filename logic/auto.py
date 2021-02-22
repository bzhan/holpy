# Author: Bohua Zhan

from kernel import term
from kernel.term import Term, Var
from kernel.macro import Macro
from kernel import theory
from kernel.theory import register_macro
from kernel.proofterm import ProofTerm, TacticException
from logic import logic
from logic.logic import apply_theorem
from logic import matcher
from logic.conv import Conv, ConvException, refl, eta_conv, top_conv
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


solve_record = dict()

def solve(goal, pts=None):
    """The main automation function.
    
    If the function succeeds, it should return a proof term whose
    proposition is the goal.

    """
    if debug_auto:
        print("Solve:", goal, [str(pt.prop) for pt in pts])

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
        if pt.prop.is_conj():
            pt1 = apply_theorem('conjD1', pt)
            pt2 = apply_theorem('conjD2', pt)
            return solve(goal, [pt1, pt2] + pts[:i] + pts[i+1:])
    
        if pt.prop.is_disj():
            a1, a2 = pt.prop.args
            assume_pt1 = ProofTerm.assume(a1)
            assume_pt2 = ProofTerm.assume(a2)
            pt1 = solve(goal, [assume_pt1] + pts[:i] + pts[i+1:])
            pt1 = pt1.implies_intr(a1)
            pt2 = solve(goal, [assume_pt2] + pts[:i] + pts[i+1:])
            pt2 = pt2.implies_intr(a2)
            return apply_theorem('disjE', pt, pt1, pt2)

    # Handle various logical connectives.
    if goal.is_conj():
        a1, a2 = goal.args
        pt1 = solve(a1, pts)
        pt2 = solve(a2, pts)
        return apply_theorem('conjI', pt1, pt2)
    
    if goal.is_disj():
        a1, a2 = goal.args
        try:
            pt1 = solve(a1, pts)
            return apply_theorem('disjI1', pt1, concl=goal)
        except TacticException:
            pt2 = solve(a2, pts)
            return apply_theorem('disjI2', pt2, concl=goal)
    
    if goal.is_implies():
        a1, a2 = goal.args
        assume_pt = ProofTerm.assume(a1)
        return solve(a2, [assume_pt] + pts).implies_intr(a1)
    
    if goal.is_forall():
        var_names = [v.name for v in term.get_vars([goal] + [pt.prop for pt in pts])]
        nm = name.get_variant_name(goal.arg.var_name, var_names)
        v = Var(nm, goal.arg.var_T)
        t = goal.arg.subst_bound(v)
        return solve(t, pts).forall_intr(v)

    # Normalize goal
    eq_pt = norm(goal, pts)
    goal = eq_pt.rhs

    if goal.is_conj():
        pt = solve(goal, pts)
        return eq_pt.symmetric().equal_elim(pt)

    res_pt = None

    if not pts and goal in solve_record:
        res_pt = solve_record[goal]

    # Call registered functions
    elif goal.is_not() and goal.arg.head in global_autos_neg:
        for f in global_autos_neg[goal.arg.head]:
            try:
                res_pt = f(goal, pts)
                break
            except TacticException:
                pass

    elif goal.head in global_autos:
        for f in global_autos[goal.head]:
            try:
                res_pt = f(goal, pts)
                break
            except TacticException:
                pass

    if res_pt is not None:
        if not pts:
            solve_record[goal] = res_pt
        return eq_pt.symmetric().equal_elim(res_pt)
    else:
        raise TacticException('Cannot solve %s' % goal)


def solve_rules(th_names):
    """Return a solve function that tries to apply each of the theorems
    in th_names.

    """ 
    def solve_fun(goal, pts):
        for th_name in th_names:
            if theory.thy.has_theorem(th_name):
                th = theory.get_theorem(th_name)
            try:
                inst = matcher.first_order_match(th.concl, goal)
            except matcher.MatchException:
                continue

            As, _ = th.prop.subst_norm(inst).strip_implies()
            try:
                pts = [solve(A, pts) for A in As]
            except TacticException:
                continue

            return apply_theorem(th_name, *pts, concl=goal)

        # Not solved
        raise TacticException

    return solve_fun


norm_record = dict()

def norm(t, pts=None):
    """The main normalization function.
    
    The function should always succeed. It returns an equality whose left
    side is t. If no normalization is available, it returns t = t.

    """
    if debug_auto:
        print("Norm:", t, [str(pt.prop) for pt in pts])

    # Do not normalize variables and abstractions
    if t.is_var() or t.is_abs():
        return refl(t)

    # No further work for numbers
    if t.is_number():
        return refl(t)

    # Record
    if not pts and t in norm_record:
        return norm_record[t]

    eq_pt = refl(t.head)

    # First normalize each argument
    for arg in t.args:
        eq_pt = eq_pt.combination(norm(arg, pts))

    # Next, apply each normalization rule
    if t.head in global_autos_norm:
        ori_rhs = eq_pt.rhs
        for f in global_autos_norm[t.head]:
            try:
                if isinstance(f, Conv):
                    eq_pt = eq_pt.on_rhs(f)
                else:
                    eq_pt = eq_pt.transitive(f(eq_pt.rhs, pts))
            except ConvException:
                continue

            if eq_pt.rhs.head != t.head:
                # Head changed, should try something else
                break

        if eq_pt.rhs == ori_rhs:
            # Unchanged, normalization stops here
            res_pt = eq_pt
        else:
            # Head changed, continue apply norm
            eq_pt2 = norm(eq_pt.rhs, pts)
            if eq_pt2.lhs != eq_pt.rhs:
                eq_pt2 = eq_pt2.on_lhs(top_conv(eta_conv()))
            res_pt = eq_pt.transitive(eq_pt2)
    else:
        # No normalization rule available for this head
        res_pt = eq_pt

    if not pts:
        norm_record[t] = res_pt
    return res_pt

def norm_rules(th_names):
    """Return a normalization function that tries to apply each of the
    rewriting rules.

    """
    def norm_fun(t, pts):
        for th_name in th_names:
            if theory.thy.has_theorem(th_name):
                th = theory.get_theorem(th_name)
            else:
                continue

            try:
                inst = matcher.first_order_match(th.concl.lhs, t)
            except matcher.MatchException:
                continue

            As, C = th.prop.subst_norm(inst).strip_implies()
            try:
                pts = [solve(A, pts) for A in As]
            except TacticException:
                continue

            return apply_theorem(th_name, *pts, concl=C)

        # No rewriting available
        return refl(t)

    return norm_fun


@register_macro('auto')
class auto_macro(Macro):
    """Macro applying auto.solve."""
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def get_proof_term(self, args, pts):
        if args.is_equals():
            # Equality: use normalization
            eq1 = norm(args.lhs, pts)
            eq2 = norm(args.rhs, pts)
            if eq1.rhs != eq2.rhs:
                print("lhs: %s" % eq1.rhs)
                print("rhs: %s" % eq2.rhs)
                raise TacticException
            return eq1.transitive(eq2.symmetric())
        else:
            # Otherwise, use solve function
            return solve(args, pts)


def auto_solve(t, pts=None):
    return ProofTerm('auto', args=t, prevs=pts)

class auto_conv(Conv):
    """Applies auto macro in conversion."""
    def __init__(self, conds=None):
        if conds is None:
            conds = []
        self.conds = conds

    def get_proof_term(self, t):
        eq_t = norm(t, self.conds)
        if t == eq_t.rhs:
            return refl(t)
        else:
            return ProofTerm('auto', args=eq_t.prop, prevs=self.conds, th=eq_t.th)


"""Managing cache records."""
def cache_stats():
    return "Norm: %d\nSolve: %d" % (len(norm_record), len(solve_record))

def clear_cache():
    global norm_record, solve_record
    norm_record = dict()
    solve_record = dict()
