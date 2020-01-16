# Author: Bohua Zhan

from kernel.type import Type
from kernel import term
from kernel.term import Term, Var, Bound
from kernel.thm import Thm, InvalidDerivationException
from logic.proofterm import ProofTerm, refl
from logic import matcher
from syntax import printer
from util import name
from util import typecheck


class ConvException(Exception):
    def __init__(self, str=""):
        self.str = str

class Conv():
    """A conversion is a function for rewriting a term.

    A Conv object has two main methods:
    eval - function to obtain the equality from the term.
    get_proof_term - function to obtain the proof term for the equality.

    """
    def eval(self, thy, t):
        return self.get_proof_term(thy, t).th

    def get_proof_term(self, thy, t):
        raise NotImplementedError

    def apply_to_pt(self, thy, pt, pos=None):
        """Apply to the given proof term."""

        # Rewriting the right side of an equality is handled
        # in a special way.
        if pos == "rhs":
            eq_pt = self.get_proof_term(thy, pt.prop.rhs)
            return ProofTerm.transitive(pt, eq_pt)

        elif pos == "lhs":
            eq_pt = self.get_proof_term(thy, pt.prop.lhs)
            return ProofTerm.transitive(ProofTerm.symmetric(eq_pt), pt)
        elif pos == "arg":
            return arg_conv(self).apply_to_pt(thy, pt)
        elif pos == "assums":
            return assums_conv(self).apply_to_pt(thy, pt)

        eq_pt = self.get_proof_term(thy, pt.prop)
        if eq_pt.prop.is_reflexive():
            return pt
        else:
            return ProofTerm.equal_elim(eq_pt, pt)

class all_conv(Conv):
    """Returns the trivial equality t = t."""
    def get_proof_term(self, thy, t):
        return refl(t)

class no_conv(Conv):
    """Always fails."""
    def get_proof_term(self, thy, t):
        raise ConvException("no_conv")

class combination_conv(Conv):
    """Apply cv1 to the function and cv2 to the argument."""
    def __init__(self, cv1, cv2):
        typecheck.checkinstance('combination_conv', cv1, Conv, cv2, Conv)
        self.cv1 = cv1
        self.cv2 = cv2

    def get_proof_term(self, thy, t):
        if not t.is_comb():
            raise ConvException("combination_conv: not a combination")
        pt1 = self.cv1.get_proof_term(thy, t.fun)
        pt2 = self.cv2.get_proof_term(thy, t.arg)

        # Obtain some savings if one of pt1 and pt2 is reflexivity:
        if pt1.th.is_reflexive() and pt2.th.is_reflexive():
            return ProofTerm.reflexive(t)
        else:
            return ProofTerm.combination(pt1, pt2)

class then_conv(Conv):
    """Applies cv1, followed by cv2."""
    def __init__(self, cv1, cv2):
        typecheck.checkinstance('then_conv', cv1, Conv, cv2, Conv)
        self.cv1 = cv1
        self.cv2 = cv2

    def __str__(self):
        return "then_conv(%s,%s)" % (str(self.cv1), str(self.cv2))

    def get_proof_term(self, thy, t):
        pt1 = self.cv1.get_proof_term(thy, t)
        t2 = pt1.prop.rhs
        pt2 = self.cv2.get_proof_term(thy, t2)
        
        # Obtain some savings if one of pt1 and pt2 is reflexivity:
        return ProofTerm.transitive(pt1, pt2)

class else_conv(Conv):
    """Applies cv1, if fails, apply cv2."""
    def __init__(self, cv1, cv2):
        typecheck.checkinstance('else_conv', cv1, Conv, cv2, Conv)
        self.cv1 = cv1
        self.cv2 = cv2

    def get_proof_term(self, thy, t):
        try:
            return self.cv1.get_proof_term(thy, t)
        except ConvException:
            return self.cv2.get_proof_term(thy, t)

class beta_conv(Conv):
    """Applies beta-conversion."""
    def __str__(self):
        return "beta_conv"

    def get_proof_term(self, thy, t):
        try:
            return ProofTerm.beta_conv(t)
        except InvalidDerivationException:
            raise ConvException("beta_conv")

class beta_norm_conv(Conv):
    def get_proof_term(self, thy, t):
        pt1 = top_conv(beta_conv()).get_proof_term(thy, t)
        if pt1.prop.rhs != t:
            pt2 = self.get_proof_term(thy, pt1.prop.rhs)
            return ProofTerm.transitive(pt1, pt2)
        else:
            return refl(t)

def beta_norm(thy, t):
    return beta_norm_conv().eval(thy, t).prop.arg

class eta_conv(Conv):
    """Eta-conversion."""
    def get_proof_term(self, thy, t):
        if not t.is_abs():
            raise ConvException("eta_conv")

        var_names = [v.name for v in term.get_vars(t.body)]
        nm = name.get_variant_name(t.var_name, var_names)
        v = Var(nm, t.var_T)
        t2 = t.subst_bound(v)

        if not (t2.is_comb() and t2.arg == v and not t2.fun.occurs_var(v)):
            raise ConvException("eta_conv")

        eq_pt = ProofTerm.theorem(thy, 'eta_conversion')
        eq_pt = ProofTerm.subst_type({
            'a': t2.fun.get_type().domain_type(),
            'b': t2.fun.get_type().range_type()}, eq_pt)
        eq_pt = ProofTerm.substitution({'f': t2.fun}, eq_pt)
        return eq_pt

class abs_conv(Conv):
    """Applies conversion to the body of abstraction."""
    def __init__(self, cv):
        typecheck.checkinstance('abs_conv', cv, Conv)
        self.cv = cv

    def get_proof_term(self, thy, t):
        if not t.is_abs():
            raise ConvException("abs_conv: not an abstraction")

        # Find a new variable x and substitute for body
        var_names = [v.name for v in term.get_vars(t.body)]
        nm = name.get_variant_name(t.var_name, var_names)
        v = Var(nm, t.var_T)
        t2 = t.subst_bound(v)

        # It is possible that cv produces additional assumptions
        # containing v. In this case the conversion should fail.
        try:
            return ProofTerm.abstraction(self.cv.get_proof_term(thy, t2), v)
        except InvalidDerivationException:
            raise ConvException("abs_conv")

def try_conv(cv):
    return else_conv(cv, all_conv())

def comb_conv(cv):
    return combination_conv(cv, cv)

def arg_conv(cv):
    return combination_conv(all_conv(), cv)

def fun_conv(cv):
    return combination_conv(cv, all_conv())

def arg1_conv(cv):
    return fun_conv(arg_conv(cv))

def binop_conv(cv):
    return combination_conv(arg_conv(cv), cv)

def every_conv(*args):
    if len(args) == 0:
        return all_conv()
    elif len(args) == 1:
        return args[0]
    else:
        return then_conv(args[0], every_conv(*args[1:]))

class argn_conv(Conv):
    """Apply cv to the nth argument of t, counting from the left and
    starting at 0.

    """
    def __init__(self, n, cv):
        self.n = n
        self.cv = cv

    def get_proof_term(self, thy, t):
        cv = arg_conv(self.cv)
        for i in range(len(t.args) - self.n - 1):
            cv = fun_conv(cv)
        return cv.get_proof_term(thy, t)

class assums_conv(Conv):
    """Given a term of the form A1 --> ... --> An --> C, apply cv
    to each A1, ..., An.

    """
    def __init__(self, cv):
        self.cv = cv

    def get_proof_term(self, thy, t):
        if t.is_implies():
            return then_conv(arg1_conv(self.cv), arg_conv(self)).get_proof_term(thy, t)
        else:
            return refl(t)

class sub_conv(Conv):
    def __init__(self, cv):
        self.cv = cv

    def get_proof_term(self, thy, t):
        if t.is_comb():
            return comb_conv(self.cv).get_proof_term(thy, t)
        elif t.is_abs():
            return abs_conv(self.cv).get_proof_term(thy, t)
        else:
            return refl(t)

class bottom_conv(Conv):
    """Applies cv repeatedly in the bottom-up manner."""
    def __init__(self, cv):
        typecheck.checkinstance('bottom_conv', cv, Conv)
        self.cv = cv

    def get_proof_term(self, thy, t):
        return then_conv(sub_conv(self), try_conv(self.cv)).get_proof_term(thy, t)

class top_conv(Conv):
    """Applies cv repeatedly in the top-down manner."""
    def __init__(self, cv):
        typecheck.checkinstance('top_conv', cv, Conv)
        self.cv = cv

    def __str__(self):
        return "top_conv(%s)" % str(self.cv)

    def get_proof_term(self, thy, t):
        return then_conv(try_conv(self.cv), sub_conv(self)).get_proof_term(thy, t)

class top_sweep_conv(Conv):
    """Applies cv in the top-down manner, but only at the first level."""
    def __init__(self, cv):
        typecheck.checkinstance('top_sweep_conv', cv, Conv)
        self.cv = cv

    def __str__(self):
        return "top_sweep_conv(%s)" % str(self.cv)

    def get_proof_term(self, thy, t):
        return else_conv(self.cv, else_conv(sub_conv(self), all_conv())).get_proof_term(thy, t)

class rewr_conv(Conv):
    """Rewrite using the given equality theorem."""
    def __init__(self, pt, *, sym=False, conds=None):
        if conds is None:
            conds = []
        typecheck.checkinstance('rewr_conv', pt, (ProofTerm, str), conds, [ProofTerm])
        self.pt = pt
        self.sym = sym
        self.conds = conds

        # Computed after the first invocation
        self.eq_pt = None
        self.As = None
        self.C = None

    def __str__(self):
        if isinstance(self.pt, str):
            return "rewr_conv(%s)" % str(self.pt)
        else:
            return "rewr_conv(%s)" % str(self.pt.th)

    def get_proof_term(self, thy, t):
        # If self.eq_pt is not present, produce it from thy, self.pt
        # and self.sym. Decompose into self.As and self.C.
        if self.eq_pt is None:
            if isinstance(self.pt, str):
                self.eq_pt = ProofTerm.theorem(thy, self.pt)
            else:
                self.eq_pt = self.pt
            if self.sym:
                self.eq_pt = ProofTerm.symmetric(self.eq_pt)

            self.As, self.C = self.eq_pt.prop.strip_implies()

        # The conclusion of eq_pt should be an equality, and the number of
        # assumptions in eq_pt should match number of conditions.
        assert Term.is_equals(self.C), "rewr_conv: theorem is not an equality."
        if len(self.As) != len(self.conds):
            raise ConvException("rewr_conv: number of conds does not agree")

        instsp = dict(), dict()
        ts = [cond.prop for cond in self.conds]
        try:
            matcher.first_order_match_list_incr(self.As, ts, instsp)
            matcher.first_order_match_incr(self.C.lhs, t, instsp)
        except matcher.MatchException:
            raise ConvException("rewr_conv: cannot match %s with %s" % (
                printer.print_term(thy, self.C.lhs), printer.print_term(thy, t)))

        # Check that every variable in the theorem has an instantiation
        if set(term.get_svars(self.As + [self.C.lhs])) != set(term.get_svars(self.As + [self.C])):
            raise ConvException("rewr_conv: unmatched vars")

        pt = self.eq_pt
        tyinst, inst = instsp
        if tyinst:
            pt = ProofTerm.subst_type(tyinst, pt)
        if inst:
            pt = ProofTerm.substitution(inst, pt)
        if self.conds:
            pt = ProofTerm.implies_elim(pt, *self.conds)

        assert pt.th.is_equals(), "rewr_conv: wrong result."

        if pt.th.prop.lhs != t:
            pt = beta_norm_conv().apply_to_pt(thy, pt)

        if pt.th.prop.lhs != t:
            pt = eta_conv().apply_to_pt(thy, pt)

        assert pt.th.prop.lhs == t, "rewr_conv: wrong result. Expected %s, got %s" % (str(t), str(pt.th.prop.lhs))
        return pt

def has_rewrite(thy, th, t, *, sym=False, conds=None):
    """Returns whether a rewrite is possible on a subterm of t.
    
    This can serve as a pre-check for top_sweep_conv, top_conv, and
    bottom_conv applied to rewr_conv.

    th -- either the name of a theorem, or the theorem itself.
    t -- target of rewriting.
    conds -- optional list of theorems matching assumptions of th.

    """
    if isinstance(th, str):
        th = thy.get_theorem(th, svar=True)

    if sym:
        th = Thm.symmetric(th)

    As, C = th.prop.strip_implies() 

    if conds is None:
        conds = []
    if not Term.is_equals(C) or len(As) != len(conds):
        return False
        
    if set(term.get_svars(As + [C.lhs])) != set(term.get_svars(As + [C])):
        return False

    ts = [cond.prop for cond in conds]
    instsp = dict(), dict()
    try:
        matcher.first_order_match_list_incr(As, ts, instsp)
    except matcher.MatchException:
        return False

    def rec(t):
        if not t.is_open() and matcher.can_first_order_match_incr(C.lhs, t, instsp):
            return True

        if t.is_comb():
            return rec(t.fun) or rec(t.arg)
        elif t.is_abs():
            var_names = [v.name for v in term.get_vars(t.body)]
            nm = name.get_variant_name(t.var_name, var_names)
            v = Var(nm, t.var_T)
            t2 = t.subst_bound(v)
            return rec(t2)
        else:
            return False

    return rec(t)
