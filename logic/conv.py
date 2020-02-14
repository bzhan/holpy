# Author: Bohua Zhan

from kernel.type import TyInst
from kernel import term
from kernel.term import Term, Var, Bound, Inst
from kernel.thm import Thm, InvalidDerivationException
from kernel import theory
from kernel.proofterm import ProofTerm, refl
from logic import matcher
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
    def eval(self, t):
        return self.get_proof_term(t).th

    def get_proof_term(self, t):
        raise NotImplementedError


class all_conv(Conv):
    """Returns the trivial equality t = t."""
    def get_proof_term(self, t):
        return refl(t)

class no_conv(Conv):
    """Always fails."""
    def get_proof_term(self, t):
        raise ConvException("no_conv")

class combination_conv(Conv):
    """Apply cv1 to the function and cv2 to the argument."""
    def __init__(self, cv1, cv2):
        typecheck.checkinstance('combination_conv', cv1, Conv, cv2, Conv)
        self.cv1 = cv1
        self.cv2 = cv2

    def get_proof_term(self, t):
        if not t.is_comb():
            raise ConvException("combination_conv: not a combination")
        pt1 = self.cv1.get_proof_term(t.fun)
        pt2 = self.cv2.get_proof_term(t.arg)

        # Obtain some savings if one of pt1 and pt2 is reflexivity:
        if pt1.th.is_reflexive() and pt2.th.is_reflexive():
            return ProofTerm.reflexive(t)
        else:
            return pt1.combination(pt2)

class then_conv(Conv):
    """Applies cv1, followed by cv2."""
    def __init__(self, cv1, cv2):
        typecheck.checkinstance('then_conv', cv1, Conv, cv2, Conv)
        self.cv1 = cv1
        self.cv2 = cv2

    def __str__(self):
        return "then_conv(%s,%s)" % (str(self.cv1), str(self.cv2))

    def get_proof_term(self, t):
        pt1 = self.cv1.get_proof_term(t)
        t2 = pt1.prop.rhs
        pt2 = self.cv2.get_proof_term(t2)
        
        # Obtain some savings if one of pt1 and pt2 is reflexivity:
        return pt1.transitive(pt2)

class else_conv(Conv):
    """Applies cv1, if fails, apply cv2."""
    def __init__(self, cv1, cv2):
        typecheck.checkinstance('else_conv', cv1, Conv, cv2, Conv)
        self.cv1 = cv1
        self.cv2 = cv2

    def get_proof_term(self, t):
        try:
            return self.cv1.get_proof_term(t)
        except ConvException:
            return self.cv2.get_proof_term(t)

class beta_conv(Conv):
    """Applies beta-conversion."""
    def __str__(self):
        return "beta_conv"

    def get_proof_term(self, t):
        try:
            return ProofTerm.beta_conv(t)
        except InvalidDerivationException:
            raise ConvException("beta_conv")

class beta_norm_conv(Conv):
    def get_proof_term(self, t):
        def rec(t):
            if t.is_abs():
                v, body = t.dest_abs()
                body_pt = rec(body)
                if body_pt.is_reflexive():
                    return refl(t)
                else:
                    return body_pt.abstraction(v)
            elif t.is_comb():
                fun_pt = rec(t.fun)
                arg_pt = rec(t.arg)
                pt = fun_pt.combination(arg_pt)
                if fun_pt.rhs.is_abs():
                    pt2 = ProofTerm.beta_conv(pt.rhs)
                    pt3 = rec(pt2.rhs)
                    return pt.transitive(pt2, pt3)
                else:
                    return pt
            else:
                return refl(t)

        return rec(t)

def beta_norm(t):
    return beta_norm_conv().eval(t).prop.arg

class eta_conv(Conv):
    """Eta-conversion."""
    def get_proof_term(self, t):
        if not t.is_abs():
            raise ConvException("eta_conv")

        v, body = t.dest_abs()

        if not (body.is_comb() and body.arg == v and not body.fun.occurs_var(v)):
            raise ConvException("eta_conv")

        return ProofTerm.theorem('eta_conversion').substitution(f=body.fun)

class abs_conv(Conv):
    """Applies conversion to the body of abstraction."""
    def __init__(self, cv):
        typecheck.checkinstance('abs_conv', cv, Conv)
        self.cv = cv

    def get_proof_term(self, t):
        if not t.is_abs():
            raise ConvException("abs_conv: not an abstraction")

        v, body = t.dest_abs()

        # It is possible that cv produces additional assumptions
        # containing v. In this case the conversion should fail.
        try:
            return self.cv.get_proof_term(body).abstraction(v)
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

    def get_proof_term(self, t):
        cv = arg_conv(self.cv)
        for i in range(len(t.args) - self.n - 1):
            cv = fun_conv(cv)
        return cv.get_proof_term(t)

class assums_conv(Conv):
    """Given a term of the form A1 --> ... --> An --> C, apply cv
    to each A1, ..., An.

    """
    def __init__(self, cv):
        self.cv = cv

    def get_proof_term(self, t):
        if t.is_implies():
            return then_conv(arg1_conv(self.cv), arg_conv(self)).get_proof_term(t)
        else:
            return refl(t)

class sub_conv(Conv):
    def __init__(self, cv):
        self.cv = cv

    def get_proof_term(self, t):
        if t.is_comb():
            return comb_conv(self.cv).get_proof_term(t)
        elif t.is_abs():
            return abs_conv(self.cv).get_proof_term(t)
        else:
            return refl(t)

class bottom_conv(Conv):
    """Applies cv repeatedly in the bottom-up manner."""
    def __init__(self, cv):
        typecheck.checkinstance('bottom_conv', cv, Conv)
        self.cv = cv

    def get_proof_term(self, t):
        pt = refl(t)
        if t.is_comb():
            return pt.on_rhs(fun_conv(self), arg_conv(self), try_conv(self.cv))
        elif t.is_abs():
            return pt.on_rhs(abs_conv(self), try_conv(self.cv))
        else:
            return pt.on_rhs(try_conv(self.cv))

class top_conv(Conv):
    """Applies cv repeatedly in the top-down manner."""
    def __init__(self, cv):
        typecheck.checkinstance('top_conv', cv, Conv)
        self.cv = cv

    def __str__(self):
        return "top_conv(%s)" % str(self.cv)

    def get_proof_term(self, t):
        def rec(t):
            pt = refl(t).on_rhs(try_conv(self.cv))
            if pt.rhs.is_comb():
                fun_pt = rec(pt.rhs.fun)
                arg_pt = rec(pt.rhs.arg)
                return pt.transitive(fun_pt.combination(arg_pt))
            elif pt.rhs.is_abs():
                v, body = t.dest_abs()
                body_pt = rec(body)
                if body_pt.is_reflexive():
                    return pt
                else:
                    return pt.transitive(body_pt.abstraction(v))
            else:
                return pt

        return rec(t)

class top_sweep_conv(Conv):
    """Applies cv in the top-down manner, but only at the first level."""
    def __init__(self, cv):
        typecheck.checkinstance('top_sweep_conv', cv, Conv)
        self.cv = cv

    def __str__(self):
        return "top_sweep_conv(%s)" % str(self.cv)

    def get_proof_term(self, t):
        def rec(t):
            pt = refl(t).on_rhs(try_conv(self.cv))
            if not pt.is_reflexive():
                return pt

            if t.is_comb():
                fun_pt = rec(t.fun)
                arg_pt = rec(t.arg)
                return fun_pt.combination(arg_pt)
            elif t.is_abs():
                v, body = t.dest_abs()
                body_pt = rec(body)
                if body_pt.is_reflexive():
                    return pt
                else:
                    return body_pt.abstraction(v)
            else:
                return pt

        return rec(t)

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

    def get_proof_term(self, t):
        # If self.eq_pt is not present, produce it from thy, self.pt
        # and self.sym. Decompose into self.As and self.C.
        if self.eq_pt is None:
            if isinstance(self.pt, str):
                self.eq_pt = ProofTerm.theorem(self.pt)
            else:
                self.eq_pt = self.pt

            self.As, self.C = self.eq_pt.prop.strip_implies()

        # The conclusion of eq_pt should be an equality, and the number of
        # assumptions in eq_pt should match number of conditions.
        assert self.C.is_equals(), "rewr_conv: theorem is not an equality."
        if len(self.As) != len(self.conds):
            raise ConvException("rewr_conv: number of conds does not agree")

        inst = Inst()
        ts = [cond.prop for cond in self.conds]
        if not self.sym:
            lhs = self.C.lhs
        else:
            lhs = self.C.rhs
        try:
            inst = matcher.first_order_match_list(self.As, ts, inst)
            inst = matcher.first_order_match(lhs, t, inst)
        except matcher.MatchException:
            raise ConvException("rewr_conv: cannot match left side")

        # Check that every variable in the theorem has an instantiation
        if set(term.get_svars(self.As + [lhs])) != set(term.get_svars(self.As + [self.C])):
            raise ConvException("rewr_conv: unmatched vars")

        pt = self.eq_pt
        pt = pt.substitution(inst)
        pt = pt.implies_elim(*self.conds)
        if self.sym:
            pt = pt.symmetric()

        assert pt.th.is_equals(), "rewr_conv: wrong result."

        if pt.th.prop.lhs != t:
            pt = pt.on_prop(beta_norm_conv())

        if pt.th.prop.lhs != t:
            pt = pt.on_prop(eta_conv())

        assert pt.th.prop.lhs == t, "rewr_conv: wrong result. Expected %s, got %s" % (str(t), str(pt.th.prop.lhs))
        return pt

def has_rewrite(th, t, *, sym=False, conds=None):
    """Returns whether a rewrite is possible on a subterm of t.
    
    This can serve as a pre-check for top_sweep_conv, top_conv, and
    bottom_conv applied to rewr_conv.

    th -- either the name of a theorem, or the theorem itself.
    t -- target of rewriting.
    conds -- optional list of theorems matching assumptions of th.

    """
    if isinstance(th, str):
        th = theory.get_theorem(th)

    if sym:
        th = Thm.symmetric(th)

    As, C = th.prop.strip_implies() 

    if conds is None:
        conds = []
    if not C.is_equals() or len(As) != len(conds):
        return False
        
    if set(term.get_svars(As + [C.lhs])) != set(term.get_svars(As + [C])):
        return False

    ts = [cond.prop for cond in conds]
    inst = Inst()
    try:
        inst = matcher.first_order_match_list(As, ts, inst)
    except matcher.MatchException:
        return False

    def rec(t):
        if not t.is_open() and matcher.can_first_order_match(C.lhs, t, inst):
            return True

        if t.is_comb():
            return rec(t.fun) or rec(t.arg)
        elif t.is_abs():
            _, body = t.dest_abs()
            return rec(body)
        else:
            return False

    return rec(t)
