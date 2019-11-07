# Author: Bohua Zhan

from kernel.type import Type
from kernel import term
from kernel.term import Term, Var
from kernel.thm import Thm, InvalidDerivationException
from logic.proofterm import ProofTerm, refl
from logic import matcher
from util import name


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
        assert isinstance(cv1, Conv) and isinstance(cv2, Conv), "combination_conv: argument"
        self.cv1 = cv1
        self.cv2 = cv2

    def get_proof_term(self, thy, t):
        if t.ty != term.COMB:
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
        assert isinstance(cv1, Conv) and isinstance(cv2, Conv), "then_conv: argument"
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
        assert isinstance(cv1, Conv) and isinstance(cv2, Conv), "else_conv: argument"
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

def beta_norm(thy, t):
    return top_conv(beta_conv()).eval(thy, t).prop.arg

class abs_conv(Conv):
    """Applies conversion to the body of abstraction."""
    def __init__(self, cv):
        assert isinstance(cv, Conv)
        self.cv = cv

    def get_proof_term(self, thy, t):
        if t.ty != term.ABS:
            raise ConvException("abs_conv: not an abstraction")

        # Find a new variable x and substitute for body
        var_names = [v.name for v in term.get_vars(t.body)]
        nm = name.get_variant_name(t.var_name, var_names)
        v = Var(nm, t.var_T)
        t2 = t.subst_bound(v)
        return ProofTerm.abstraction(self.cv.get_proof_term(thy, t2), v)

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
        assert isinstance(cv, Conv), "bottom_conv: argument"
        self.cv = cv

    def get_proof_term(self, thy, t):
        return then_conv(sub_conv(self), try_conv(self.cv)).get_proof_term(thy, t)

class top_conv(Conv):
    """Applies cv repeatedly in the top-down manner."""
    def __init__(self, cv):
        assert isinstance(cv, Conv), "top_conv: argument"
        self.cv = cv

    def __str__(self):
        return "top_conv(%s)" % str(self.cv)

    def get_proof_term(self, thy, t):
        return then_conv(try_conv(self.cv), sub_conv(self)).get_proof_term(thy, t)

class top_sweep_conv(Conv):
    """Applies cv in the top-down manner, but only at the first level."""
    def __init__(self, cv):
        assert isinstance(cv, Conv), "top_sweep_conv: argument"
        self.cv = cv

    def __str__(self):
        return "top_sweep_conv(%s)" % str(self.cv)

    def get_proof_term(self, thy, t):
        return else_conv(self.cv, else_conv(sub_conv(self), all_conv())).get_proof_term(thy, t)

class rewr_conv(Conv):
    """Rewrite using the given equality theorem.
    
    match_vars -- whether variables in pat should be matched.
    
    """
    def __init__(self, pt, match_vars=True, sym=False, conds=None):
        assert isinstance(pt, ProofTerm) or isinstance(pt, str), "rewr_conv: argument"
        self.pt = pt
        self.sym = sym
        self.match_vars = match_vars
        if conds is not None:
            assert isinstance(conds, list) and all(isinstance(cond, ProofTerm) for cond in conds), "rewr_conv"
        self.conds = conds

    def __str__(self):
        if isinstance(self.pt, str):
            return "rewr_conv(%s)" % str(self.pt)
        else:
            return "rewr_conv(%s)" % str(self.pt.th)

    def get_proof_term(self, thy, t):
        if isinstance(self.pt, str):
            eq_pt = ProofTerm.theorem(thy, self.pt)
            if self.sym:
                eq_pt = ProofTerm.symmetric(eq_pt)
        else:
            eq_pt = self.pt
                
        # Deconstruct th into assumptions and conclusion
        As, C = eq_pt.assums, eq_pt.concl
        assert Term.is_equals(C), "rewr_conv: theorem is not an equality."

        tyinst, inst = dict(), dict()

        if self.match_vars:
            try:
                matcher.first_order_match_incr(C.lhs, t, (tyinst, inst))
            except matcher.MatchException:
                raise ConvException("rewr_conv: cannot match %s with %s" % (str(C.lhs), str(t)))
        elif C.lhs != t:
            raise ConvException("rewr_conv: %s ~= %s" % (str(C.lhs), str(t)))

        pt = ProofTerm.substitution(inst, ProofTerm.subst_type(tyinst, eq_pt))
        if self.conds is not None:
            pt = ProofTerm.implies_elim(pt, *self.conds)

        As = pt.assums
        for A in As:
            pt = ProofTerm.implies_elim(pt, ProofTerm.assume(A))

        if not (pt.th.is_equals() and pt.th.prop.lhs == t):
            raise ConvException("rewr_conv: wrong result")

        return pt
