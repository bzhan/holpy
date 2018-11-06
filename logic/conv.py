# Author: Bohua Zhan

from kernel.type import Type
from kernel.term import Var, Term
from kernel.thm import Thm, InvalidDerivationException
from logic.proofterm import ProofTerm
from logic.matcher import Matcher, MatchException

class ConvException(Exception):
    pass

class Conv():
    """A conversion is a function for rewriting a term.

    A Conv object has two main methods:
    __call__ - function to obtain the equality from the term.
    get_proof_term - function to obtain the proof term for the equality.

    """
    def __call__(self, t):
        pass

    def get_proof_term(self, t):
        pass

class all_conv(Conv):
    """Returns the trivial equality t = t."""
    def __call__(self, t):
        return Thm.reflexive(t)

    def get_proof_term(self, t):
        return ProofTerm.reflexive(t)

class no_conv(Conv):
    """Always fails."""
    def __call__(self, t):
        raise ConvException()

    def get_proof_term(self, t):
        raise ConvException()

class combination_conv(Conv):
    """Apply cv1 to the function and cv2 to the argument."""
    def __init__(self, cv1, cv2):
        assert isinstance(cv1, Conv) and isinstance(cv2, Conv), "combination_conv: argument"
        self.cv1 = cv1
        self.cv2 = cv2

    def __call__(self, t):
        if t.ty != Term.COMB:
            raise ConvException()
        return Thm.combination(self.cv1(t.fun), self.cv2(t.arg))

    def get_proof_term(self, t):
        if t.ty != Term.COMB:
            raise ConvException()
        pt1 = self.cv1.get_proof_term(t.fun)
        pt2 = self.cv2.get_proof_term(t.arg)

        # Obtain some savings if one of pt1 and pt2 is reflexivity:
        if pt1.th.is_reflexive():
            return ProofTerm.arg_combination(pt2, pt1.th.concl.arg)
        elif pt2.th.is_reflexive():
            return ProofTerm.fun_combination(pt1, pt2.th.concl.arg)
        else:
            return ProofTerm.combination(pt1, pt2)

class then_conv(Conv):
    """Applies cv1, followed by cv2."""
    def __init__(self, cv1, cv2):
        assert isinstance(cv1, Conv) and isinstance(cv2, Conv), "then_conv: argument"
        self.cv1 = cv1
        self.cv2 = cv2

    def __call__(self, t):
        th1 = self.cv1(t)
        (_, t2) = th1.concl.dest_binop()
        th2 = self.cv2(t2)
        return Thm.transitive(th1, th2)

    def get_proof_term(self, t):
        pt1 = self.cv1.get_proof_term(t)
        (_, t2) = pt1.th.concl.dest_binop()
        pt2 = self.cv2.get_proof_term(t2)
        
        # Obtain some savings if one of pt1 and pt2 is reflexivity:
        if pt1.th.is_reflexive():
            return pt2
        elif pt2.th.is_reflexive():
            return pt1
        else:
            return ProofTerm.transitive(pt1, pt2)

class else_conv(Conv):
    """Applies cv1, if fails, apply cv2."""
    def __init__(self, cv1, cv2):
        assert isinstance(cv1, Conv) and isinstance(cv2, Conv), "else_conv: argument"
        self.cv1 = cv1
        self.cv2 = cv2

    def __call__(self, t):
        try:
            return self.cv1(t)
        except ConvException:
            return self.cv2(t)

    def get_proof_term(self, t):
        try:
            return self.cv1.get_proof_term(t)
        except ConvException:
            return self.cv2.get_proof_term(t)

class beta_conv(Conv):
    """Applies beta-conversion."""
    def __call__(self, t):
        try:
            return Thm.beta_conv(t)
        except InvalidDerivationException:
            raise ConvException()

    def get_proof_term(self, t):
        try:
            return ProofTerm.beta_conv(t)
        except InvalidDerivationException:
            raise ConvException()

class abs_conv(Conv):
    """Applies conversion to the body of abstraction."""
    def __init__(self, cv):
        assert isinstance(cv, Conv)
        self.cv = cv
    
    def __call__(self, t):
        if t.ty != Term.ABS:
            raise ConvException()
        
        # Find a new variable x and substitute for body
        v = Var(t.var_name, t.T)
        t2 = t.subst_bound(v)
        return Thm.abstraction(self.cv(t2), v)

    def get_proof_term(self, t):
        if t.ty != Term.ABS:
            raise ConvException()

        # Find a new variable x and substitute for body
        v = Var(t.var_name, t.T)
        t2 = t.subst_bound(v)
        return ProofTerm.abstraction(self.cv.get_proof_term(t2), v)

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

def fun2_conv(cv):
    return fun_conv(fun_conv(cv))

def binop_conv(cv):
    return combination_conv(arg_conv(cv), cv)

class sub_conv(Conv):
    def __init__(self, cv):
        self.cv = cv

    def __call__(self, t):
        return try_conv(else_conv(comb_conv(self.cv), abs_conv(self.cv)))(t)

    def get_proof_term(self, t):
        return try_conv(else_conv(comb_conv(self.cv), abs_conv(self.cv))).get_proof_term(t)

class bottom_conv(Conv):
    """Applies cv repeatedly in the bottom-up manner."""
    def __init__(self, cv):
        assert isinstance(cv, Conv), "bottom_conv: argument"
        self.cv = cv

    def __call__(self, t):
        return then_conv(sub_conv(self), try_conv(self.cv))(t)

    def get_proof_term(self, t):
        return then_conv(sub_conv(self), try_conv(self.cv)).get_proof_term(t)

class top_conv(Conv):
    """Applies cv repeatedly in the top-down manner."""
    def __init__(self, cv):
        assert isinstance(cv, Conv), "top_conv: argument"
        self.cv = cv

    def __call__(self, t):
        return then_conv(try_conv(self.cv), sub_conv(self))(t)

    def get_proof_term(self, t):
        return then_conv(try_conv(self.cv), sub_conv(self)).get_proof_term(t)

class rewr_conv(Conv):
    """Rewrite using the given equality theorem."""
    def __init__(self, pt):
        assert isinstance(pt, ProofTerm), "rewr_conv: argument"
        self.pt = pt
        self.th = pt.th

    def __call__(self, t):
        pat = self.th.concl.arg1
        inst = dict()

        try:
            inst = Matcher.first_order_match(pat, t)
        except MatchException:
            raise ConvException()

        return Thm.substitution(self.th, inst)

    def get_proof_term(self, t):
        pat = self.th.concl.arg1
        inst = dict()

        try:
            inst = Matcher.first_order_match(pat, t)
        except MatchException:
            raise ConvException()

        if inst:
            return ProofTerm.substitution(self.pt, inst)
        else:
            return self.pt
