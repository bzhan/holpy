# Author: Bohua Zhan

from collections import OrderedDict

from kernel.type import Type, hol_bool
from kernel.term import Term, Var, TermSubstitutionException, TypeCheckException
from kernel.macro import MacroSig

class InvalidDerivationException(Exception):
    """Exception during derivation. Provides error message."""
    def __init__(self, str):
        self.str = str

class Thm():
    """Represents a theorem in sequent calculus.

    A theorem is given by a list of hypotheses and a proposition.
    The theorem (As, C) means the list of hypotheses As implies the
    proposition C. It is usually written as:

    A1, ... An |- C.

    For a theorem statement to be well-formed, every item in the list As
    as well as C must be well-formed terms of type boolean.

    This module also contains the list of primitive deduction rules for
    higher-order logic. Each primitive deduction rule represents a logically
    sound way of constructing a new theorem from a (possibly empty) list of
    old theorems. In principle, every theorem should be constructed using
    primitive deduction rules from the initial axioms. However, this is not
    enforced by this module, nor is the proof object stored in the theorem.
    Proof objects are managed by the Proof module.

    """
    def __init__(self, hyps, prop):
        """Create a theorem with the given list of hypotheses and
        proposition.

        """
        self.hyps = tuple(hyps)
        self.prop = prop
        assert all(isinstance(A, Term) for A in self.hyps), "Thm: hyps must be terms."
        assert isinstance(prop, Term), "Thm: proposition must be a term."

    @property
    def assums(self):
        return self.prop.strip_implies()[0]

    @property
    def concl(self):
        return self.prop.strip_implies()[1]

    def __str__(self):
        """Print the given theorem."""
        if self.hyps:
            str_hyps = ", ".join(str(hyp) for hyp in self.hyps)
            return str_hyps + " |- " + str(self.prop)
        else:
            return "|- " + str(self.prop)

    def __repr__(self):
        return str(self)

    def __hash__(self):
        return hash(("HYPS", tuple(self.hyps), "PROP", self.prop))

    def __eq__(self, other):
        """Note order of hypotheses does not matter when comparing for
        equality.

        """
        return set(self.hyps) == set(other.hyps) and self.prop == other.prop

    def check_thm_type(self):
        """Make sure the all hypotheses and proposition type-check and
        have type boolean.
        
        """
        for t in list(self.hyps) + [self.prop]:
            if t.checked_get_type() != hol_bool:
                raise TypeCheckException()

    @staticmethod
    def mk_implies(*args):
        """Returns the theorem s1 --> ... --> sn --> t."""
        return Thm([], Term.mk_implies(*args))

    @staticmethod
    def mk_equals(x, y):
        """Returns the theorem x = y."""
        return Thm([], Term.mk_equals(x, y))

    def is_reflexive(self):
        """Check whether the proposition of the theorem is of the form x = y."""
        return self.prop.is_equals() and self.prop.arg1 == self.prop.arg

    def can_prove(self, target):
        """Determine whether self is sufficient to prove target."""
        return self.prop == target.prop and set(self.hyps).issubset(set(target.hyps))

    @staticmethod
    def assume(A):
        """Derivation rule ASSUME:

        A |- A
        """
        assert isinstance(A, Term), "Thm.assume"
        return Thm([A], A)
    
    @staticmethod
    def implies_intr(A, th):
        """Derivation rule IMPLIES_INTR:

        A |- B
        ------------
        |- A --> B
        """
        return Thm(tuple(t for t in th.hyps if t != A), Term.mk_implies(A, th.prop))

    @staticmethod
    def implies_elim(th1, th2):
        """Derivation rule IMPLIES_ELIM (modus ponens):

        |- A --> B
        |- A
        ------------
        |- B
        """
        if th1.prop.is_implies():
            A, B = th1.prop.args
            if A == th2.prop:
                return Thm(list(OrderedDict.fromkeys(th1.hyps + th2.hyps)), B)
            else:
                raise InvalidDerivationException("implies_elim: " + str(A) + " ~= " + str(th2.prop))
        else:
            raise InvalidDerivationException("implies_elim")

    @staticmethod
    def reflexive(x):
        """Derivation rule REFLEXIVE:

        |- x = x
        """
        return Thm.mk_equals(x, x)

    @staticmethod
    def symmetric(th):
        """Derivation rule SYMMETRIC:

        |- x = y
        ------------
        |- y = x
        """
        if th.prop.is_equals():
            x, y = th.prop.args
            return Thm(th.hyps, Term.mk_equals(y, x))
        else:
            raise InvalidDerivationException("symmetric")

    @staticmethod
    def transitive(th1, th2):
        """Derivation rule TRANSITIVE:

        |- x = y
        |- y = z
        ------------
        |- x = z
        """
        if th1.prop.is_equals() and th2.prop.is_equals():
            x, y1 = th1.prop.args
            y2, z = th2.prop.args
            if y1 == y2:
                return Thm(list(OrderedDict.fromkeys(th1.hyps + th2.hyps)), Term.mk_equals(x, z))
            else:
                raise InvalidDerivationException("transitive: middle term")
        else:
            raise InvalidDerivationException("transitive: not equalities")

    @staticmethod
    def combination(th1, th2):
        """Derivation rule COMBINATION:

        |- f = g
        |- x = y
        ------------
        |- f x = g y
        """
        if th1.prop.is_equals() and th2.prop.is_equals():
            f, g = th1.prop.args
            x, y = th2.prop.args
            Tf = f.get_type()
            if Tf.is_fun() and Tf.domain_type() == x.get_type():
                return Thm(list(OrderedDict.fromkeys(th1.hyps + th2.hyps)), Term.mk_equals(f(x), g(y)))
            else:
                raise InvalidDerivationException("combination")
        else:
            raise InvalidDerivationException("combination")

    @staticmethod
    def equal_intr(th1, th2):
        """Derivation rule EQUAL_INTR:

        |- A --> B
        |- B --> A
        ------------
        |- A = B
        """
        if th1.prop.is_implies() and th2.prop.is_implies():
            A1, B1 = th1.prop.args
            B2, A2 = th2.prop.args
            if A1 == A2 and B1 == B2:
                return Thm(list(OrderedDict.fromkeys(th1.hyps + th2.hyps)), Term.mk_equals(A1, B1))
            else:
                raise InvalidDerivationException("equal_intr")
        else:
            raise InvalidDerivationException("equal_intr")

    @staticmethod
    def equal_elim(th1, th2):
        """Derivation rule EQUAL_ELIM:

        |- A = B
        |- A
        ------------
        |- B
        """
        if th1.prop.is_equals():
            A, B = th1.prop.args
            if A == th2.prop:
                return Thm(list(OrderedDict.fromkeys(th1.hyps + th2.hyps)), B)
            else:
                raise InvalidDerivationException("equal_elim")
        else:
            raise InvalidDerivationException("equal_elim")

    @staticmethod
    def subst_type(tyinst, th):
        """Derivation rule SUBST_TYPE:

        Perform substitution on the type variables.

        A |- B
        ------------
        A[s] |- B[s]  where s is substitution on types

        """
        hyps_new = [hyp.subst_type(tyinst) for hyp in th.hyps]
        prop_new = th.prop.subst_type(tyinst)
        return Thm(hyps_new, prop_new)

    @staticmethod
    def substitution(inst, th):
        """Derivation rule SUBSTITUTION:

        Perform substitution on the term variables.

        A |- B
        ------------
        A[s] |- B[s]  where s is substitution on terms

        """
        try:
            hyps_new = [hyp.subst(inst) for hyp in th.hyps]
            prop_new = th.prop.subst(inst)
        except TermSubstitutionException:
            raise InvalidDerivationException("substitution")
        return Thm(hyps_new, prop_new)

    @staticmethod
    def beta_conv(t):
        """Derivation rule BETA_CONV:

        |- (%x. t1) t2 = t1[t2/x]
        """
        try:
            t_new = t.beta_conv()
        except TermSubstitutionException:
            raise InvalidDerivationException("beta_conv")
        return Thm.mk_equals(t, t_new)

    @staticmethod
    def abstraction(x, th):
        """Derivation rule ABSTRACTION:

        A |- t1 = t2
        ------------------------
        A |- (%x. t1) = (%x. t2)  where x does not occur in A.
        """
        if any(hyp.occurs_var(x) for hyp in th.hyps):
            raise InvalidDerivationException("abstraction")
        elif th.prop.is_equals():
            t1, t2 = th.prop.args
            try:
                t1_new, t2_new = (Term.mk_abs(x, t1), Term.mk_abs(x, t2))
            except TermSubstitutionException:
                raise InvalidDerivationException("abstraction")
            return Thm(th.hyps, Term.mk_equals(t1_new, t2_new))
        else:
            raise InvalidDerivationException("abstraction")

    @staticmethod
    def forall_intr(x, th):
        """Derivation rule FORALL_INTR:

        A |- t
        ------------
        A |- !x. t    where x does not occur in A.
        """
        if any(hyp.occurs_var(x) for hyp in th.hyps):
            raise InvalidDerivationException("forall_intr")
        elif x.ty != Term.VAR:
            raise InvalidDerivationException("forall_intr")
        else:
            return Thm(th.hyps, Term.mk_all(x, th.prop))

    @staticmethod
    def forall_elim(s, th):
        """Derivation rule FORALL_ELIM:

        |- !x. t
        ------------
        |- t[s/x]
        """
        if th.prop.is_all():
            if th.prop.arg.var_T != s.get_type():
                raise InvalidDerivationException("forall_elim")
            else:
                return Thm(th.hyps, th.prop.arg.subst_bound(s))
        else:
            raise InvalidDerivationException("forall_elim")

# Table of primitive derivations
primitive_deriv = {
    "assume" : (Thm.assume, MacroSig.TERM),
    "implies_intr" : (Thm.implies_intr, MacroSig.TERM),
    "implies_elim" : (Thm.implies_elim, MacroSig.NONE),
    "reflexive" : (Thm.reflexive, MacroSig.TERM),
    "symmetric" : (Thm.symmetric, MacroSig.NONE),
    "transitive" : (Thm.transitive, MacroSig.NONE),
    "combination" : (Thm.combination, MacroSig.NONE),
    "equal_intr" : (Thm.equal_intr, MacroSig.NONE),
    "equal_elim" : (Thm.equal_elim, MacroSig.NONE),
    "subst_type" : (Thm.subst_type, MacroSig.TYINST),
    "substitution" : (Thm.substitution, MacroSig.INST),
    "beta_conv" : (Thm.beta_conv, MacroSig.TERM),
    "abstraction" : (Thm.abstraction, MacroSig.TERM),
    "forall_intr" : (Thm.forall_intr, MacroSig.TERM),
    "forall_elim" : (Thm.forall_elim, MacroSig.TERM)
}
