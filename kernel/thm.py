# Author: Bohua Zhan

import abc
from kernel.type import *
from kernel.term import *

class InvalidDerivationException(Exception):
    pass

class Thm(abc.ABC):
    """Represents a theorem in the sequent calculus.

    A theorem is given by a set of assumptions and the conclusion.
    The theorem (As, C) is usually written as:

    A1, ... An |- C.
    """

    def __init__(self, assums, concl):
        self.assums = set(assums)
        self.concl = concl

    def __str__(self):
        if self.assums:
            str_assums = ", ".join(sorted(repr(assum) for assum in self.assums))
            return str_assums + " |- " + repr(self.concl)
        else:
            return "|- " + repr(self.concl)

    def __repr__(self):
        return str(self)

    def __eq__(self, other):
        """Note order of assumptions does not matter when comparing for
        equality.
        """
        return self.assums == other.assums and self.concl == other.concl

    @staticmethod
    def assume(A):
        """Derivation rule ASSUME:

        A |- A
        """
        return Thm([A], A)
    
    @staticmethod
    def implies_intr(th, A):
        """Derivation rule IMPLIES_INTR:

        A |- B
        ------------
        |- A --> B
        """
        return Thm(th.assums.difference({A}), Term.mk_implies(A, th.concl))

    @staticmethod
    def implies_elim(th1, th2):
        """Derivation rule IMPLIES_ELIM (modus ponens):

        |- A --> B
        |- A
        ------------
        |- B
        """
        if th1.concl.is_implies():
            (A, B) = th1.concl.dest_binop()
            if A == th2.concl:
                return Thm(th1.assums.union(th2.assums), B)
            else:
                raise InvalidDerivationException()
        else:
            raise InvalidDerivationException()

    @staticmethod
    def reflexive(x):
        """Derivation rule REFLEXIVE:

        |- x = x
        """
        return Thm([], Term.mk_equals(x,x))

    @staticmethod
    def symmetric(th):
        """Derivation rule SYMMETRIC:

        |- x = y
        ------------
        |- y = x
        """
        if th.concl.is_equals():
            (x, y) = th.concl.dest_binop()
            return Thm(th.assums, Term.mk_equals(y,x))
        else:
            raise InvalidDerivationException()

    @staticmethod
    def transitive(th1, th2):
        """Derivation rule TRANSITIVE:

        |- x = y
        |- y = z
        ------------
        |- x = z
        """
        if th1.concl.is_equals() and th2.concl.is_equals():
            (x, y1) = th1.concl.dest_binop()
            (y2, z) = th2.concl.dest_binop()
            if y1 == y2:
                return Thm(th1.assums.union(th2.assums), Term.mk_equals(x,z))
            else:
                raise InvalidDerivationException()
        else:
            raise InvalidDerivationException()

    @staticmethod
    def combination(th1, th2):
        """Derivation rule COMBINATION:

        |- f = g
        |- x = y
        ------------
        |- f x = g y
        """
        if th1.concl.is_equals() and th2.concl.is_equals():
            (f, g) = th1.concl.dest_binop()
            (x, y) = th2.concl.dest_binop()
            return Thm(th1.assums.union(th2.assums), Term.mk_equals(Comb(f,x), Comb(g,y)))
        else:
            raise InvalidDerivationException()

    @staticmethod
    def equal_intr(th1, th2):
        """Derivation rule EQUAL_INTR:

        |- A --> B
        |- B --> A
        ------------
        |- A = B
        """
        if th1.concl.is_implies() and th2.concl.is_implies():
            (A1, B1) = th1.concl.dest_binop()
            (B2, A2) = th2.concl.dest_binop()
            if A1 == A2 and B1 == B2:
                return Thm(th1.assums.union(th2.assums), Term.mk_equals(A1, B1))
            else:
                raise InvalidDerivationException()
        else:
            raise InvalidDerivationException()

    @staticmethod
    def equal_elim(th1, th2):
        """Derivation rule EQUAL_ELIM:

        |- A = B
        |- A
        ------------
        |- B
        """
        if th1.concl.is_equals():
            (A, B) = th1.concl.dest_binop()
            if A == th2.concl:
                return Thm(th1.assums.union(th2.assums), B)
            else:
                raise InvalidDerivationException()
        else:
            raise InvalidDerivationException()

    @staticmethod
    def subst_type(th, subst):
        """Derivation rule SUBST_TYPE:

        Perform substitution on the type variables.

        A |- B
        ------------
        A[s] |- B[s]  where s is substitution on types

        """
        assums_new = [assum.subst_type(subst) for assum in th.assums]
        concl_new = th.concl.subst_type(subst)
        return Thm(assums_new, concl_new)

    @staticmethod
    def substitution(th, subst):
        """Derivation rule SUBSTITUTION:

        Perform substitution on the term variables.

        A |- B
        ------------
        A[s] |- B[s]  where s is substitution on terms

        """
        try:
            assums_new = [assum.subst(subst) for assum in th.assums]
            concl_new = th.concl.subst(subst)
        except TermSubstitutionException:
            raise InvalidDerivationException()
        return Thm(assums_new, concl_new)

    @staticmethod
    def beta_conv(t):
        """Derivation rule BETA_CONV:

        |- (%x. t1) t2 = t1[t2/x]
        """
        try:
            t_new = t.beta_conv()
        except TermSubstitutionException:
            raise InvalidDerivationException()
        return Thm([], Term.mk_equals(t, t_new))

    @staticmethod
    def abstraction(th, x):
        """Derivation rule ABSTRACTION:

        A |- t1 = t2
        ------------------------
        A |- (%x. t1) = (%x. t2)  where x does not occur in A.
        """
        if any(assum.occurs_var(x) for assum in th.assums):
            raise InvalidDerivationException()
        elif th.concl.is_equals():
            (t1, t2) = th.concl.dest_binop()
            try:
                (t1_new, t2_new) = (t1.abstract_over(x), t2.abstract_over(x))
            except TermSubstitutionException:
                raise InvalidDerivationException()
            return Thm(th.assums, Term.mk_equals(t1_new, t2_new))
        else:
            raise InvalidDerivationException()

# Table of base derivations
base_deriv = {
    "assume" : Thm.assume,
    "implies_intr" : Thm.implies_intr,
    "implies_elim" : Thm.implies_elim,
}
