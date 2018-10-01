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
    def implies_intr(A, th):
        """Derivation rule IMPLIES_INTR:

        A |- B
        ------------
        |- A --> B
        """
        if A in list(th.assums):
            return Thm(th.assums.difference({A}), mk_implies(A, th.concl))
        else:
            raise InvalidDerivationException()

    @staticmethod
    def implies_elim(th1, th2):
        """Derivation rule IMPLIES_ELIM (modus ponens):

        |- A --> B
        |- A
        ------------
        |- B
        """
        if is_implies(th1.concl):
            (A, B) = dest_binop(th1.concl)
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
        return Thm([], mk_equals(x,x))

    @staticmethod
    def symmetric(th):
        """Derivation rule SYMMETRIC:

        |- x = y
        ------------
        |- y = x
        """
        if is_equals(th.concl):
            (x, y) = dest_binop(th.concl)
            return Thm(th.assums, mk_equals(y,x))
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
        if is_equals(th1.concl) and is_equals(th2.concl):
            (x, y1) = dest_binop(th1.concl)
            (y2, z) = dest_binop(th2.concl)
            if y1 == y2:
                return Thm(th1.assums.union(th2.assums), mk_equals(x,z))
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
        if is_equals(th1.concl) and is_equals(th2.concl):
            (f, g) = dest_binop(th1.concl)
            (x, y) = dest_binop(th2.concl)
            return Thm(th1.assums.union(th2.assums), mk_equals(Comb(f,x), Comb(g,y)))
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
        if is_implies(th1.concl) and is_implies(th2.concl):
            (A1, B1) = dest_binop(th1.concl)
            (B2, A2) = dest_binop(th2.concl)
            if A1 == A2 and B1 == B2:
                return Thm(th1.assums.union(th2.assums), mk_equals(A1, B1))
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
        if is_equals(th1.concl):
            (A, B) = dest_binop(th1.concl)
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
        ----------
        A[s] |- B[s]
        """
        assums_new = [assum.subst_type(subst) for assum in th.assums]
        concl_new = th.concl.subst_type(subst)
        return Thm(assums_new, concl_new)
