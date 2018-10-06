# Author: Bohua Zhan

import abc
from kernel.term import Const
from kernel.thm import Thm

class Extension(abc.ABC):
    """A single extension to a theory. There are currently three kinds
    of extensions, to be defined below.

    """
    (AX_CONSTANT, CONSTANT, THEOREM) = range(3)

    def __str__(self):
        if self.ty == Extension.AX_CONSTANT:
            return "AxConstant " + self.name + " :: " + str(self.T)
        elif self.ty == Extension.CONSTANT:
            return "Constant " + self.name + " = " + str(self.expr)
        elif self.ty == Extension.THEOREM:
            return "Theorem " + self.name + ": " + str(self.th)
        else:
            raise TypeError()

    def __repr__(self):
        return str(self)

    def get_const_term(self):
        """Return the term to be added in the Constant extension."""
        assert self.ty == Extension.CONSTANT, "get_const_term"
        return Const(self.name, self.expr.get_type())

    def get_eq_thm(self):
        """Return the equality theorem to be added in the Constant extension."""
        assert self.ty == Extension.CONSTANT, "get_eq_thm"
        return Thm.mk_equals(self.get_const_term(), self.expr)
    
class AxConstant(Extension):
    def __init__(self, name, T):
        """Extending the theory by adding an axiomatized constant.

        name -- name of the constant.
        T -- type of the constant.
        
        """
        self.ty = Extension.AX_CONSTANT
        self.name = name
        self.T = T

class Constant(Extension):
    def __init__(self, name, expr):
        """Extending the theory by adding a constant by definition.
        
        name -- name of the constant.
        expr -- the expression the constant is equal to.

        """
        self.ty = Extension.CONSTANT
        self.name = name
        self.expr = expr

class Theorem(Extension):
    def __init__(self, name, th, prf = None):
        """Extending the theory by adding an axiom/theorem.

        name -- name of the theorem.
        th -- statement of the theorem.
        prf -- proof of the theorem. If None, this is an axiomatic extension.

        """
        self.ty = Extension.THEOREM
        self.name = name
        self.th = th
        self.prf = prf

class TheoryExtension(abc.ABC):
    """A theory extension contains a list of extensions to a theory. These
    may involve new types, constants, and theorems. Definition of
    new types, constants, and theorems may be accompanied by proof, which
    can be checked by the theory.

    """
    def __init__(self):
        self.data = []

    def add_extension(self, extension):
        """Add a new extension."""
        self.data.append(extension)

    def get_extensions(self):
        """Return list of extensions."""
        return self.data

    def __str__(self):
        return "\n".join(str(ext) for ext in self.data)

    def __repr__(self):
        return str(self)
