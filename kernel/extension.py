# Author: Bohua Zhan

import abc
from kernel.term import Const
from kernel.thm import Thm

class Extension(abc.ABC):
    """A single extension to a theory.
    
    ty -- type of the extension (add new type, axiomatized constant,
    defined constant, or theorem).    

    """
    (TYPE, AX_CONSTANT, CONSTANT, THEOREM) = range(4)

    def __init__(self, ty):
        self.ty = ty

    @staticmethod
    def AxConstant(name, T):
        """Extending the theory by adding an axiomatized constant.

        name -- name of the constant.
        T -- type of the constant.
        
        """
        t = Extension(Extension.AX_CONSTANT)
        t.name = name
        t.T = T
        return t

    @staticmethod
    def Constant(name, expr):
        """Extending the theory by adding a constant.
        
        name -- name of the constant.
        expr -- the value the constant is equal to.

        """
        t = Extension(Extension.CONSTANT)
        t.name = name
        t.expr = expr
        return t

    @staticmethod
    def Theorem(name, th, prf = None):
        """Extending the theory by adding an axiom/theorem.

        name -- name of the theorem.
        th -- statement of the theorem.
        prf -- proof of the theorem. If None, this is an axiomatic extension.

        """
        t = Extension(Extension.THEOREM)
        t.name = name
        t.th = th
        t.prf = prf
        return t

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
