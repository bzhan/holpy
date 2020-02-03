# Author: Bohua Zhan

from kernel.term import Const
from kernel.thm import Thm


class Extension():
    """Represents a single extension to the theory.

    There are currently four kinds of extensions:

    TConst(name, arity): extend the theory by a type with the given
    name and arity.

    Constant(name, T): extend the theory by a constant with the given
    name and type.

    Theorem(name, th, prf): extend the theory by adding a theorem with
    the given name and statement. If prf = None, then the theorem should
    be accepted as an axiom. Otherwise prf is a proof of the theorem.

    Attribute(name, attribute): add given attribute to the given theorem.

    Overload(name): extend the theory by adding an overloading of a
    constant.

    """
    # ty values for distinguishing between Extension objects.
    TCONST, CONSTANT, THEOREM, ATTRIBUTE, OVERLOAD = range(5)

    def is_tconst(self):
        return self.ty == Extension.TCONST

    def is_constant(self):
        return self.ty == Extension.CONSTANT

    def is_theorem(self):
        return self.ty == Extension.THEOREM

    def is_attribute(self):
        return self.ty == Extension.ATTRIBUTE

    def is_overload(self):
        return self.ty == Extension.OVERLOAD

    def __str__(self):
        if self.ty == Extension.TCONST:
            return "Type " + self.name + " " + str(self.arity)
        elif self.ty == Extension.CONSTANT:
            ref_str = " (" + self.ref_name + ")" if self.ref_name != self.name else ""
            return "Constant " + self.name + " :: " + str(self.T) + ref_str
        elif self.ty == Extension.THEOREM:
            return "Theorem " + self.name + ": " + str(self.th)
        elif self.ty == Extension.ATTRIBUTE:
            return "Attribute " + self.name + " [" + self.attribute + "]"
        elif self.ty == Extension.OVERLOAD:
            return "Overload " + self.name
        else:
            raise TypeError

    def __repr__(self):
        return str(self)

    def __eq__(self, other):
        if self.ty != other.ty:
            return False
        elif self.ty == Extension.TCONST:
            return self.name == other.name and self.arity == other.arity
        elif self.ty == Extension.CONSTANT:
            return self.name == other.name and self.T == other.T
        elif self.ty == Extension.THEOREM:
            return self.name == other.name and self.th == other.th and self.prf == other.prf
        elif self.ty == Extension.ATTRIBUTE:
            return self.name == other.name and self.attribute == other.attribute
        elif self.ty == Extension.OVERLOAD:
            return self.name == other.name
        else:
            raise TypeError


class TConst(Extension):
    def __init__(self, name, arity):
        """Extending the theory by adding an type.

        name -- name of the type.
        arity -- arity of the type.

        """
        self.ty = Extension.TCONST
        self.name = name
        self.arity = arity

class Constant(Extension):
    def __init__(self, name, T, *, ref_name=None):
        """Extending the theory by adding a constant.
        
        name -- name of the constant.
        T -- type of the constant.

        """
        self.ty = Extension.CONSTANT
        self.name = name
        self.T = T
        self.ref_name = name if ref_name is None else ref_name

class Theorem(Extension):
    def __init__(self, name, th, prf=None):
        """Extending the theory by adding an axiom/theorem.

        name -- name of the theorem.
        th -- statement of the theorem.
        prf -- proof of the theorem. If None, this is an axiomatic extension.

        """
        self.ty = Extension.THEOREM
        self.name = name
        self.th = th
        self.prf = prf

class Attribute(Extension):
    def __init__(self, name, attribute):
        """Extend the theory by adding an attribute.

        name -- name of the theorem.
        attribute -- name of the attribute.

        """
        self.ty = Extension.ATTRIBUTE
        self.name = name
        self.attribute = attribute

class Overload(Extension):
    def __init__(self, name):
        """Extending the theory by adding an overloaded constant.

        name -- name of the overloaded constant.

        """
        self.ty = Extension.OVERLOAD
        self.name = name
