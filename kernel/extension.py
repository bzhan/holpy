# Author: Bohua Zhan

from kernel.term import Const
from kernel.thm import Thm

TYPE, CONSTANT, THEOREM, MACRO, METHOD, ATTRIBUTE, OVERLOAD = range(7)

class Extension():
    """Represents a single extension to the theory.

    There are currently four kinds of extensions:

    Type(name, arity): extend the theory by a type with the given
    name and arity.

    Constant(name, T): extend the theory by a constant with the given
    name and type.

    Theorem(name, th, prf): extend the theory by adding a theorem with
    the given name and statement. If prf = None, then the theorem should
    be accepted as an axiom. Otherwise prf is a proof of the theorem.

    Attribute(name, attribute): add given attribute to the given theorem.

    Macro(name): extend the theory by adding the given macro from
    global_macros.

    Method(name): extend the theory by adding the given method from
    global_methods.

    Overload(name): extend the theory by adding an overloading of a
    constant.

    """
    def __str__(self):
        if self.ty == TYPE:
            return "Type " + self.name + " " + str(self.arity)
        elif self.ty == CONSTANT:
            ref_str = " (" + self.ref_name + ")" if self.ref_name != self.name else ""
            return "Constant " + self.name + " :: " + str(self.T) + ref_str
        elif self.ty == THEOREM:
            return "Theorem " + self.name + ": " + str(self.th)
        elif self.ty == ATTRIBUTE:
            return "Attribute " + self.name + " [" + self.attribute + "]"
        elif self.ty == MACRO:
            return "Macro " + self.name
        elif self.ty == METHOD:
            return "Method " + self.name
        elif self.ty == OVERLOAD:
            return "Overload " + self.name
        else:
            raise TypeError

    def __repr__(self):
        return str(self)

    def __eq__(self, other):
        if self.ty != other.ty:
            return False
        elif self.ty == TYPE:
            return self.name == other.name and self.arity == other.arity
        elif self.ty == CONSTANT:
            return self.name == other.name and self.T == other.T
        elif self.ty == THEOREM:
            return self.name == other.name and self.th == other.th and self.prf == other.prf
        elif self.ty == ATTRIBUTE:
            return self.name == other.name and self.attribute == other.attribute
        elif self.ty == MACRO:
            return self.name == other.name
        elif self.ty == METHOD:
            return self.name == other.name
        elif self.ty == OVERLOAD:
            return self.name == other.name
        else:
            raise TypeError


class Type(Extension):
    def __init__(self, name, arity):
        """Extending the theory by adding an type.

        name -- name of the type.
        arity -- arity of the type.

        """
        self.ty = TYPE
        self.name = name
        self.arity = arity

class Constant(Extension):
    def __init__(self, name, T, *, ref_name=None):
        """Extending the theory by adding a constant.
        
        name -- name of the constant.
        T -- type of the constant.

        """
        self.ty = CONSTANT
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
        self.ty = THEOREM
        self.name = name
        self.th = th
        self.prf = prf

class Attribute(Extension):
    def __init__(self, name, attribute):
        """Extend the theory by adding an attribute.

        name -- name of the theorem.
        attribute -- name of the attribute.

        """
        self.ty = ATTRIBUTE
        self.name = name
        self.attribute = attribute

class Macro(Extension):
    def __init__(self, name):
        """Extending the theory by adding a macro.

        name -- name of the macro.

        """
        self.ty = MACRO
        self.name = name

class Method(Extension):
    def __init__(self, name):
        """Extending the theory by adding a method.

        name -- name of the method.

        """
        self.ty = METHOD
        self.name = name

class Overload(Extension):
    def __init__(self, name):
        """Extending the theory by adding an overloaded constant.

        name -- name of the overloaded constant.

        """
        self.ty = OVERLOAD
        self.name = name
