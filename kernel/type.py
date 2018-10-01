# Author: Bohua Zhan

import abc
from enum import Enum

class UnknownTypeException(Exception):
    pass

class HOLType(abc.ABC):
    """Represents a type in higher-order logic.
    """

    VAR = 1
    COMP = 2

    def __init__(self, ty):
        self.ty = ty

    def is_fun(self):
        return self.ty == HOLType.COMP and self.name == "fun"
    
    def domain_type(self):
        assert(self.is_fun())
        return self.args[0]
    
    def range_type(self):
        assert(self.is_fun())
        return self.args[1]
        
    def __str__(self):
        if self.ty == HOLType.VAR:
            return "'" + self.name
        elif self.ty == HOLType.COMP:
            if len(self.args) == 0:
                return self.name
            elif len(self.args) == 1:
                return str(self.args[0]) + " " + self.name
            elif HOLType.is_fun(self):
                # 'a => 'b => 'c associates to the right. So parenthesis is
                # needed to express ('a => 'b) => 'c.
                if HOLType.is_fun(self.args[0]):
                    return "(" + str(self.args[0]) + ") => " + str(self.args[1])
                else:
                    return str(self.args[0]) + " => " + str(self.args[1])
            else:
                return "(" + ", ".join(str(t) for t in self.args) + ") " + self.name
        else:
            raise UnknownTypeException()

    def __repr__(self):
        return str(self)

    def __hash__(self):
        if self.ty == HOLType.VAR:
            return hash(("VAR", self.name))
        elif self.ty == HOLType.COMP:
            return hash(("COMP", self.name, tuple(hash(arg) for arg in self.args)))
    
    def __eq__(self, other):
        if self.ty != other.ty:
            return False
        elif self.ty == HOLType.VAR:
            return self.name == other.name
        elif self.ty == HOLType.COMP:
            return self.name == other.name and self.args == other.args
        else:
            raise UnknownTypeException()

    def subst(self, subst):
        """Given a dictionary subst mapping from names to types,
        simultaneously substitute for the type variables using the
        dictionary.

        """
        assert isinstance(subst, dict), "subst must be a dictionary"
        if self.ty == HOLType.VAR:
            if self.name in subst:
                return subst[self.name]
            else:
                return self
        elif self.ty == HOLType.COMP:
            return Type(self.name, [T.subst(subst) for T in self.args])
        else:
            raise UnknownTypeException()

def TVar(name):
    T = HOLType(HOLType.VAR)
    T.name = name
    return T

def Type(name, args = []):
    T = HOLType(HOLType.COMP)
    T.name = name
    if isinstance(args, list):
        T.args = args
    else:
        T.args = [args]
    return T

def TFun(arg1, arg2):
    return Type("fun", [arg1, arg2])

hol_bool = Type("bool")
