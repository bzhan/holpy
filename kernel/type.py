# Author: Bohua Zhan

import abc
from enum import Enum

class UnknownTypeException(Exception):
    pass

class TypeMatchException(Exception):
    pass

class HOLType(abc.ABC):
    """Represents a type in higher-order logic.
    """

    (VAR, COMB) = range(2)

    def __init__(self, ty):
        self.ty = ty

    def is_fun(self):
        return self.ty == HOLType.COMB and self.name == "fun"
    
    def domain_type(self):
        assert(self.is_fun())
        return self.args[0]
    
    def range_type(self):
        assert(self.is_fun())
        return self.args[1]
        
    def __str__(self):
        if self.ty == HOLType.VAR:
            return "'" + self.name
        elif self.ty == HOLType.COMB:
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
        elif self.ty == HOLType.COMB:
            return hash(("COMB", self.name, tuple(hash(arg) for arg in self.args)))
    
    def __eq__(self, other):
        if self.ty != other.ty:
            return False
        elif self.ty == HOLType.VAR:
            return self.name == other.name
        elif self.ty == HOLType.COMB:
            return self.name == other.name and self.args == other.args
        else:
            raise UnknownTypeException()

    def subst(self, tyinst):
        """Given a dictionary tyinst mapping from names to types,
        simultaneously substitute for the type variables using the
        dictionary.

        """
        assert isinstance(tyinst, dict), "tyinst must be a dictionary"
        if self.ty == HOLType.VAR:
            if self.name in tyinst:
                return tyinst[self.name]
            else:
                return self
        elif self.ty == HOLType.COMB:
            return Type(self.name, [T.subst(tyinst) for T in self.args])
        else:
            raise UnknownTypeException()

    @staticmethod
    def TVar(name):
        T = HOLType(HOLType.VAR)
        T.name = name
        return T

    @staticmethod
    def Type(name, args = []):
        T = HOLType(HOLType.COMB)
        T.name = name
        if isinstance(args, list):
            T.args = args
        else:
            T.args = [args]
        return T

    @staticmethod
    def TFun(*args):
        """Returns the function type arg1 => arg2 => ... => argn."""
        res = args[-1]
        for arg in reversed(args[:-1]):
            res = Type("fun", [arg, res])
        return res

    def match_incr(self, T, tyinst):
        """Incremental match. Here tyinst is the current instantiation.
        This is updated by the function.

        """
        if self.ty == HOLType.VAR:
            if self.name in tyinst:
                if T != tyinst[self.name]:
                    raise TypeMatchException()
            else:
                tyinst[self.name] = T
        elif self.ty == HOLType.COMB:
            if T.ty != HOLType.COMB or T.name != self.name:
                raise TypeMatchException()
            else:
                for (arg, argT) in zip(self.args, T.args):
                    arg.match_incr(argT, tyinst)
        else:
            raise UnknownTypeException()

    def match(self, T):
        """Match self with T. Returns either a dictionary containing the
        match, or raise TypeMatchException.

        """
        tyinst = dict()
        self.match_incr(T, tyinst)
        return tyinst

TVar = HOLType.TVar
Type = HOLType.Type
TFun = HOLType.TFun
hol_bool = Type("bool")
