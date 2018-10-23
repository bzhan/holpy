# Author: Bohua Zhan

import abc

class TypeMatchException(Exception):
    pass

class HOLType(abc.ABC):
    """Represents a type in higher-order logic.
    
    Types in HOL are formed by two kinds of constructors: TVar and Type.

    TVar(name) represents a type variable with the given name. Type(f, args)
    represents a type constant applied to a list of arguments.
    
    There are two fundamental type constants:
    
    - booleans, with name "bool" and no arguments.
    
    - functions, with name "fun" and two arguments: the domain and codomain
    types. Type("fun", a, b) is printed as a => b. The => sign associates to
    the right.
    
    Further defined type constants include:
    
    - natural numbers, with name "nat" and no arguments.
    
    - lists, with name "list" and one argument.

    - product, with name "prod" and two arguments. Type("prod", a, b) is
    printed as a * b.
    
    Examples:
    
    nat => bool: functions from natural numbers to booleans (predicates on
    natural numbers).

    nat => nat: functions from natural numbers to natural numbers.

    nat => nat => nat: or nat => (nat => nat), functions from two natural
    numbers to natural numbers.

    nat * nat => nat: functions from a pair of natural numbers to natural
    numbers.

    nat list: list of natural numbers.

    nat list list: list of lists of natural numbers.

    """
    (VAR, COMB) = range(2)

    def is_fun(self):
        """Whether self is of the form a => b."""
        return self.ty == HOLType.COMB and self.name == "fun"
    
    def domain_type(self):
        """Given a type of form a => b, return a."""
        assert(self.is_fun())
        return self.args[0]
    
    def range_type(self):
        """Given a type of form a => b, return b."""
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
            raise TypeError()

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
            raise TypeError()

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
            return Type(self.name, *(T.subst(tyinst) for T in self.args))
        else:
            raise TypeError()

    def match_incr(self, T, tyinst):
        """Incremental match. Match self (as a pattern) with T. Here tyinst
        is the current instantiation. This is updated by the function.

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
            raise TypeError()

    def match(self, T):
        """Match self (as a pattern) with T. Returns either a dictionary
        containing the match, or raise TypeMatchException.

        """
        tyinst = dict()
        self.match_incr(T, tyinst)
        return tyinst

class TVar(HOLType):
    """Type variable."""
    def __init__(self, name):
        self.ty = HOLType.VAR
        self.name = name

class Type(HOLType):
    """Type constant, applied to a list of arguments."""
    def __init__(self, name, *args):
        self.ty = HOLType.COMB
        self.name = name
        self.args = args

def TFun(*args):
    """Returns the function type arg1 => arg2 => ... => argn."""
    res = args[-1]
    for arg in reversed(args[:-1]):
        res = Type("fun", arg, res)
    return res

"""Boolean type."""
hol_bool = Type("bool")
