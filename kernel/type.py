# Author: Bohua Zhan

from collections import OrderedDict

class TypeMatchException(Exception):
    pass

class HOLType():
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
    (TVAR, TYPE) = range(2)

    def is_fun(self):
        """Whether self is of the form a => b."""
        return self.ty == HOLType.TYPE and self.name == "fun"
    
    def domain_type(self):
        """Given a type of form a => b, return a."""
        assert(self.is_fun())
        return self.args[0]
    
    def range_type(self):
        """Given a type of form a => b, return b."""
        assert(self.is_fun())
        return self.args[1]

    def strip_type(self):
        """Given a type of form a_1 => ... => a_n, b, return the pair
        [a_1, ... a_n], b.
        
        """
        if self.is_fun():
            domains, range = self.range_type().strip_type()
            return ([self.domain_type()] + domains, range)
        else:
            return ([], self)
        
    def __str__(self):
        if self.ty == HOLType.TVAR:
            return "'" + self.name
        elif self.ty == HOLType.TYPE:
            if len(self.args) == 0:
                return self.name
            elif len(self.args) == 1:
                # Insert parenthesis if the single argument is a function.
                if HOLType.is_fun(self.args[0]):
                    return "(" + str(self.args[0]) + ") " + self.name
                else:
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
        if self.ty == HOLType.TVAR:
            return "TVar(" + self.name + ")"
        elif self.ty == HOLType.TYPE:
            return "Type(" + self.name + ", " + str(list(self.args)) + ")"
        else:
            raise TypeError()

    def __hash__(self):
        if hasattr(self, "_hash_val"):
            return self._hash_val
        if self.ty == HOLType.TVAR:
            self._hash_val = hash(("VAR", self.name))
        elif self.ty == HOLType.TYPE:
            self._hash_val = hash(("COMB", self.name, tuple(hash(arg) for arg in self.args)))
        return self._hash_val
    
    def __eq__(self, other):
        if not isinstance(other, HOLType):
            return False
        if self.ty != other.ty:
            return False
        elif self.ty == HOLType.TVAR:
            return self.name == other.name
        elif self.ty == HOLType.TYPE:
            return self.name == other.name and self.args == other.args
        else:
            raise TypeError()

    def subst(self, tyinst):
        """Given a dictionary tyinst mapping from names to types,
        simultaneously substitute for the type variables using the
        dictionary.

        """
        assert isinstance(tyinst, dict), "tyinst must be a dictionary"
        if self.ty == HOLType.TVAR:
            if self.name in tyinst:
                return tyinst[self.name]
            else:
                return self
        elif self.ty == HOLType.TYPE:
            return Type(self.name, *(T.subst(tyinst) for T in self.args))
        else:
            raise TypeError()

    def match_incr(self, T, tyinst, internal_only=False):
        """Incremental match. Match self (as a pattern) with T. Here tyinst
        is the current instantiation. This is updated by the function.

        """
        if self.ty == HOLType.TVAR:
            if internal_only and not self.name.startswith('_'):
                if self != T:
                    raise TypeMatchException()
            elif self.name in tyinst:
                if T != tyinst[self.name]:
                    raise TypeMatchException()
            else:
                tyinst[self.name] = T
        elif self.ty == HOLType.TYPE:
            if T.ty != HOLType.TYPE or T.name != self.name:
                raise TypeMatchException()
            else:
                for arg, argT in zip(self.args, T.args):
                    arg.match_incr(argT, tyinst, internal_only=internal_only)
        else:
            raise TypeError()

    def match(self, T, internal_only=False):
        """Match self (as a pattern) with T. Returns either a dictionary
        containing the match, or raise TypeMatchException.

        """
        tyinst = dict()
        self.match_incr(T, tyinst, internal_only=internal_only)
        return tyinst

    def get_tvars(self):
        """Return the list of type variables."""
        def collect(T):
            if T.ty == HOLType.TVAR:
                return [T]
            else:
                return sum([collect(arg) for arg in T.args], [])

        return list(OrderedDict.fromkeys(collect(self)))

    def get_tsubs(self):
        """Return the list of types appearing in self."""
        def collect(T):
            if T.ty == HOLType.TVAR:
                return [T]
            else:
                return sum([collect(arg) for arg in T.args], [T])

        return list(OrderedDict.fromkeys(collect(self)))

class TVar(HOLType):
    """Type variable."""
    def __init__(self, name):
        self.ty = HOLType.TVAR
        self.name = name

class Type(HOLType):
    """Type constant, applied to a list of arguments."""
    def __init__(self, name, *args):
        self.ty = HOLType.TYPE
        self.name = name
        self.args = args

def TFun(*args):
    """Returns the function type arg1 => arg2 => ... => argn."""

    if isinstance(args[0], list):
        args = tuple(args[0])
    assert all(isinstance(arg, HOLType) for arg in args), \
           "TFun: each argument of TFun must be a type."
    res = args[-1]
    for arg in reversed(args[:-1]):
        res = Type("fun", arg, res)
    return res

"""Boolean type."""
boolT = Type("bool")
