# Author: Bohua Zhan

from collections import OrderedDict


class TypeMatchException(Exception):
    pass


class HOLType():
    """Represents a type in higher-order logic.
    
    Types in HOL are formed by two kinds of constructors: STVar, TVar and Type.

    STVar(name) represents a schematic type variable with the given name.
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
    # ty values for distinguishing between HOLType objects.
    STVAR, TVAR, TYPE = range(3)
    
    def is_stvar(self):
        """Return whether self is a schematic type variable."""
        return self.ty == HOLType.STVAR

    def is_tvar(self):
        """Return whether self is a type variable."""
        return self.ty == HOLType.TVAR

    def is_type(self):
        """Return whether self is given by a type constructor."""
        return self.ty == HOLType.TYPE

    def is_fun(self):
        """Whether self is of the form a => b."""
        return self.is_type() and self.name == "fun"
    
    def domain_type(self):
        """Given a type of form a => b, return a."""
        assert self.is_fun(), "domain_type"
        return self.args[0]
    
    def range_type(self):
        """Given a type of form a => b, return b."""
        assert self.is_fun(), "range_type"
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
        if self.is_stvar():
            return "'?" + self.name
        elif self.is_tvar():
            return "'" + self.name
        elif self.is_type():
            if len(self.args) == 0:
                return self.name
            elif len(self.args) == 1:
                # Insert parenthesis if the single argument is a function.
                if self.args[0].is_fun():
                    return "(%s) %s" % (self.args[0], self.name)
                else:
                    return "%s %s" % (self.args[0], self.name)
            elif self.is_fun():
                # 'a => 'b => 'c associates to the right. So parenthesis is
                # needed to express ('a => 'b) => 'c.
                if self.args[0].is_fun():
                    return "(%s) => %s" % (self.args[0], self.args[1])
                else:
                    return "%s => %s" % (self.args[0], self.args[1])
            else:
                return "(%s) %s" % (", ".join(str(t) for t in self.args), self.name)
        else:
            raise TypeError

    def __repr__(self):
        if self.is_stvar():
            return "STVar(%s)" % self.name
        if self.is_tvar():
            return "TVar(%s)" % self.name
        elif self.is_type():
            return "Type(%s, %s)" % (self.name, list(self.args))
        else:
            raise TypeError

    def __hash__(self):
        if not hasattr(self, "_hash_val"):
            if self.is_stvar():
                self._hash_val = hash(("STVAR", self.name))
            if self.is_tvar():
                self._hash_val = hash(("TVAR", self.name))
            elif self.is_type():
                self._hash_val = hash(("TYPE", self.name, tuple(hash(arg) for arg in self.args)))
        return self._hash_val
    
    def __eq__(self, other):
        if other is None:
            return False
        assert isinstance(other, HOLType), "cannot compare HOLType with %s" % str(type(other))

        if self.ty != other.ty:
            return False
        elif self.is_stvar() or self.is_tvar():
            return self.name == other.name
        elif self.is_type():
            return self.name == other.name and self.args == other.args
        else:
            raise TypeError

    def __le__(self, other):
        """Fast version of comparison."""
        if self.ty != other.ty:
            return self.ty <= other.ty
        elif self.is_stvar() or self.is_tvar():
            return self.name <= other.name
        elif self.is_type():
            return (self.name, self.args) <= (other.name, other.args)
        else:
            raise TypeError

    def __lt__(self, other):
        """Fast version of comparison."""
        if self.ty != other.ty:
            return self.ty < other.ty
        elif self.is_stvar() or self.is_tvar():
            return self.name < other.name
        elif self.is_type():
            return (self.name, self.args) < (other.name, other.args)
        else:
            raise TypeError

    def subst(self, tyinst):
        """Given a dictionary tyinst mapping from names to types,
        simultaneously substitute for the type variables using the
        dictionary.

        """
        assert isinstance(tyinst, dict), "tyinst must be a dictionary"
        if self.is_stvar():
            if self.name in tyinst:
                return tyinst[self.name]
            else:
                return self
        elif self.is_tvar():
            return self
        elif self.is_type():
            return Type(self.name, *(T.subst(tyinst) for T in self.args))
        else:
            raise TypeError

    def match_incr(self, T, tyinst):
        """Incremental match. Match self (as a pattern) with T. Here tyinst
        is the current instantiation. This is updated by the function.

        """
        if self.is_stvar():
            if self.name in tyinst:
                if T != tyinst[self.name]:
                    raise TypeMatchException
            else:
                tyinst[self.name] = T
        elif self.is_tvar():
            if self != T:
                raise TypeMatchException
        elif self.is_type():
            if (not T.is_type()) or T.name != self.name:
                raise TypeMatchException
            else:
                for arg, argT in zip(self.args, T.args):
                    arg.match_incr(argT, tyinst)
        else:
            raise TypeError

    def match(self, T):
        """Match self (as a pattern) with T. Returns either a dictionary
        containing the match, or raise TypeMatchException.

        """
        tyinst = dict()
        self.match_incr(T, tyinst)
        return tyinst

    def get_stvars(self):
        """Return the list of schematic type variables."""
        def collect(T):
            if T.is_stvar():
                return [T]
            elif T.is_tvar():
                return []
            else:
                return sum([collect(arg) for arg in T.args], [])

        return list(OrderedDict.fromkeys(collect(self)))

    def get_tvars(self):
        """Return the list of type variables."""
        def collect(T):
            if T.is_stvar():
                return []
            elif T.is_tvar():
                return [T]
            else:
                return sum([collect(arg) for arg in T.args], [])

        return list(OrderedDict.fromkeys(collect(self)))

    def get_tsubs(self):
        """Return the list of types appearing in self."""
        def collect(T):
            if T.is_stvar() or T.is_tvar():
                return [T]
            else:
                return sum([collect(arg) for arg in T.args], [T])

        return list(OrderedDict.fromkeys(collect(self)))

    def convert_stvar(self):
        if self.is_stvar():
            raise TypeMatchException("convert_stvar")
        elif self.is_tvar():
            return STVar(self.name)
        elif self.is_type():
            return Type(self.name, *(arg.convert_stvar() for arg in self.args))
        else:
            raise TypeError

class STVar(HOLType):
    """Schematic type variable."""
    def __init__(self, name):
        self.ty = HOLType.STVAR
        self.name = name

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
