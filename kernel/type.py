# Author: Bohua Zhan

from collections import UserDict

from logic import term_ord
from util import typecheck


class TypeException(Exception):
    """Indicates error in processing types."""
    def __init__(self, msg):
        self.msg = msg

    def __str__(self):
        return self.msg


class TypeMatchException(Exception):
    """Indicates error when matching types."""
    def __init__(self, msg):
        self.msg = msg

    def __str__(self):
        return self.msg


class TyInst(UserDict):
    """Instantiation of schematic type variables."""
    def __str__(self):
        return ', '.join("'%s := %s" % (nm, T) for nm, T in self.items())

    def __copy__(self):
        return TyInst(self)


"""Default parser for types. If None, Type() is unable to parse type."""
type_parser = None

"""Default printer for types. If None, Type.print_basic is used."""
type_printer = None


class Type():
    """Represents a type in higher-order logic.
    
    Types in HOL are formed by two kinds of constructors: STVar, TVar and TConst.

    STVar(name) represents a schematic type variable with the given name.
    TVar(name) represents a type variable with the given name. TConst(f, args)
    represents a type constant applied to a list of arguments.
    
    There are two fundamental type constants:
    
    - booleans, with name "bool" and no arguments.
    
    - functions, with name "fun" and two arguments: the domain and codomain
    types. TConst("fun", a, b) is printed as a => b. The => sign associates to
    the right.
    
    Further defined type constants include:
    
    - natural numbers, with name "nat" and no arguments.
    
    - lists, with name "list" and one argument.

    - product, with name "prod" and two arguments. TConst("prod", a, b) is
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
    # ty values for distinguishing between Type objects.
    STVAR, TVAR, TCONST = range(3)

    def __init__(self, arg):
        if not isinstance(arg, Type):
            if type_parser is not None:
                T = type_parser(arg)
            else:
                raise TypeException('Type: parser not found.')
        else:
            T = arg

        # Now copy the content of T onto self
        self.__dict__.update(T.__dict__)

    def is_stvar(self):
        """Return whether self is a schematic type variable."""
        return self.ty == Type.STVAR

    def is_tvar(self):
        """Return whether self is a type variable."""
        return self.ty == Type.TVAR

    def is_tconst(self):
        """Return whether self is given by a type constructor."""
        return self.ty == Type.TCONST

    def is_fun(self):
        """Whether self is of the form a => b."""
        return self.is_tconst() and self.name == "fun"
    
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
        
    def print_basic(self):
        """Basic printing function for types."""
        if self.is_stvar():
            return "?'" + self.name
        elif self.is_tvar():
            return "'" + self.name
        elif self.is_tconst():
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

    def __str__(self):
        if type_printer is None:
            return self.print_basic()
        else:
            return type_printer(self)

    def __repr__(self):
        if self.is_stvar():
            return "STVar(%s)" % self.name
        if self.is_tvar():
            return "TVar(%s)" % self.name
        elif self.is_tconst():
            return "TConst(%s, %s)" % (self.name, list(self.args))
        else:
            raise TypeError

    def __hash__(self):
        if not hasattr(self, "_hash_val"):
            if self.is_stvar():
                self._hash_val = hash(("STVAR", self.name))
            if self.is_tvar():
                self._hash_val = hash(("TVAR", self.name))
            elif self.is_tconst():
                self._hash_val = hash(("TCONST", self.name, tuple(hash(arg) for arg in self.args)))
        return self._hash_val
    
    def __eq__(self, other):
        if other is None:
            return False
        assert isinstance(other, Type), "cannot compare Type with %s" % str(type(other))

        if id(self) == id(other):
            return True

        if self.ty != other.ty:
            return False
        elif self.is_stvar() or self.is_tvar():
            return self.name == other.name
        elif self.is_tconst():
            return self.name == other.name and self.args == other.args
        else:
            raise TypeError

    def __le__(self, other):
        """Fast version of comparison."""
        if self.ty != other.ty:
            return self.ty <= other.ty
        elif self.is_stvar() or self.is_tvar():
            return self.name <= other.name
        elif self.is_tconst():
            return (self.name, self.args) <= (other.name, other.args)
        else:
            raise TypeError

    def __lt__(self, other):
        """Fast version of comparison."""
        if self.ty != other.ty:
            return self.ty < other.ty
        elif self.is_stvar() or self.is_tvar():
            return self.name < other.name
        elif self.is_tconst():
            return (self.name, self.args) < (other.name, other.args)
        else:
            raise TypeError

    def size(self):
        """Return the size of the type."""
        if self.is_stvar() or self.is_tvar():
            return 1
        elif self.is_tconst():
            return 1 + sum(T.size() for T in self.args)
        else:
            raise TypeError

    def subst(self, tyinst=None, **kwargs):
        """Simultaneously substitute for the type variables using tyinst.
        
        Parameters
        ==========
        tyinst : TyInst
            Type instantiation to be substituted.

        """
        if tyinst is None:
            tyinst = TyInst(**kwargs)
        if self.is_stvar():
            if self.name in tyinst:
                return tyinst[self.name]
            else:
                return self
        elif self.is_tvar():
            return self
        elif self.is_tconst():
            return TConst(self.name, *(T.subst(tyinst) for T in self.args))
        else:
            raise TypeError

    def match_incr(self, T, tyinst):
        """Incremental type matching of self with T.
        
        Parameters
        ==========
        tyinst : TyInst
            The current instantiation. This is updated by the function.

        """
        if self.is_stvar():
            if self.name in tyinst:
                if T != tyinst[self.name]:
                    raise TypeMatchException('Unable to match %s with %s' % (T, tyinst[self.name]))
            else:
                tyinst[self.name] = T
        elif self.is_tvar():
            if self != T:
                raise TypeMatchException('Unable to match %s with %s' % (self, T))
        elif self.is_tconst():
            if (not T.is_tconst()) or T.name != self.name:
                raise TypeMatchException('Unable to match %s with %s' % (self, T))
            else:
                for arg, argT in zip(self.args, T.args):
                    arg.match_incr(argT, tyinst)
        else:
            raise TypeError

    def match(self, T):
        """Type matching of self with T.
        
        Return the resulting instantiation, or raise TypeMatchException
        if matching fails.

        """
        tyinst = TyInst()
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

        return term_ord.sorted_typs(collect(self))

    def get_tvars(self):
        """Return the list of type variables."""
        def collect(T):
            if T.is_stvar():
                return []
            elif T.is_tvar():
                return [T]
            else:
                return sum([collect(arg) for arg in T.args], [])

        return term_ord.sorted_typs(collect(self))

    def get_tsubs(self):
        """Return the list of types appearing in self."""
        def collect(T):
            if T.is_stvar() or T.is_tvar():
                return [T]
            else:
                return sum([collect(arg) for arg in T.args], [T])

        return term_ord.sorted_typs(collect(self))

    def convert_stvar(self):
        if self.is_stvar():
            raise TypeException("convert_stvar")
        elif self.is_tvar():
            return STVar(self.name)
        elif self.is_tconst():
            return TConst(self.name, *(arg.convert_stvar() for arg in self.args))
        else:
            raise TypeError

    def is_numeral_type(self):
        return self in (NatType, IntType, RealType)


class STVar(Type):
    """Schematic type variable."""
    def __init__(self, name):
        self.ty = Type.STVAR
        self.name = name

class TVar(Type):
    """Type variable."""
    def __init__(self, name):
        self.ty = Type.TVAR
        self.name = name

class TConst(Type):
    """Type constant, applied to a list of arguments."""
    def __init__(self, name, *args):
        self.ty = Type.TCONST
        self.name = name
        self.args = args

def TFun(*args):
    """Returns the function type arg1 => arg2 => ... => argn."""
    typecheck.checkinstance('TFun', args, [Type])
    res = args[-1]
    for arg in reversed(args[:-1]):
        res = TConst("fun", arg, res)
    return res


# Boolean type
BoolType = TConst("bool")

# Numeral types
NatType = TConst('nat')
IntType = TConst('int')
RealType = TConst('real')
