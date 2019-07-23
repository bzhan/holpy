# Author: Bohua Zhan

from collections import OrderedDict
from copy import copy

from kernel.type import TFun, boolT

class OpenTermException(Exception):
    pass

class TermSubstitutionException(Exception):
    def __init__(self, str=""):
        self.str = str


class TypeCheckException(Exception):
    pass

class Term():
    """Represents a term in higher-order logic.
    
    There are five term constructors:

    Var(name, T): variable with given name and type.

    Const(name, T): constant with given name and type.

    Comb(f, a): the function f applied to a, written as f a (or f(a)).

    Abs(x, T, body): abstraction. x is the suggested name of the bound
    variable, and T is the type of the bound variable. body is the body of
    the abstraction. This is written as %x::T. body, where the type T is
    usually omitted.

    Bound(n): bound variable with de Bruijn index n.

    Examples:

    Var("a", nat) is a variable of type nat.

    Const("zero", nat) is constant zero.

    Comb(Const("Suc", nat => nat), Const("zero", nat)) is the successor function
    applied to zero, or the constant 1.

    Comb(Comb(Const("plus", nat => nat => nat), Var("a", nat)), Var("b", nat))
    is the term a + b.
    
    Bound variables in the lambda calculus are represented using de Bruijn
    indices, where Bound(i) represents the bound variable that is i
    abstractions away.

    Examples:
    
    Abs("x", T, P(Bound(0))) is %x::T. P x.

    Abs("x", S, Abs("y", T, Q(Bound(1), Bound(0)))) is %x::S. %y::T. Q x y.

    """
    VAR, CONST, COMB, ABS, BOUND = range(5)

    def is_var(self):
        return self.ty == Term.VAR

    def is_const(self):
        return self.ty == Term.CONST

    def is_comb(self):
        return self.ty == Term.COMB

    def is_abs(self):
        return self.ty == Term.ABS

    def is_bound(self):
        return self.ty == Term.BOUND

    def __str__(self):
        """Printing function for terms. Note we do not yet handle collision
        in lambda terms.

        """
        def helper(t, bd_vars):
            """bd_vars is the list of names of bound variables."""
            if t.is_var() or t.is_const():
                return t.name
            elif t.is_comb():
                # a b c associates to the left. So parenthesis is needed to express
                # a (b c). Parenthesis is also needed for lambda terms.
                if t.fun.is_abs():
                    str_fun = "(" + helper(t.fun, bd_vars) + ")"
                else:
                    str_fun = helper(t.fun, bd_vars)
                if t.arg.is_comb() or t.arg.is_abs():
                    str_arg = "(" + helper(t.arg, bd_vars) + ")"
                else:
                    str_arg = helper(t.arg, bd_vars)
                return str_fun + " " + str_arg
            elif t.is_abs():
                body_repr = helper(t.body, [t.var_name] + bd_vars)
                return "%" + t.var_name + ". " + body_repr
            elif t.is_bound():
                if t.n >= len(bd_vars):
                    raise OpenTermException
                else:
                    return bd_vars[t.n]
            else:
                raise TypeError()

        return helper(self, [])

    def __repr__(self):
        if self.is_var():
            return "Var(" + self.name + "," + str(self.T) + ")"
        elif self.is_const():
            return "Const(" + self.name + "," + str(self.T) + ")"
        elif self.is_comb():
            return "Comb(" + repr(self.fun) + "," + repr(self.arg) + ")"
        elif self.is_abs():
            return "Abs(" + self.var_name + "," + str(self.var_T) + "," + repr(self.body) + ")"
        elif self.is_bound():
            return "Bound " + str(self.n)
        else:
            raise TypeError()

    def __hash__(self):
        if hasattr(self, "_hash_val"):
            return self._hash_val
        if self.is_var():
            self._hash_val = hash(("VAR", self.name, hash(self.T)))
        elif self.is_const():
            self._hash_val = hash(("CONST", self.name, hash(self.T)))
        elif self.is_comb():
            self._hash_val = hash(("COMB", hash(self.fun), hash(self.arg)))
        elif self.is_abs():
            self._hash_val = hash(("ABS", hash(self.var_T), hash(self.body)))
        elif self.is_bound():
            self._hash_val = hash(("BOUND", self.n))
        else:
            raise TypeError()
        return self._hash_val

    def __eq__(self, other):
        """Equality on terms is defined by alpha-conversion. This ignores
        suggested names in lambda terms.

        """
        assert isinstance(other, Term), "cannot compare Term with %s" % str(type(other))

        if self.ty != other.ty:
            return False
        elif self.is_var() or self.is_const():
            return self.name == other.name and self.T == other.T
        elif self.is_comb():
            return self.fun == other.fun and self.arg == other.arg
        elif self.is_abs():
            # Note the suggested variable name is not important
            return self.var_T == other.var_T and self.body == other.body
        elif self.is_bound():
            return self.n == other.n
        else:
            raise TypeError()

    def __copy__(self):
        """Returns a copy of self. Types are shared, the rest of
        the information are copied.

        """
        if self.is_var():
            return Var(self.name, self.T)
        elif self.is_const():
            return Const(self.name, self.T)
        elif self.is_comb():
            return Comb(copy(self.fun), copy(self.arg))
        elif self.is_abs():
            return Abs(self.var_name, self.var_T, copy(self.body))
        elif self.is_bound():
            return Bound(self.n)
        else:
            raise TypeError()

    def __call__(self, *args):
        """Apply self (as a function) to a list of arguments."""
        res = self
        for arg in args:
            res = Comb(res, arg)
        return res

    def _get_type(self, bd_vars):
        """Helper function for get_type. bd_vars is the list of types of
        the bound variables.

        """
        if self.is_var() or self.is_const():
            return self.T
        elif self.is_comb():
            type_fun = self.fun._get_type(bd_vars)
            if type_fun.is_fun():
                return type_fun.range_type()
            else:
                raise TypeCheckException()
        elif self.is_abs():
            return TFun(self.var_T, self.body._get_type([self.var_T] + bd_vars))
        elif self.is_bound():
            if self.n >= len(bd_vars):
                raise OpenTermException()
            else:
                return bd_vars[self.n]
        else:
            raise TypeError()
    
    def get_type(self):
        """Returns type of the term with minimal type-checking."""
        return self._get_type([])

    def _is_open(self, n):
        """Helper function for is_open."""
        if self.is_var() or self.is_const():
            return False
        elif self.is_comb():
            return self.fun._is_open(n) or self.arg._is_open(n)
        elif self.is_abs():
            return self.body._is_open(n+1)
        elif self.is_bound():
            return self.n >= n
        else:
            raise TypeError()

    def is_open(self):
        """Whether t is an open term."""
        return self._is_open(0)

    def subst_type(self, tyinst):
        """Perform substitution on type variables."""
        if self.is_var():
            return Var(self.name, self.T.subst(tyinst))
        elif self.is_const():
            return Const(self.name, self.T.subst(tyinst))
        elif self.is_comb():
            return Comb(self.fun.subst_type(tyinst), self.arg.subst_type(tyinst))
        elif self.is_abs():
            return Abs(self.var_name, self.var_T.subst(tyinst), self.body.subst_type(tyinst))
        elif self.is_bound():
            return self
        else:
            raise TypeError()

    def subst_type_inplace(self, tyinst):
        """Perform substitution on type variables."""
        if hasattr(self, "_hash_val"):
            del self._hash_val
        if self.is_var():
            self.T = self.T.subst(tyinst)
        elif self.is_const():
            self.T = self.T.subst(tyinst)
        elif self.is_comb():
            self.fun.subst_type_inplace(tyinst)
            self.arg.subst_type_inplace(tyinst)
        elif self.is_abs():
            self.var_T = self.var_T.subst(tyinst)
            self.body.subst_type_inplace(tyinst)
        elif self.is_bound():
            pass
        else:
            raise TypeError()

    def subst(self, inst):
        """Perform substitution on term variables.

        Here inst must be a dictionary mapping from variable names to the
        substituted term. The type of the substituted term must match *exactly*
        the type of the variable. If substitution on types is needed, it should
        be performed before calling subst.

        """
        assert isinstance(inst, dict), "inst must be a dictionary"
        if self.is_var():
            if self.name in inst:
                t = inst[self.name]
                if t.get_type() == self.T:
                    return inst[self.name]
                else:
                    raise TermSubstitutionException("Type " + str(t.get_type()) + " != " + str(self.T))
            else:
                return self
        elif self.is_const():
            return self
        elif self.is_comb():
            return Comb(self.fun.subst(inst), self.arg.subst(inst))
        elif self.is_abs():
            return Abs(self.var_name, self.var_T, self.body.subst(inst))
        elif self.is_bound():
            return self
        else:
            raise TypeError()

    def strip_comb(self):
        """Given a term f t1 t2 ... tn, returns (f, [t1, t2, ..., tn])."""
        if self.is_comb():
            (f, args) = self.fun.strip_comb()
            return (f, args + [self.arg])
        else:
            return (self, [])

    @property
    def head(self):
        """Given a term f t1 t2 ... tn, returns f."""
        return self.strip_comb()[0]

    @property
    def args(self):
        """Given a term f t1 t2 ... tn, return the list [t1, ..., tn]."""
        return self.strip_comb()[1]

    def is_binop(self):
        """Whether self is of the form f t1 t2."""
        return len(self.args) == 2

    @property
    def arg1(self):
        """Given a term f a b, return a."""
        return self.fun.arg

    def is_implies(self):
        """Whether self is of the form A --> B."""
        implies = Const("implies", TFun(boolT, boolT, boolT))
        return self.is_binop() and self.head == implies

    @staticmethod
    def mk_implies(*args):
        """Construct the term s1 --> ... --> sn --> t."""
        implies = Const("implies", TFun(boolT, boolT, boolT))
        res = args[-1]
        for s in reversed(args[:-1]):
            res = implies(s, res)
        return res

    def strip_implies(self):
        """Given s1 --> ... --> sn --> t, return ([s1, ..., sn], t)."""
        if self.is_implies():
            rest, c = self.arg.strip_implies()
            return ([self.arg1] + rest, c)
        else:
            return ([], self)

    def is_all(self):
        """Whether self is of the form !x. P x.
        
        Note that unlike many other systems, we require the argument of
        all to be in abstraction form.
        
        """
        return self.is_comb() and self.fun.is_const() and \
            self.fun.name == "all" and self.arg.is_abs()

    def mk_all(x, body):
        """Given a variable x and a term t possibly depending on x, return
        the term !x. t. Optional arguments var_name and T specify the
        suggested name and type of the bound variable.

        """
        all_t = Const("all", TFun(TFun(x.T, boolT), boolT))
        return all_t(Term.mk_abs(x, body))

    def is_const_name(self, name):
        """Whether self is a constant with the given name."""
        return self.is_const() and self.name == name

    @staticmethod
    def equals(T):
        """Returns the equals constant for the given type."""
        return Const("equals", TFun(T, T, boolT))

    def is_equals(self):
        """Whether self is of the form A = B."""
        if self.is_binop():
            return self.head.is_const_name("equals")
        else:
            return False

    def is_reflexive(self):
        """Whether self is of the form A = A."""
        return self.is_equals() and self.arg1 == self.arg

    def is_VAR(self):
        """Whether self is of the form _VAR v."""
        return self.is_comb() and self.fun.is_const_name("_VAR") and self.arg.is_var()

    @property
    def lhs(self):
        assert self.is_equals(), "lhs: not an equality."
        return self.arg1

    @property
    def rhs(self):
        assert self.is_equals(), "rhs: not an equality."
        return self.arg

    @staticmethod
    def mk_equals(s, t):
        """Construct the term s = t."""
        eq_t = Term.equals(s.get_type())
        return eq_t(s, t)

    def _subst_bound(self, t, n):
        """Helper function for subst_bound. Here self is an open term. Replace
        Bound n by t outside any Abs. When entering into an Abs, increment n.

        """
        if self.is_var() or self.is_const():
            return self
        elif self.is_comb():
            return Comb(self.fun._subst_bound(t,n), self.arg._subst_bound(t,n))
        elif self.is_abs():
            return Abs(self.var_name, self.var_T, self.body._subst_bound(t, n+1))
        elif self.is_bound():
            if self.n == n:
                return t
            else:
                return self
        else:
            raise TypeError()

    def subst_bound(self, t):
        """Given an Abs(x,T,body), substitute x for t in the body. t should
        have type T.

        """
        if self.is_abs():
            # Perform the substitution. Note t may be a bound variable itself.
            return self.body._subst_bound(t, 0)
        else:
            raise TermSubstitutionException()

    def beta_conv(self):
        """Beta-conversion: given a term of the form (%x. t1) t2, return the
        term t1[t2/x] which is beta-equivalent.

        """
        if self.is_comb():
            return self.fun.subst_bound(self.arg)
        else:
            raise TermSubstitutionException()

    def beta_norm(self):
        """Normalize self using beta-conversion."""
        if self.is_var() or self.is_const() or self.is_bound():
            return self
        elif self.is_comb():
            f = self.fun.beta_norm()
            x = self.arg.beta_norm()
            if f.is_abs():
                return f(x).beta_conv().beta_norm()
            else:
                return f(x)
        elif self.is_abs():
            return Abs(self.var_name, self.var_T, self.body.beta_norm())
        else:
            raise TypeError()

    def occurs_var(self, t):
        """Whether the variable t occurs in self."""
        if self.is_var():
            return self == t
        elif self.is_const():
            return False
        elif self.is_comb():
            return self.fun.occurs_var(t) or self.arg.occurs_var(t)
        elif self.is_abs():
            return self.body.occurs_var(t)
        elif self.is_bound():
            return False
        else:
            raise TypeError()    

    def _abstract_over(self, t, n):
        """Helper function for abstract_over. Here self is an open term.
        t should be replaced by Bound n.

        """
        if self.is_var():
            if self.name == t.name:
                if self.T != t.T:
                    raise TermSubstitutionException()
                else:
                    return Bound(n)
            else:
                return self
        elif self.is_const():
            return self
        elif self.is_comb():
            return Comb(self.fun._abstract_over(t,n), self.arg._abstract_over(t,n))
        elif self.is_abs():
            return Abs(self.var_name, self.var_T, self.body._abstract_over(t, n+1))
        elif self.is_bound():
            return self
        else:
            raise TypeError()

    def abstract_over(self, t):
        """Abstract over the variable t. The result is ready to become
        the body of an Abs term.
        
        """
        if t.is_var():
            return self._abstract_over(t,0)
        else:
            raise TermSubstitutionException()

    @staticmethod
    def mk_abs(t, body):
        """Given body in terms of t, return the term %t. body. """
        if t.ty != Term.VAR:
            raise TermSubstitutionException()
        res = Abs(t.name, t.T, body.abstract_over(t))
        return res

    def _checked_get_type(self, bd_vars):
        """Helper function for checked_get_type. bd_vars is the list of
        types of the bound variables.

        """
        if self.is_var() or self.is_const():
            return self.T
        elif self.is_comb():
            funT = self.fun._checked_get_type(bd_vars)
            argT = self.arg._checked_get_type(bd_vars)
            if funT.is_fun() and funT.domain_type() == argT:
                return funT.range_type()
            else:
                raise TypeCheckException()
        elif self.is_abs():
            bodyT = self.body._checked_get_type([self.var_T] + bd_vars)
            return TFun(self.var_T, bodyT)
        elif self.is_bound():
            if self.n >= len(bd_vars):
                raise OpenTermException()
            else:
                return bd_vars[self.n]
        else:
            raise TypeError()

    def checked_get_type(self):
        """Perform type-checking and return the type of self."""
        return self._checked_get_type([])


class Var(Term):
    """Variable, specified by name and type."""
    def __init__(self, name, T):
        self.ty = Term.VAR
        self.name = name
        self.T = T

class Const(Term):
    """Constant, specified by name and type."""
    def __init__(self, name, T):
        self.ty = Term.CONST
        self.name = name
        self.T = T

class Comb(Term):
    """Combination."""
    def __init__(self, fun, arg):
        self.ty = Term.COMB
        self.fun = fun
        self.arg = arg

class Abs(Term):
    """Abstraction. The input to Abs is the list x1, T1, ..., xn, Tn, body.
    
    The result is %x1 : T1. ... %xn : Tn. body.
    """
    def __init__(self, *args):
        if len(args) < 3:
            raise TypeError()
        else:
            self.ty = Term.ABS
            self.var_name = args[0]
            self.var_T = args[1]
            if len(args) == 3:
                self.body = args[2]
            else:
                self.body = Abs(*args[2:])

class Bound(Term):
    """Bound variable, with de Bruijn index n."""
    def __init__(self, n):
        self.ty = Term.BOUND
        self.n = n

def get_vars(t):
    """Returns list of variables in a term or a list of terms."""
    def helper(t):
        if t.is_var():
            return [t]
        elif t.is_comb():
            return helper(t.fun) + helper(t.arg)
        elif t.is_abs():
            return helper(t.body)
        else:
            return []

    if isinstance(t, Term):
        return list(OrderedDict.fromkeys(helper(t)))
    elif isinstance(t, list):
        return list(OrderedDict.fromkeys(sum([helper(s) for s in t], [])))
    else:
        raise TypeError()

def get_consts(t):
    """Returns list of constants in a term or a list of terms."""
    def helper(t):
        if t.is_const():
            return [t]
        elif t.is_comb():
            return helper(t.fun) + helper(t.arg)
        elif t.is_abs():
            return helper(t.body)
        else:
            return []

    if isinstance(t, Term):
        return list(OrderedDict.fromkeys(helper(t)))
    elif isinstance(t, list):
        return list(OrderedDict.fromkeys(sum([helper(s) for s in t], [])))
    else:
        raise TypeError()
