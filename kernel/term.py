# Author: Bohua Zhan

from kernel.type import TFun, hol_bool

class OpenTermException(Exception):
    pass

class TermSubstitutionException(Exception):
    pass

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

    Const("0", nat) is constant zero.

    Comb(Const("Suc", nat => nat), Const("0", nat)) is the successor function
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
    (VAR, CONST, COMB, ABS, BOUND) = range(5)

    def __str__(self):
        if self.ty == Term.VAR:
            return "Var(" + self.name + "," + str(self.T) + ")"
        elif self.ty == Term.CONST:
            return "Const(" + self.name + "," + str(self.T) + ")"
        elif self.ty == Term.COMB:
            # a $ b $ c associates to the left. So parenthesis is needed to
            # express a $ (b $ c).
            if self.arg.ty == Term.COMB:
                return str(self.fun) + " $ (" + str(self.arg) + ")"
            else:
                return str(self.fun) + " $ " + str(self.arg)
        elif self.ty == Term.ABS:
            return "Abs(" + self.var_name + "," + str(self.T) + "," + str(self.body) + ")"
        elif self.ty == Term.BOUND:
            return "Bound " + str(self.n)
        else:
            raise TypeError()

    def _repr(self, bd_vars, *, print_abs_type = False):
        """Helper function for __repr__. bd_vars is the list of names of
        bound variables.

        print_abs_type: print type information for bound variables.

        """
        if self.ty == Term.VAR or self.ty == Term.CONST:
            return self.name
        elif self.ty == Term.COMB:
            # a b c associates to the left. So parenthesis is needed to express
            # a (b c). Parenthesis is also needed for lambda terms.
            if self.fun.ty == Term.ABS:
                str_fun = "(" + self.fun._repr(bd_vars) + ")"
            else:
                str_fun = self.fun._repr(bd_vars)
            if self.arg.ty == Term.COMB or self.arg.ty == Term.ABS:
                str_arg = "(" + self.arg._repr(bd_vars) + ")"
            else:
                str_arg = self.arg._repr(bd_vars)
            return str_fun + " " + str_arg
        elif self.ty == Term.ABS:
            var_str = self.var_name + "::" + repr(self.T) if print_abs_type else self.var_name
            body_repr = self.body._repr([self.var_name] + bd_vars, print_abs_type = print_abs_type)
            return "%" + var_str + ". " + body_repr
        elif self.ty == Term.BOUND:
            if self.n >= len(bd_vars):
                raise OpenTermException
            else:
                return bd_vars[self.n]
        else:
            raise TypeError()

    def __repr__(self):
        """Print the term in short form. Note we do not yet handle name
        collisions in lambda terms.

        """
        return self._repr([])

    def repr_with_abs_type(self):
        """Print the term with type information for bound variables."""
        return self._repr([], print_abs_type = True)

    def __hash__(self):
        if self.ty == Term.VAR:
            return hash(("VAR", self.name, hash(self.T)))
        elif self.ty == Term.CONST:
            return hash(("CONST", self.name, hash(self.T)))
        elif self.ty == Term.COMB:
            return hash(("COMB", hash(self.fun), hash(self.arg)))
        elif self.ty == Term.ABS:
            return hash(("ABS", hash(self.T), hash(self.body)))
        elif self.ty == Term.BOUND:
            return hash(("BOUND", self.n))
        else:
            raise TypeError()

    def __eq__(self, other):
        """Equality on terms is defined by alpha-conversion. This ignores
        suggested names in lambda terms.

        """
        if self.ty != other.ty:
            return False
        elif self.ty == Term.VAR or self.ty == Term.CONST:
            return self.name == other.name and self.T == other.T
        elif self.ty == Term.COMB:
            return self.fun == other.fun and self.arg == other.arg
        elif self.ty == Term.ABS:
            # Note the suggested variable name is not important
            return self.T == other.T and self.body == other.body
        elif self.ty == Term.BOUND:
            return self.n == other.n
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
        if self.ty == Term.VAR or self.ty == Term.CONST:
            return self.T
        elif self.ty == Term.COMB:
            type_fun = self.fun._get_type(bd_vars)
            if type_fun.is_fun():
                return type_fun.range_type()
            else:
                raise TypeCheckException()
        elif self.ty == Term.ABS:
            return TFun(self.T, self.body._get_type([self.T] + bd_vars))
        elif self.ty == Term.BOUND:
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
        if self.ty == Term.VAR or self.ty == Term.CONST:
            return False
        elif self.ty == Term.COMB:
            return self.fun._is_open(n) or self.arg._is_open(n)
        elif self.ty == Term.ABS:
            return self.body._is_open(n+1)
        elif self.ty == Term.BOUND:
            return self.n >= n
        else:
            raise TypeError()

    def is_open(self):
        """Whether t is an open term."""
        return self._is_open(0)

    def subst_type(self, tyinst):
        """Perform substitution on type variables."""
        if self.ty == Term.VAR:
            return Var(self.name, self.T.subst(tyinst))
        elif self.ty == Term.CONST:
            return Const(self.name, self.T.subst(tyinst))
        elif self.ty == Term.COMB:
            return Comb(self.fun.subst_type(tyinst), self.arg.subst_type(tyinst))
        elif self.ty == Term.ABS:
            return Abs(self.var_name, self.T.subst(tyinst), self.body.subst_type(tyinst))
        elif self.ty == Term.BOUND:
            return self
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
        if self.ty == Term.VAR:
            if self.name in inst:
                t = inst[self.name]
                if t.get_type() == self.T:
                    return inst[self.name]
                else:
                    raise TermSubstitutionException()
            else:
                return self
        elif self.ty == Term.CONST:
            return self
        elif self.ty == Term.COMB:
            return Comb(self.fun.subst(inst), self.arg.subst(inst))
        elif self.ty == Term.ABS:
            return Abs(self.var_name, self.T, self.body.subst(inst))
        elif self.ty == Term.BOUND:
            return self
        else:
            raise TypeError()

    def strip_comb(self):
        """Given a term f t1 t2 ... tn, returns (f, [t1, t2, ..., tn])."""
        if self.ty == Term.COMB:
            (f, args) = self.fun.strip_comb()
            return (f, args + [self.arg])
        else:
            return (self, [])

    def get_head(self):
        """Given a term f t1 t2 ... tn, returns f."""
        if self.ty == Term.COMB:
            return self.fun.get_head()
        else:
            return self

    def is_binop(self):
        """Whether self is of the form f t1 t2."""
        return self.ty == Term.COMB and self.fun.ty == Term.COMB

    def dest_binop(self):
        """Given a term f t1 t2, return (t1, t2)."""
        return (self.fun.arg, self.arg)

    @property
    def arg1(self):
        """Given a term f a b, return a."""
        return self.fun.arg

    def is_implies(self):
        """Whether self is of the form A --> B."""
        implies = Const("implies", TFun(hol_bool, hol_bool, hol_bool))
        return self.is_binop() and self.get_head() == implies

    @staticmethod
    def mk_implies(*args):
        """Construct the term s1 --> ... --> sn --> t."""
        implies = Const("implies", TFun(hol_bool, hol_bool, hol_bool))
        res = args[-1]
        for s in reversed(args[:-1]):
            res = implies(s, res)
        return res

    def is_all(self):
        """Whether self is of the form !x. P x.
        
        Note that unlike many other systems, we require the argument of
        all to be in abstraction form.
        
        """
        return self.ty == Term.COMB and self.fun.ty == Term.CONST and \
            self.fun.name == "all" and self.arg.ty == Term.ABS

    def mk_all(x, body, *, var_name = None, T = None):
        """Given a variable x and a term t possibly depending on x, return
        the term !x. t. Optional arguments var_name and T specify the
        suggested name and type of the bound variable.

        """
        if T is None:
            T = x.T

        all_t = Const("all", TFun(TFun(T, hol_bool), hol_bool))
        return all_t(Term.mk_abs(x, body, var_name = var_name, T = T))

    @staticmethod
    def equals(T):
        """Returns the equals constant for the given type."""
        return Const("equals", TFun(T, T, hol_bool))

    def is_equals(self):
        """Whether self is of the form A = B."""
        if self.is_binop():
            f = self.get_head()
            return f.ty == Term.CONST and f.name == "equals"
        else:
            return False

    @staticmethod
    def mk_equals(s, t):
        """Construct the term s = t."""
        eq_t = Term.equals(s.get_type())
        return eq_t(s, t)

    def _subst_bound(self, t, n):
        """Helper function for subst_bound. Here self is an open term. Replace
        Bound n by t outside any Abs. When entering into an Abs, increment n.

        """
        if self.ty == Term.VAR or self.ty == Term.CONST:
            return self
        elif self.ty == Term.COMB:
            return Comb(self.fun._subst_bound(t,n), self.arg._subst_bound(t,n))
        elif self.ty == Term.ABS:
            return Abs(self.var_name, self.T, self.body._subst_bound(t, n+1))
        elif self.ty == Term.BOUND:
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
        if self.ty == Term.ABS:
            if self.T == t.get_type():
                return self.body._subst_bound(t, 0)
            else:
                raise TermSubstitutionException()
        else:
            raise TermSubstitutionException()

    def beta_conv(self):
        """Beta-conversion: given a term of the form (%x. t1) t2, return the
        term t1[t2/x] which is beta-equivalent.

        """
        if self.ty == Term.COMB:
            return self.fun.subst_bound(self.arg)
        else:
            raise TermSubstitutionException()

    def occurs_var(self, t):
        """Whether the variable t occurs in self."""
        if self.ty == Term.VAR:
            return self == t
        elif self.ty == Term.CONST:
            return False
        elif self.ty == Term.COMB:
            return self.fun.occurs_var(t) or self.arg.occurs_var(t)
        elif self.ty == Term.ABS:
            return self.body.occurs_var(t)
        elif self.ty == Term.BOUND:
            return False
        else:
            raise TypeError()

    def _abstract_over(self, t, n):
        """Helper function for abstract_over. Here self is an open term.
        t should be replaced by Bound n.

        """
        if self.ty == Term.VAR:
            if self.name == t.name:
                if self.T != t.T:
                    raise TermSubstitutionException()
                else:
                    return Bound(n)
            else:
                return self
        elif self.ty == Term.CONST:
            return self
        elif self.ty == Term.COMB:
            return Comb(self.fun._abstract_over(t,n), self.arg._abstract_over(t,n))
        elif self.ty == Term.ABS:
            return Abs(self.var_name, self.T, self.body._abstract_over(t, n+1))
        elif self.ty == Term.BOUND:
            return self
        else:
            raise TypeError()

    def abstract_over(self, t):
        """Abstract over the variable t."""
        if t.ty == Term.VAR:
            return Abs(t.name, t.T, self._abstract_over(t,0))
        else:
            raise TermSubstitutionException()

    @staticmethod
    def mk_abs(t, body, *, var_name = None, T = None):
        """Given body in terms of t, return the term %t. body. Optional
        arguments var_name and T specify the suggested variable name and
        type of the abstraction (default to those of t).

        """
        res = body.abstract_over(t)
        if var_name is not None:
            res.var_name = var_name
        if T is not None:
            res.T = T
        return res

    def _checked_get_type(self, bd_vars):
        """Helper function for checked_get_type. bd_vars is the list of
        types of the bound variables.

        """
        if self.ty == Term.VAR or self.ty == Term.CONST:
            return self.T
        elif self.ty == Term.COMB:
            funT = self.fun._checked_get_type(bd_vars)
            argT = self.arg._checked_get_type(bd_vars)
            if funT.is_fun() and funT.domain_type() == argT:
                return funT.range_type()
            else:
                raise TypeCheckException()
        elif self.ty == Term.ABS:
            bodyT = self.body._checked_get_type([self.T] + bd_vars)
            return TFun(self.T, bodyT)
        elif self.ty == Term.BOUND:
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
            self.T = args[1]
            if len(args) == 3:
                self.body = args[2]
            else:
                self.body = Abs(*args[2:])

class Bound(Term):
    """Bound variable, with de Bruijn index n."""
    def __init__(self, n):
        self.ty = Term.BOUND
        self.n = n
