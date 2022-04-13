# Author: Bohua Zhan

from collections import UserDict
from copy import copy
import math
from fractions import Fraction

from kernel.type import Type, TFun, BoolType, NatType, IntType, RealType, TyInst, TypeMatchException
from kernel import term_ord
from util import typecheck
from util import name


class TermException(Exception):
    """Indicates error in processing terms."""
    def __init__(self, msg):
        self.msg = msg

    def __str__(self):
        return self.msg

class TypeCheckException(Exception):
    """Indicates error in type checking of terms."""
    def __init__(self, msg):
        self.msg = msg

    def __str__(self):
        return self.msg

class Inst(UserDict):
    """Instantiation of schematic variables."""
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.tyinst = TyInst()

    def __str__(self):
        res = ''
        if self.tyinst:
            res = str(self.tyinst) + ', '
        res += ', '.join('%s := %s' % (nm, t) for nm, t in self.items())
        return res

    def __copy__(self):
        res = Inst(self)
        res.tyinst = copy(self.tyinst)
        return res

    def __bool__(self):
        return bool(self.tyinst) or bool(self.keys())


"""Default parser for terms. If None, Term() is unable to parse string."""
term_parser = None

"""Default printer for terms. If None, Term.print_basic is used."""
term_printer = None


class Term():
    """Represents a term in higher-order logic.
    
    There are six term constructors:
    
    SVar(name, T): schematic variable with given name and type.

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
    # ty values for distinguishing between Term objects.
    SVAR, VAR, CONST, COMB, ABS, BOUND = range(6)

    def __init__(self, arg):
        if not isinstance(arg, Term):
            if term_parser is not None:
                t = term_parser(arg)
            else:
                raise TermException('Term: parser not found.')
        else:
            t = arg
        
        # Now copy the content of t onto self
        self.__dict__.update(t.__dict__)

    def is_svar(self):
        return self.ty == Term.SVAR

    def is_var(self):
        """Return whether the term is a variable."""
        return self.ty == Term.VAR

    def is_const(self, name=None):
        """Return whether the term is a constant.

        name : optional str
            If given, test whether the term has that name.

        """
        if self.ty != Term.CONST:
            return False
        else:
            return name is None or self.name == name

    def is_comb(self, name=None, nargs=None):
        """Return whether the term is a combination.

        name : optional str
            If given, test whether the head of the term has that name.

        nargs : optional int
            Must be given together with name. If given, test whether the
            head is applied to exactly that many arguments.

        """
        if self.ty != Term.COMB:
            return False
        elif name is not None:
            return self.head.is_const(name) and (nargs is None or len(self.args) == nargs)
        else:
            return True

    def is_abs(self):
        """Return whether the term is an abstraction."""
        return self.ty == Term.ABS

    def is_bound(self):
        """Return whether the term is a bound variable."""
        return self.ty == Term.BOUND

    def print_basic(self):
        """Basic printing function for terms. Note we do not yet handle collision
        in lambda terms.

        """
        def helper(t, bd_vars):
            """bd_vars is the list of names of bound variables."""
            if t.is_svar():
                return "?" + t.name
            elif t.is_var() or t.is_const():
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
                    return ":B" + str(t.n)
                else:
                    return bd_vars[t.n]
            else:
                raise TypeError

        return helper(self, [])

    def __str__(self):
        if term_printer is None:
            return self.print_basic()
        else:
            return term_printer(self)

    def __repr__(self):
        if self.is_svar():
            return "SVar(%s, %s)" % (self.name, self.T)
        elif self.is_var():
            return "Var(%s, %s)" % (self.name, self.T)
        elif self.is_const():
            return "Const(%s, %s)" % (self.name, self.T)
        elif self.is_comb():
            return "Comb(%s, %s)" % (repr(self.fun), repr(self.arg))
        elif self.is_abs():
            return "Abs(%s, %s, %s)" % (self.var_name, self.var_T, repr(self.body))
        elif self.is_bound():
            return "Bound(%s)" % self.n
        else:
            raise TypeError

    def __hash__(self):
        if not hasattr(self, "_hash_val"):
            if self.is_svar():
                self._hash_val = hash(("SVAR", self.name, hash(self.T)))
            elif self.is_var():
                self._hash_val = hash(("VAR", self.name, hash(self.T)))
            elif self.is_const():
                self._hash_val = hash(("CONST", self.name, hash(self.T)))
            elif self.is_comb():
                self._hash_val = hash(("COMB", hash(self.fun), hash(self.arg)))
            elif self.is_abs():
                self._hash_val = hash(("ABS", hash(self.var_name), hash(self.var_T), hash(self.body)))
            elif self.is_bound():
                self._hash_val = hash(("BOUND", self.n))
            else:
                raise TypeError
        return self._hash_val

    def __eq__(self, other):
        """Equality on terms is defined by alpha-conversion. This ignores
        suggested names in lambda terms.

        """
        assert isinstance(other, Term), "cannot compare Term with %s" % str(type(other))

        if id(self) == id(other):
            return True

        if self.ty != other.ty:
            return False
        elif self.is_svar() or self.is_var() or self.is_const():
            return self.name == other.name and self.T == other.T
        elif self.is_comb():
            return self.fun == other.fun and self.arg == other.arg
        elif self.is_abs():
            # Note the suggested variable name is not important
            return self.var_T == other.var_T and self.body == other.body
        elif self.is_bound():
            return self.n == other.n
        else:
            raise TypeError

    def __copy__(self):
        """Returns a copy of self. Types are shared, the rest of
        the information are copied.

        """
        if self.is_svar():
            return SVar(self.name, self.T)
        elif self.is_var():
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
            raise TypeError

    def __call__(self, *args):
        """Apply self (as a function) to a list of arguments."""
        res = self
        for arg in args:
            res = Comb(res, arg)
        return res

    def size(self):
        """Return the size of the term."""
        if self.is_svar() or self.is_var() or self.is_const():
            return 1
        elif self.is_comb():
            return 1 + self.fun.size() + self.arg.size()
        elif self.is_abs():
            return 1 + self.body.size()
        elif self.is_bound():
            return 1
        else:
            raise TypeError
    
    def get_type(self):
        """Returns type of the term with minimal type checking."""
        def rec(t, bd_vars):
            """Helper function. bd_vars is the list of types of the bound variables."""
            if t.is_svar() or t.is_var() or t.is_const():
                return t.T
            elif t.is_comb():
                type_fun = rec(t.fun, bd_vars)
                if type_fun.is_fun():
                    return type_fun.range_type()
                else:
                    raise TypeCheckException('function type expected in application')
            elif t.is_abs():
                return TFun(t.var_T, rec(t.body, [t.var_T] + bd_vars))
            elif t.is_bound():
                if t.n >= len(bd_vars):
                    raise TypeCheckException("open term")
                else:
                    return bd_vars[t.n]
            else:
                raise TypeError

        return rec(self, [])

    def is_open(self):
        """Whether t is an open term."""
        def rec(t, n):
            if t.is_svar() or t.is_var() or t.is_const():
                return False
            elif t.is_comb():
                return rec(t.fun, n) or rec(t.arg, n)
            elif t.is_abs():
                return rec(t.body, n+1)
            elif t.is_bound():
                return t.n >= n
            else:
                raise TypeError
        return rec(self, 0)

    def subst_type(self, tyinst=None, **kwargs):
        """Perform substitution on type variables.
        
        Parameters
        ==========
        tyinst : TyInst
            Type instantiation to be substituted.

        """
        if tyinst is None:
            tyinst = TyInst(**kwargs)
        if self.is_svar():
            return SVar(self.name, self.T.subst(tyinst))
        elif self.is_var():
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
            raise TypeError

    def subst_type_inplace(self, tyinst):
        """Perform substitution on type variables."""
        typecheck.checkinstance('subst_type_inplace', tyinst, TyInst)
        if hasattr(self, "_hash_val"):
            del self._hash_val
        if self.is_svar() or self.is_var() or self.is_const():
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
            raise TypeError

    def subst(self, inst=None, **kwargs):
        """Perform substitution on term variables.

        Parameters
        ==========
        inst : Inst
            Instantiation to be substituted.

        """
        if inst is None:
            inst = Inst(**kwargs)

        # First match type variables.
        svars = get_svars(self)
        for v in svars:
            if v.name in inst:
                try:
                    inst_T = inst[v.name].get_type()
                    v.T.match_incr(inst_T, inst.tyinst)
                except TypeMatchException:
                    raise TermException("subst: type " + str(v.T) + " cannot match " + str(inst_T))

        # Now apply substitution recursively.
        def rec(t):
            if t.is_svar():
                if t.name in inst:
                    return inst[t.name]
                else:
                    return t
            elif t.is_var() or t.is_const():
                return t
            elif t.is_comb():
                return Comb(rec(t.fun), rec(t.arg))
            elif t.is_abs() and t.body.is_comb() and t.body.fun.is_svar() and \
                t.body.fun.name in inst and t.body.arg == Bound(0) and inst[t.body.fun.name].is_abs():
                return inst[t.body.fun.name]
            elif t.is_abs():
                return Abs(t.var_name, t.var_T, rec(t.body))
            elif t.is_bound():
                return t
            else:
                raise TypeError

        return rec(self.subst_type(inst.tyinst))

    def strip_comb(self):
        """Given a term f t1 t2 ... tn, returns (f, [t1, t2, ..., tn])."""
        t = self
        args = []
        while t.is_comb():
            args.append(t.arg)
            t = t.fun
        return (t, list(reversed(args)))

    @property
    def head(self):
        """Given a term f t1 t2 ... tn, returns f."""
        t = self
        while t.is_comb():
            t = t.fun
        return t

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

    def is_not(self):
        """Whether self is of form ~A."""
        return self.is_comb('neg', 1)

    def is_implies(self):
        """Whether self is of the form A --> B."""
        return self.is_comb('implies', 2)

    def strip_implies(self):
        """Given s1 --> ... --> sn --> t, return ([s1, ..., sn], t)."""
        if self.is_implies():
            rest, c = self.arg.strip_implies()
            return ([self.arg1] + rest, c)
        else:
            return ([], self)

    def is_conj(self):
        """Whether t is of the form A & B."""
        return self.is_comb('conj', 2)

    def strip_conj(self):
        """Given s1 & ... & sn, return [s1, ..., sn]."""
        if self.is_conj():
            return [self.arg1] + self.arg.strip_conj()
        else:
            return [self]

    def is_disj(self):
        """Whether t is of the form A | B."""
        return self.is_comb('disj', 2)

    def strip_disj(self):
        """Given s1 | ... | sn, return [s1, ..., sn]."""
        if self.is_disj():
            return [self.arg1] + self.arg.strip_disj()
        else:
            return [self]

    def is_forall(self):
        """Whether self is of the form !x. P x."""
        return self.is_comb('all', 1)

    def is_exists(self):
        """Whether self is of the form ?x. P x."""
        return self.is_comb('exists', 1)

    def is_equals(self):
        """Whether self is of the form A = B."""
        return self.is_comb('equals', 2)

    def is_compares(self):
        """Whether self is of the form A <(=) B or A >(=) B"""
        return self.is_less() or self.is_less_eq() or self.is_greater() or self.is_greater_eq()

    def is_reflexive(self):
        """Whether self is of the form A = A."""
        return self.is_equals() and self.arg1 == self.arg

    def is_VAR(self):
        """Whether self is of the form _VAR v."""
        return self.is_comb('_VAR', 1) and self.arg.is_var()

    @property
    def lhs(self):
        assert self.is_equals(), "lhs: not an equality."
        return self.arg1

    @property
    def rhs(self):
        assert self.is_equals(), "rhs: not an equality."
        return self.arg

    def incr_boundvars(self, inc):
        """Increase loose bound variables in self by inc."""
        def rec(t, lev):
            if t.is_svar() or t.is_var() or t.is_const():
                return t
            elif t.is_comb():
                return Comb(rec(t.fun, lev), rec(t.arg, lev))
            elif t.is_abs():
                return Abs(t.var_name, t.var_T, rec(t.body, lev+1))
            elif t.is_bound():
                if t.n >= lev:
                    return Bound(t.n + inc)
                else:
                    return t
            else:
                raise TypeError

        return rec(self, 0)

    def subst_bound(self, t):
        """Given an Abs(x,T,body), substitute x for t in the body. t should
        have type T.

        """

        def rec(s, n):
            if s.is_svar() or s.is_var() or s.is_const():
                return s
            elif s.is_comb():
                return Comb(rec(s.fun, n), rec(s.arg, n))
            elif s.is_abs():
                return Abs(s.var_name, s.var_T, rec(s.body, n+1))
            elif s.is_bound():
                if s.n == n:
                    return t.incr_boundvars(n)
                elif s.n > n:  # Bound outside
                    return Bound(s.n - 1)
                else:  # Locally bound
                    return s
            else:
                raise TypeError

        if self.is_abs():
            # Perform the substitution. Note t may be a bound variable itself.
            return rec(self.body, 0)
        else:
            raise TermException("subst_bound: input is not an abstraction.")

    def beta_conv(self):
        """Beta-conversion: given a term of the form (%x. t1) t2, return the
        term t1[t2/x] which is beta-equivalent.

        """
        if self.is_comb() and self.fun.is_abs():
            return self.fun.subst_bound(self.arg)
        else:
            raise TermException("beta_conv: input is not in the form (%x. t1) t2.")

    def beta_norm(self):
        """Normalize self using beta-conversion."""
        if self.is_svar() or self.is_var() or self.is_const() or self.is_bound():
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
            raise TypeError

    def subst_norm(self, inst=None, **kwargs):
        """Substitute using the given instantiation, then normalize with
        respect to beta-conversion.

        """
        if inst is None:
            inst = Inst(**kwargs)
        return self.subst(inst).beta_norm()

    def occurs_var(self, t):
        """Whether the variable t occurs in self."""
        if self.is_svar():
            return False
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
            raise TypeError    

    def abstract_over(self, t):
        """Abstract over the variable t. The result is ready to become
        the body of an Abs term.
        
        """
        def rec(s, n):
            if s.is_svar():
                if t.is_svar() and s.name == t.name:
                    if s.T != t.T:
                        raise TermException("abstract_over: wrong type.")
                    else:
                        return Bound(n)
                else:
                    return s
            elif s.is_var():
                if t.is_var() and s.name == t.name:
                    if s.T != t.T:
                        raise TermException("abstract_over: wrong type.")
                    else:
                        return Bound(n)
                else:
                    return s
            elif s.is_const():
                return s
            elif s.is_comb():
                return Comb(rec(s.fun, n), rec(s.arg, n))
            elif s.is_abs():
                return Abs(s.var_name, s.var_T, rec(s.body, n+1))
            elif s.is_bound():
                return s
            else:
                raise TypeError

        if t.is_var() or t.is_svar():
            return rec(self, 0)
        else:
            raise TermException("abstract_over: t is not a variable.")

    def checked_get_type(self):
        """Perform type-checking and return the type of self."""
        def rec(t, bd_vars):
            if t.is_svar() or t.is_var() or t.is_const():
                return t.T
            elif t.is_comb():
                funT = rec(t.fun, bd_vars)
                argT = rec(t.arg, bd_vars)
                if not funT.is_fun():
                    raise TypeCheckException('function type expected in application')
                elif funT.domain_type() != argT:
                    raise TypeCheckException(
                        'type mismatch in application. Expected %s. Got %s' % (funT.domain_type(), argT))
                else:
                    return funT.range_type()
            elif t.is_abs():
                bodyT = rec(t.body, [t.var_T] + bd_vars)
                return TFun(t.var_T, bodyT)
            elif t.is_bound():
                if t.n >= len(bd_vars):
                    raise TypeCheckException("open term")
                else:
                    return bd_vars[t.n]
            else:
                raise TypeError
        return rec(self, [])

    def convert_svar(self):
        if self.is_svar():
            raise TermException("convert_svar: term already contains SVar.")
        elif self.is_var():
            return SVar(self.name, self.T.convert_stvar())
        elif self.is_const():
            return Const(self.name, self.T.convert_stvar())
        elif self.is_comb():
            return self.fun.convert_svar()(self.arg.convert_svar())
        elif self.is_abs():
            return Abs(self.var_name, self.var_T.convert_stvar(), self.body.convert_svar())
        elif self.is_bound():
            return self
        else:
            raise TypeError

    def dest_abs(self, var_name=None):
        """Given self of form %x. body, return pair (x, body).

        If var_name is None, the name recorded in the abstraction is used
        as the suggested name. Otherwise var_name is used as suggested name.

        It is guaranteed that v does not repeat names with any variables
        in the body.

        """
        assert self.is_abs(), 'dest_abs'
        var_names = [v.name for v in self.body.get_vars()]
        if var_name is None:
            var_name = self.var_name
        nm = name.get_variant_name(var_name, var_names)
        v = Var(nm, self.var_T)
        body = self.subst_bound(v)

        return v, body

    def is_binary(self):
        """Whether self is in standard binary form.
        
        Note binary form means no of_nat is applied.
    
        """
        if self.is_const("zero") or self.is_const("one"):
            return True
        elif self.is_comb('bit0', 1) or self.is_comb('bit1', 1):
            return self.arg.is_binary()
        else:
            return False

    def dest_binary(self):
        """Convert HOL binary form to Python integer.
        
        Note binary form means no of_nat is applied.

        """
        if self.is_const("zero"):
            return 0
        elif self.is_const("one"):
            return 1
        elif self.is_comb('bit0', 1):
            return 2 * self.arg.dest_binary()
        elif self.is_comb('bit1', 1):
            return 2 * self.arg.dest_binary() + 1
        else:
            raise TermException('dest_binary: term is not in binary form.')

    def is_nat(self):
        return self.get_type() == NatType

    def is_int(self):
        return self.get_type() == IntType

    def is_real(self):
        return self.get_type() == RealType

    def is_zero(self):
        return self.is_const('zero')

    def is_one(self):
        return self.is_const('one')

    def is_plus(self):
        return self.is_comb('plus', 2)

    def is_minus(self):
        return self.is_comb('minus', 2)

    def is_uminus(self):
        return self.is_comb('uminus', 1)

    def is_times(self):
        return self.is_comb('times', 2)

    def is_divides(self):
        return self.is_comb('real_divide', 2)

    def is_real_inverse(self):
        return self.is_comb("real_inverse", 1) and self.arg.get_type() == RealType

    def is_nat_power(self):
        return self.is_comb('power', 2) and self.arg.get_type() == NatType

    def is_real_power(self):
        return self.is_comb('power', 2) and self.arg.get_type() == RealType

    def is_nat_number(self):
        """Whether self represents a nonnegative integer (of any type)."""
        return self.is_zero() or self.is_one() or (self.is_comb('of_nat', 1) and self.arg.is_binary())

    def is_frac_number(self):
        """Whether self represents a nonnegative fraction (of any type).

        Note we check that the fraction in normal form: the denominator
        is not 1, and the numerator and denominator have gcd 1.

        """
        if self.is_divides():
            if not (self.arg1.is_nat_number() and self.arg.is_nat_number()):
                return False

            m, n = self.arg1.dest_number(), self.arg.dest_number()
            return n != 1 and math.gcd(m, n) == 1
        else:
            return self.is_nat_number()

    def is_number(self):
        """Whether self represents a number.
        
        Note we check that the number is in normal form. If the number
        is nonnegative, it is a natural number or fraction in normal form.
        Otherwise, it is in the form -x where x > 0.

        """
        if self.is_zero():
            return True
        if self.is_one():
            return True

        if self.is_uminus():
            return self.arg.is_frac_number() and not self.arg.is_zero()
        else:
            return self.is_frac_number()

    def is_constant(self):
        """Whether self represents a constant.
        
        Note the constant could be in arbitrary form.
        """
        if self.is_number():
            return True
        elif self.is_uminus():
            return self.arg.is_constant()
        elif self.head.name in ("plus", "minus", "times", "real_divide", "power"):
            return self.arg1.is_constant() and self.arg.is_constant()
        else:
            return False

    def dest_number(self):
        """Convert a term to a Python number."""
        if self.is_zero():
            return 0
        if self.is_one():
            return 1

        if self.is_uminus():
            return -self.arg.dest_number()
        if self.is_divides():
            num, denom = self.arg1.dest_number(), self.arg.dest_number()
            if denom == 0:
                return 0  # n / 0 = 0 in the HOL library
            elif denom == 1:
                return num
            else:
                return Fraction(num) / denom

        if not (self.is_comb('of_nat', 1) and self.arg.is_binary()):
            raise TermException('dest_number: term %s is not a number.' % self)
        return self.arg.dest_binary()

    def __add__(self, other):
        T = self.get_type()
        if isinstance(other, (int, Fraction)):
            other = Number(T, other)
        if not isinstance(other, Term):
            return NotImplemented
        return plus(T)(self, other)

    def __radd__(self, other):
        T = self.get_type()
        if isinstance(other, (int, Fraction)):
            other = Number(T, other)
        return plus(T)(other, self)

    def __sub__(self, other):
        T = self.get_type()
        if isinstance(other, (int, Fraction)):
            other = Number(T, other)
        return minus(T)(self, other)

    def __rsub__(self, other):
        T = self.get_type()
        if isinstance(other, (int, Fraction)):
            other = Number(T, other)
        return minus(T)(other, self)

    def __mul__(self, other):
        T = self.get_type()
        if isinstance(other, (int, Fraction)):
            other = Number(T, other)
        return times(T)(self, other)

    def __rmul__(self, other):
        T = self.get_type()
        if isinstance(other, (int, Fraction)):
            other = Number(T, other)
        return times(T)(other, self)

    def __truediv__(self, other):
        T = self.get_type()
        if isinstance(other, (int, Fraction)):
            other = Number(T, other)
        return divides(T)(self, other)

    def __rtruediv__(self, other):
        T = self.get_type()
        if isinstance(other, (int, Fraction)):
            other = Number(T, other)
        return divides(T)(other, self)

    def __neg__(self):
        T = self.get_type()
        return uminus(T)(self)

    def __pos__(self):
        return self

    def __pow__(self, other):
        T = self.get_type()
        if isinstance(other, int) and other >= 0:
            other = Number(NatType, other)
        elif isinstance(other, (int, Fraction)):
            other = Number(RealType, other)
        if other.get_type() == NatType:
            return nat_power(T)(self, other)
        elif other.get_type() == RealType:
            return real_power(T)(self, other)
        else:
            raise TermException('__pow__: unexpected type for exponent.')

    def __rpow__(self, other):
        if not isinstance(other, Term):
            raise TermException('__rpow__: base must be a HOL term.')
        base_T = other.get_type()
        exponent_T = self.get_type()
        if exponent_T == NatType:
            return nat_power(base_T)(other, self)
        elif exponent_T == RealType:
            return real_power(base_T)(other, self)
        else:
            raise TermException('__rpow__: unexpected type for exponent.')

    def is_less_eq(self):
        return self.is_comb('less_eq', 2)

    def is_less(self):
        return self.is_comb('less', 2)

    def is_greater_eq(self):
        return self.is_comb('greater_eq', 2)

    def is_greater(self):
        return self.is_comb('greater', 2)

    def __le__(self, other):
        T = self.get_type()
        if isinstance(other, (int, Fraction)):
            other = Number(T, other)
        return less_eq(T)(self, other)

    def __lt__(self, other):
        T = self.get_type()
        if isinstance(other, (int, Fraction)):
            other = Number(T, other)
        return less(T)(self, other)

    def __ge__(self, other):
        T = self.get_type()
        if isinstance(other, (int, Fraction)):
            other = Number(T, other)
        return greater_eq(T)(self, other)

    def __gt__(self, other):
        T = self.get_type()
        if isinstance(other, (int, Fraction)):
            other = Number(T, other)
        return greater(T)(self, other)

    def get_svars(self):
        def rec(t):
            if t.is_svar():
                return [t]
            elif t.is_comb():
                return rec(t.fun) + rec(t.arg)
            elif t.is_abs():
                return rec(t.body)
            else:
                return []

        return term_ord.sorted_terms(rec(self))

    def get_vars(self):
        def rec(t):
            if t.is_var():
                return [t]
            elif t.is_comb():
                return rec(t.fun) + rec(t.arg)
            elif t.is_abs():
                return rec(t.body)
            else:
                return []

        return term_ord.sorted_terms(rec(self))

    def get_consts(self):
        def rec(t):
            if t.is_const():
                return [t]
            elif t.is_comb():
                return rec(t.fun) + rec(t.arg)
            elif t.is_abs():
                return rec(t.body)
            else:
                return []
        return term_ord.sorted_terms(rec(self))
        

    def has_var(self):
        if self.is_var():
            return True
        elif self.is_comb():
            return self.fun.has_var() or self.arg.has_var()
        elif self.is_abs():
            return self.body.has_var()
        else:
            return False

    def get_stvars(self):
        def rec(t):
            if t.is_var() or t.is_const():
                return t.T.get_stvars()
            elif t.is_comb():
                return rec(t.fun) + rec(t.arg)
            elif t.is_abs():
                return t.var_T.get_stvars() + rec(t.body)
            else:
                return []

        return term_ord.sorted_typs(rec(self))


class SVar(Term):
    """Schematic variable, specified by name and type."""
    def __init__(self, name, T):
        self.ty = Term.SVAR
        self.name = name
        self.T = T

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
            raise TypeError
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

def get_svars(t):
    """Returns list of schematic variables in a term or a list of terms."""
    if isinstance(t, Term):
        return t.get_svars()
    elif isinstance(t, list):
        return term_ord.sorted_terms(sum([s.get_svars() for s in t], []))
    else:
        raise TypeError

def get_vars(t):
    """Returns list of variables in a term or a list of terms."""
    if isinstance(t, Term):
        return t.get_vars()
    elif isinstance(t, list):
        return term_ord.sorted_terms(sum([s.get_vars() for s in t], []))
    else:
        raise TypeError

def get_stvars(t):
    """Get the list of type variables for a term."""
    if isinstance(t, Term):
        return t.get_stvars()
    elif isinstance(t, list):
        return term_ord.sorted_typs(sum([s.get_stvars() for s in t], []))
    else:
        raise TypeError


true = Const("true", BoolType)
false = Const("false", BoolType)

neg = Const("neg", TFun(BoolType, BoolType))
conj = Const("conj", TFun(BoolType, BoolType, BoolType))
disj = Const("disj", TFun(BoolType, BoolType, BoolType))
implies = Const("implies", TFun(BoolType, BoolType, BoolType))

def equals(T):
    """Returns the equals constant for the given type."""
    return Const("equals", TFun(T, T, BoolType))

def Eq(s, t):
    """Construct the term s = t."""
    if isinstance(s, (int, Fraction)):
        assert isinstance(t, Term), "Eq: one of the arguments must be a term."
        s = Number(t.get_type(), s)
    elif isinstance(t, (int, Fraction)):
        t = Number(s.get_type(), t)

    return equals(s.get_type())(s, t)

def Not(t):
    """Return negation of boolean term t."""
    typecheck.checkinstance('Not', t, Term)
    return neg(t)

def And(*args):
    """Return the conjunction of the arguments."""
    typecheck.checkinstance('And', args, [Term])
    if not args:
        return true
    res = args[-1]
    for s in reversed(args[:-1]):
        res = conj(s, res)
    return res

def Or(*args):
    """Return the disjunction of the arguments."""
    typecheck.checkinstance('Or', args, [Term])
    if not args:
        return false
    res = args[-1]
    for s in reversed(args[:-1]):
        res = disj(s, res)
    return res

def Implies(*args):
    """Construct the term s1 --> ... --> sn --> t."""
    typecheck.checkinstance('Implies', args, [Term])
    if not args:
        raise TermException("Implies: input must have at least one term.")
    res = args[-1]
    for s in reversed(args[:-1]):
        res = implies(s, res)
    return res

def Lambda(*args):
    """Construct the term %x_1 ... x_n. body.
    
    The arguments are x_1, ..., x_n, body.

    Here x_1, ..., x_n must be variables (or schematic variable) and
    body is a term possibly depending on x_1, ..., x_n.
    
    """
    typecheck.checkinstance('Lambda', args, [Term])
    if len(args) < 2:
        raise TermException("Lambda: must provide two terms.")
    body = args[-1]
    for x in reversed(args[:-1]):
        if not (x.is_var() or x.is_svar()):
            raise TermException("Lambda: x must be a variable. Got %s" % str(x))
        body = Abs(x.name, x.T, body.abstract_over(x))
    return body

def forall(T):
    return Const("all", TFun(TFun(T, BoolType), BoolType))
 
def Forall(*args):
    """Construct the term !x_1 ... x_n. body.
    
    The arguments are x_1, ..., x_n, body.

    Here x_1, ..., x_n must be variables (or schematic variable) and
    body is a term possibly depending on x_1, ..., x_n.

    """
    typecheck.checkinstance('Forall', args, [Term])
    if len(args) < 2:
        raise TermException("Forall: must provide two terms.")
    body = args[-1]
    for x in reversed(args[:-1]):
        if not (x.is_var() or x.is_svar()):
            raise TermException("Forall: x must be a variable. Got %s" % str(x))
        body = forall(x.T)(Lambda(x, body))
    return body

def exists(T):
    return Const("exists", TFun(TFun(T, BoolType), BoolType))

def Exists(*args):
    """Construct the term EX x. body.
    
    Here x must be a variable and body is a term possibly depending on x.
    
    """
    typecheck.checkinstance('Forall', args, [Term])
    if len(args) < 2:
        raise TermException("Forall: must provide two terms.")
    body = args[-1]
    for x in reversed(args[:-1]):
        if not (x.is_var() or x.is_svar()):
            raise TermException("Forall: x must be a variable. Got %s" % str(x))
        body = exists(x.T)(Lambda(x, body))
    return body


def plus(T):
    return Const('plus', TFun(T, T, T))

def minus(T):
    return Const('minus', TFun(T, T, T))

def uminus(T):
    return Const('uminus', TFun(T, T))

def times(T):
    return Const('times', TFun(T, T, T))

def divides(T):
    return Const('real_divide', TFun(T, T, T))

def of_nat(T):
    return Const('of_nat', TFun(NatType, T))

def of_int(T):
    return Const('of_int', TFun(IntType, T))

def nat_power(T):
    return Const('power', TFun(T, NatType, T))

def real_power(T):
    return Const('power', TFun(T, RealType, T))

def less_eq(T):
    return Const('less_eq', TFun(T, T, BoolType))

def less(T):
    return Const('less', TFun(T, T, BoolType))

def greater_eq(T):
    return Const('greater_eq', TFun(T, T, BoolType))

def greater(T):
    return Const('greater', TFun(T, T, BoolType))

# Binary bits 0 and 1
nat_zero = Const('zero', NatType)
nat_one = Const('one', NatType)
bit0 = Const("bit0", TFun(NatType, NatType))
bit1 = Const("bit1", TFun(NatType, NatType))

def Binary(n):
    """Convert Python integer n to HOL binary form.
    
    This function does not apply of_nat.
    
    """
    typecheck.checkinstance('Binary', n, int)
    if n == 0:
        return nat_zero
    elif n == 1:
        return nat_one
    elif n % 2 == 0:
        return bit0(Binary(n // 2))
    else:
        return bit1(Binary(n // 2))

def Number(T, x):
    """Convert Python number x to HOL term with type T."""
    if x == 0:
        return Const('zero', T)
    if x == 1:
        return Const('one', T)
    if x < 0:
        assert T != NatType, "Number: natural numbers cannot be negative."
        return uminus(T)(Number(T, -x))
    if isinstance(x, Fraction):
        if x.denominator == 1:
            return Number(T, x.numerator)
        else:
            assert T != NatType, "Number: natural numbers cannot be fractions."
            assert T != IntType, "Number: integers cannot be fractions."
            return divides(T)(Number(T, x.numerator), Number(T, x.denominator))
    
    return of_nat(T)(Binary(x))

def Nat(n):
    """Construct natural number with value n."""
    return Number(NatType, n)

def Int(n):
    """Construct integer with value n."""
    return Number(IntType, n)

def Real(r):
    """Construct real number with value r."""
    return Number(RealType, r)

def Sum(T, ts):
    """Compute the sum of a list of terms with type T."""
    ts = list(ts)  # Coerce generators to list
    typecheck.checkinstance('Sum', T, Type, ts, [Term])
    if len(ts) == 0:
        return Const('zero', T)
    res = ts[0]
    for t in ts[1:]:
        res = res + t
    return res

def Prod(T, ts):
    """Compute the product of a list of terms with type T."""
    ts = list(ts)  # Coerce generators to list
    typecheck.checkinstance('Prod', T, Type, ts, [Term])
    if len(ts) == 0:
        return Const('one', T)
    res = ts[0]
    for t in ts[1:]:
        res = res * t
    return res

def BoolVars(s):
    """Create a list of variables of boolean type.

    s is a string containing space-separated names of variables.

    """
    nms = s.split(' ')
    return [Var(nm, BoolType) for nm in nms]

def NatVars(s):
    """Create a list of variables of nat type.

    s is a string containing space-separated names of variables.

    """
    nms = s.split(' ')
    return [Var(nm, NatType) for nm in nms]

def IntVars(s):
    """Create a list of variables of int type.

    s is a string containing space-separated names of variables.

    """
    nms = s.split(' ')
    return [Var(nm, IntType) for nm in nms]

def RealVars(s):
    """Create a list of variables of int type.

    s is a string containing space-separated names of variables.

    """
    nms = s.split(' ')
    return [Var(nm, RealType) for nm in nms]