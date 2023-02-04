"""Expressions."""

import copy
import functools
import operator
from decimal import Decimal
from collections.abc import Iterable
from typing import Dict, List, Optional, Set, TypeGuard, Tuple
from sympy.simplify.fu import *
from sympy.ntheory.factor_ import factorint

from integral import poly
from integral.poly import *

VAR, CONST, OP, FUN, DERIV, INTEGRAL, EVAL_AT, SYMBOL, LIMIT, INF, INDEFINITEINTEGRAL, DIFFERENTIAL, \
SKOLEMFUNC, SUMMATION = range(14)

op_priority = {
    "+": 65, "-": 65, "*": 70, "/": 70, "^": 75, "=": 50, "<": 50, ">": 50, "<=": 50, ">=": 50, "!=": 50
}


def is_square(r):
    return math.sqrt(r) * math.sqrt(r) == r


class Location:
    """Location within an expression."""

    def __init__(self, data):
        if isinstance(data, Iterable) and all(isinstance(n, int) for n in data):
            self.data = tuple(data)
        elif isinstance(data, str):
            if data in (".", ""):
                self.data = tuple([])
            else:
                self.data = tuple(int(n) for n in data.split('.'))
        elif isinstance(data, Location):
            self.data = data.data
        else:
            raise TypeError

    def __str__(self):
        if not self.data:
            return "."
        else:
            return ".".join(str(n) for n in self.data)

    def is_empty(self):
        return len(self.data) == 0

    @property
    def head(self):
        return self.data[0]

    @property
    def rest(self):
        return Location(self.data[1:])

    def append(self, i: int) -> "Location":
        return Location(self.data + (i,))


class Expr:
    """Expressions."""

    def __add__(self, other):
        if isinstance(other, (int, Fraction)):
            other = Const(other)
        return Op("+", self, other)

    def __radd__(self, other):
        if isinstance(other, (int, Fraction)):
            other = Const(other)
        return Op("+", other, self)

    def __sub__(self, other):
        if isinstance(other, (int, Fraction)):
            other = Const(other)
        return Op("-", self, other)

    def __mul__(self, other):
        if isinstance(other, (int, Fraction)):
            other = Const(other)
        return Op("*", self, other)

    def __rmul__(self, other):
        if isinstance(other, (int, Fraction)):
            other = Const(other)
        return Op("*", other, self)

    def __truediv__(self, other):
        if isinstance(other, (int, Fraction)):
            other = Const(other)
        return Op("/", self, other)

    def __rtruediv__(self, other):
        if isinstance(other, (int, Fraction)):
            other = Const(other)
        return Op("/", other, self)

    def __xor__(self, other):
        if isinstance(other, (int, Fraction)):
            other = Const(other)
        return Op("^", self, other)

    def __pow__(self, other):
        if isinstance(other, (int, Fraction)):
            other = Const(other)
        return Op("^", self, other)

    def __neg__(self):
        if self == POS_INF:
            return NEG_INF
        elif self == NEG_INF:
            return POS_INF
        return Op("-", self)

    def size(self):
        if self.ty in (VAR, CONST, SYMBOL, INF):
            return 1
        elif self.is_op() or self.is_fun():
            return 1 + sum(arg.size() for arg in self.args)
        elif self.is_deriv():
            return 1 + self.body.size()
        elif self.ty in (INTEGRAL, EVAL_AT):
            return 1 + self.lower.size() + self.upper.size() + self.body.size()
        elif self.ty == LIMIT:
            return 1 + self.lim.size() + self.body.size()
        elif self.ty in (DIFFERENTIAL, INDEFINITEINTEGRAL):
            return 1 + self.body.size()
        elif self.ty == SKOLEMFUNC:
            return 1 + len(self.dependent_vars)
        elif self.ty == SUMMATION:
            return 1 + self.lower.size() + self.upper.size() + self.body.size()
        else:
            raise NotImplementedError

    def is_var(self) -> TypeGuard["Var"]:
        return self.ty == VAR

    def is_diff(self) -> bool:
        return self.ty == DIFFERENTIAL

    def is_const(self) -> TypeGuard["Const"]:
        return self.ty == CONST

    def is_op(self) -> TypeGuard["Op"]:
        return self.ty == OP

    def is_fun(self) -> TypeGuard["Fun"]:
        return self.ty == FUN

    def is_deriv(self) -> TypeGuard["Deriv"]:
        return self.ty == DERIV

    def is_skolem_func(self) -> TypeGuard["SkolemFunc"]:
        return self.ty == SKOLEMFUNC
    
    def is_symbol(self) -> TypeGuard["Symbol"]:
        return self.ty == SYMBOL

    def is_zero(self) -> bool:
        return self.is_const() and self.val == 0

    def is_INF(self) -> bool:
        if self.is_power():
            a, b = self.args
            if a.is_const() and b.is_const():
                return a.val == 0 and b.val < 0
        elif self.is_divides():
            a, b = self.args
            if a.is_const() and b.is_const():
                return a.val != 0 and b.val == 0
        elif self.is_fun():
            if self.func_name == 'tan':
                a = (self.args[0] / Fun('pi')).normalize()
                # the coef of pi
                coef = (a * 2).normalize()
                if coef.is_const() and coef.val % 2 == 1:
                    return True
        return False

    def is_integral(self) -> bool:
        return self.ty == INTEGRAL

    def is_indefinite_integral(self) -> bool:
        return self.ty == INDEFINITEINTEGRAL

    def is_evalat(self) -> bool:
        return self.ty == EVAL_AT

    def is_limit(self) -> bool:
        return self.ty == LIMIT

    def is_plus(self):
        return self.ty == OP and self.op == '+'

    def is_uminus(self):
        return self.ty == OP and self.op == '-' and len(self.args) == 1

    def is_minus(self):
        return self.ty == OP and self.op == '-' and len(self.args) == 2

    def is_times(self):
        return self.ty == OP and self.op == '*'

    def is_divides(self):
        return self.ty == OP and self.op == '/'

    def is_power(self):
        return self.ty == OP and self.op == '^'

    def is_equals(self):
        return self.ty == OP and self.op == '='

    def is_v_equals(self):
        return self.is_equals() and self.args[0].is_var() and self.args[1].is_constant()

    def is_not_equals(self):
        return self.ty == OP and self.op == "!="

    def is_less(self):
        return self.ty == OP and self.op == "<"

    def is_less_eq(self):
        return self.ty == OP and self.op == "<="

    def is_greater(self):
        return self.ty == OP and self.op == ">"

    def is_greater_eq(self):
        return self.ty == OP and self.op == ">="

    def is_inf(self):
        return self.ty == INF and (self.t == Decimal("inf") or self.t == Decimal("-inf"))

    def is_pos_inf(self):
        return self.ty == INF and self.t == Decimal("inf")

    def is_neg_inf(self):
        return self.ty == INF and self.t == Decimal("-inf")

    def is_trig(self):
        return self.ty == FUN and self.func_name in ("sin", "cos", "tan", "cot", "csc", "sec")

    def is_inverse_trig(self):
        return self.ty == FUN and self.func_name in ("asin", "acos", "atan", "acot", "acsc", "asec")

    def is_skolem_term(self):
        if self.get_vars() != set():
            return False
        if not self.is_constant():
            return True
        else:
            return False

    def all_dependencies(self):
        """Return the set of all dependent variables in Skolem terms."""
        if self.ty == SKOLEMFUNC:
            return self.dependent_vars
        elif self.is_constant() or self.ty == VAR:
            return set()
        elif self.ty in (OP, FUN):
            res = set()
            for arg in self.args:
                res = res.union(arg.all_dependencies())
            return res
        else:
            raise NotImplementedError
        
    def is_summation(self) -> TypeGuard["Summation"]:
        return self.ty == SUMMATION

    @property
    def lhs(self) -> Expr:
        if self.is_equals():
            return self.args[0]
        else:
            raise AssertionError("lhs: term is not an equality")

    @property
    def rhs(self) -> Expr:
        if self.is_equals():
            return self.args[1]
        else:
            raise AssertionError("rhs: term is not an equality")

    def __le__(self, other):
        if isinstance(other, (int, Fraction)):
            return False

        if self.size() != other.size():
            return self.size() <= other.size()

        if self.ty != other.ty:
            return self.ty <= other.ty

        if self.is_var():
            return self.name <= other.name
        elif self.is_const():
            return self.val <= other.val
        elif self.is_op():
            return (self.op, self.args) <= (other.op, other.args)
        elif self.is_fun():
            return (self.func_name, self.args) <= (other.func_name, other.args)
        elif self.is_deriv():
            return (self.body, self.var) <= (other.body, other.var)
        elif self.is_integral() or self.is_evalat():
            return (self.body, self.lower, self.upper, self.var) <= \
                   (other.body, other.lower, other.upper, other.var)
        elif self.is_symbol():
            return sum(self.ty) <= sum(other.ty)
        elif self.is_summation():
            return (self.body, self.lower, self.upper, self.index_var) <= \
                   (other.body, other.lower, other.upper, other.index_var)
        elif self.is_skolem_func():
            return (self.name, self.dependent_vars) <= (other.name, other.dependent_vars)
        else:
            print(type(self))
            raise NotImplementedError

    def __lt__(self, other):
        return self <= other and self != other

    def __gt__(self, other):
        return other <= self and self != other

    def __ge__(self, other):
        return not self < other

    def priority(self):
        if self.ty in (VAR, SYMBOL, INF, SKOLEMFUNC):
            return 100
        elif self.ty == CONST:
            if isinstance(self.val, Fraction) and self.val.denominator != 1:
                return op_priority['/']
            elif self.val < 0:
                # return 80  # priority of uminus
                return 74
            else:
                return 100
        elif self.ty == OP:
            if len(self.args) == 1:
                return 80  # priority of uminus
            elif self.op in op_priority:
                return op_priority[self.op]
            else:
                raise NotImplementedError
        elif self.ty in (FUN, SUMMATION):
            return 95
        elif self.ty in (DERIV, INTEGRAL, EVAL_AT, INDEFINITEINTEGRAL, DIFFERENTIAL):
            return 10
        elif self.ty == LIMIT:
            return 5

    def __lt__(self, other):
        return self <= other and self != other

    def get_subexpr(self, loc) -> Expr:
        """Given an expression, return the subexpression at location."""
        if not isinstance(loc, Location):
            loc = Location(loc)
        if loc.is_empty():
            return self
        elif self.ty == VAR or self.ty == CONST:
            raise AssertionError("get_subexpr: invalid location")
        elif self.ty == OP or self.ty == FUN:
            assert loc.head < len(self.args), "get_subexpr: invalid location"
            return self.args[loc.head].get_subexpr(loc.rest)
        elif self.ty == DERIV:
            assert loc.head == 0, "get_subexpr: invalid location"
            return self.body.get_subexpr(loc.rest)
        elif self.ty == INTEGRAL or self.ty == EVAL_AT:
            if loc.head == 0:
                return self.body.get_subexpr(loc.rest)
            elif loc.head == 1:
                return self.lower.get_subexpr(loc.rest)
            elif loc.head == 2:
                return self.upper.get_subexpr(loc.rest)
            else:
                raise AssertionError("get_subexpr: invalid location")
        elif self.ty == LIMIT:
            assert loc.head == 0, "get_subexpr: invalid location"
            return self.body.get_subexpr(loc.rest)

        else:
            raise NotImplementedError

    def replace_expr(self, loc, new_expr: Expr) -> Expr:
        """Replace self's subexpr at location."""
        if not isinstance(loc, Location):
            loc = Location(loc)
        if loc.is_empty():
            return new_expr
        elif self.ty == VAR or self.ty == CONST:
            raise AssertionError("replace_expr: invalid location")
        elif self.ty == OP:
            assert loc.head < len(self.args), "replace_expr: invalid location"
            if len(self.args) == 1:
                return Op(self.op, self.args[0].replace_expr(loc.rest, new_expr))
            elif len(self.args) == 2:
                if loc.head == 0:
                    return Op(self.op, self.args[0].replace_expr(loc.rest, new_expr), self.args[1])
                elif loc.head == 1:
                    return Op(self.op, self.args[0], self.args[1].replace_expr(loc.rest, new_expr))
                else:
                    raise AssertionError("replace_expr: invalid location")
            else:
                raise NotImplementedError
        elif self.ty == FUN:
            assert loc.head < len(self.args), "replace_expr: invalid location"
            arg = self.args[loc.head].replace_expr(loc.rest, new_expr)
            return Fun(self.func_name, arg)
        elif self.ty == INTEGRAL:
            if loc.head == 0:
                return Integral(self.var, self.lower, self.upper, self.body.replace_expr(loc.rest, new_expr))
            elif loc.head == 1:
                return Integral(self.var, self.lower.replace_expr(loc.rest, new_expr), self.upper, self.body)
            elif loc.head == 2:
                return Integral(self.var, self.lower, self.upper.replace_expr(loc.rest, new_expr), self.body)
            else:
                raise AssertionError("replace_expr: invalid location")
        elif self.ty == EVAL_AT:
            if loc.head == 0:
                return EvalAt(self.var, self.lower, self.upper, self.body.replace_expr(loc.rest, new_expr))
            elif loc.head == 1:
                return EvalAt(self.var, self.lower.replace_expr(loc.rest, new_expr), self.upper, self.body)
            elif loc.head == 2:
                return EvalAt(self.var, self.lower, self.upper.replace_expr(loc.rest, new_expr), self.body)
            else:
                raise AssertionError("replace_expr: invalid location")
        elif self.ty == DERIV:
            assert loc.head == 0, "replace_expr: invalid location"
            return Deriv(self.var, self.body.replace_expr(loc.rest, new_expr))
        elif self.ty == LIMIT:
            assert loc.head == 0, "replace_expr: invalid location"
            return Limit(self.var, self.limit, self.body.replace_expr(loc.rest, new_expr))
        else:
            raise NotImplementedError

    def get_location(self) -> Location:
        """Returns the location at which the 'selected' field is True."""
        location = []

        def get(exp, loc=''):
            if hasattr(exp, 'selected') and exp.selected == True:
                location.append(loc[1:])
                exp.selected = False  # Once it is found, restore it.
            elif exp.ty == OP or exp.ty == FUN:
                for i in range(len(exp.args)):
                    get(exp.args[i], loc + "." + str(i))
            elif exp.ty == INTEGRAL or exp.ty == EVAL_AT:
                get(exp.lower, loc + ".1")
                get(exp.upper, loc + ".2")
                get(exp.body, loc + ".0")
            elif exp.ty == DERIV or exp.ty == LIMIT:
                get(exp.body, loc + ".0")

        get(self)
        return location[0]

    def find_subexpr(self, subexpr: Expr) -> List[Location]:
        """Returns the location of a subexpression."""
        locations = []

        def find(e: Expr, loc: Location):
            if e == subexpr:
                locations.append(Location(loc))
            elif e.is_op() or e.is_fun():
                for i, arg in enumerate(e.args):
                    find(arg, loc.append(i))
            elif e.is_integral() or e.is_evalat():
                find(e.lower, loc.append(1))
                find(e.upper, loc.append(2))
                find(e.body, loc.append(0))
            elif e.is_deriv() or e.is_limit() or e.is_indefinite_integral():
                find(e.body, loc.append(0))
            elif e.is_summation():
                find(e.body, loc.append(0))
                find(e.lower, loc.append(1))
                find(e.upper, loc.append(2))

        find(self, Location(""))
        return locations

    def subst(self, var: str, e: Expr) -> Expr:
        """Substitute occurrence of var for e in self."""
        assert isinstance(var, str) and isinstance(e, Expr)
        if self.is_var():
            if self.name == var:
                return e
            else:
                return self
        elif self.is_const():
            return self
        elif self.is_skolem_func():
            return SkolemFunc(self.name, tuple(arg.subst(var, e) for arg in self.dependent_vars))
        elif self.is_symbol():
            return self
        elif self.is_op():
            return Op(self.op, *[arg.subst(var, e) for arg in self.args])
        elif self.is_fun():
            return Fun(self.func_name, *[arg.subst(var, e) for arg in self.args])
        elif self.is_deriv():
            return Deriv(self.var, self.body.subst(var, e))
        elif self.is_limit():
            return Limit(self.var, self.lim.subst(var, e), self.body.subst(var, e))
        elif self.is_inf():
            return self
        elif self.is_integral():
            return Integral(self.var, self.lower.subst(var, e), self.upper.subst(var, e), self.body.subst(var, e))
        elif self.is_indefinite_integral():
            return IndefiniteIntegral(self.var, self.body.subst(var, e), self.skolem_args)
        elif self.is_evalat():
            return EvalAt(self.var, self.lower.subst(var, e), self.upper.subst(var, e), self.body.subst(var, e))
        elif self.is_summation():
            return Summation(self.index_var, self.lower.subst(var, e), self.upper.subst(var, e),
                             self.body.subst(var, e))
        else:
            print('subst on', self)
            raise NotImplementedError

    def is_constant(self):
        """Determine whether expr is a number.
        
        Note Inf is not considered to be constants.
        
        """
        if self.is_const():
            return True
        elif self.is_fun() or self.is_op():
            return all(arg.is_constant() for arg in self.args)
        else:
            return False
        
    def is_evaluable(self):
        return self.is_constant() or self.is_inf()

    def get_vars(self) -> Set[str]:
        """Obtain the set of variables in self."""
        res = set()

        def rec(t, bd_vars):
            if t.ty == VAR:
                if t.name not in bd_vars:
                    res.add(t.name)
            elif t.ty in (CONST, INF, SKOLEMFUNC):
                return
            elif t.ty in (OP, FUN):
                for arg in t.args:
                    rec(arg, bd_vars)
            elif t.ty == DERIV:
                rec(t.body, bd_vars + [t.var])
            elif t.ty == LIMIT:
                rec(t.lim, bd_vars + [t.var])
                rec(t.body, bd_vars + [t.var])
            elif t.ty in (INTEGRAL, EVAL_AT):
                rec(t.lower, bd_vars + [t.var])
                rec(t.upper, bd_vars + [t.var])
                rec(t.body, bd_vars + [t.var])
            elif t.ty == INDEFINITEINTEGRAL:
                rec(t.body, bd_vars + [t.var])
            elif t.ty == SUMMATION:
                rec(t.lower, bd_vars + [t.index_var])
                rec(t.upper, bd_vars + [t.index_var])
                rec(t.body, bd_vars + [t.index_var])
            elif t.is_equals():
                rec(t.bd_vars)
                rec(t.rhs, bd_vars)
            else:
                print(t, type(t))
                raise NotImplementedError

        rec(self, [])
        return res

    def has_symbol(self) -> bool:
        if isinstance(self, Symbol):
            return True
        elif isinstance(self, Union[Var, Const, Inf, SkolemFunc]):
            return False
        elif isinstance(self, Integral):
            return self.upper.has_symbol() or self.lower.has_symbol() or self.body.has_symbol()
        elif isinstance(self, IndefiniteIntegral):
            return self.body.has_symbol()
        elif isinstance(self, Union[Op, Fun]):
            return any([arg.has_symbol for arg in self.args])
        elif isinstance(self, Summation):
            return self.body.has_symbol()
        else:
            print(self)
            raise NotImplementedError

    def contains_var(self, x: str) -> bool:
        """Whether self contains variable x."""
        assert isinstance(x, str)
        return x in self.get_vars()

    def replace(self, e: Expr, repl_e: Expr) -> Expr:
        """Replace occurrences of e with repl_e."""
        assert isinstance(e, Expr) and isinstance(repl_e, Expr)
        if self == e:
            return repl_e
        elif self.ty in (VAR, CONST, INF):
            return self
        elif self.is_op():
            return Op(self.op, *[arg.replace(e, repl_e) for arg in self.args])
        elif self.is_fun():
            return Fun(self.func_name, *[arg.replace(e, repl_e) for arg in self.args])
        elif self.is_deriv():
            return Deriv(self.var, self.body.replace(e, repl_e))
        elif self.is_integral():
            return Integral(self.var, self.lower.replace(e, repl_e), self.upper.replace(e, repl_e),
                            self.body.replace(e, repl_e))
        elif self.is_evalat():
            return EvalAt(self.var, self.lower.replace(e, repl_e), self.upper.replace(e, repl_e),
                          self.body.replace(e, repl_e))
        elif self.is_skolem_func():
            return SkolemFunc(self.name, tuple(var.replace(e, repl_e) for var in self.dependent_vars))
        elif self.is_summation():
            return Summation(self.index_var, self.lower, self.upper, self.body.replace(e, repl_e))
        elif self.is_limit():
            return Limit(self.var, self.lim.replace(e, repl_e), self.body.replace(e, repl_e), self.drt)
        else:
            print(self)
            raise NotImplementedError

    def to_const_poly(self) -> ConstantPolynomial:
        """Normalize a constant expression.

        Assume self.is_constant() = True in this function.

        """
        if self.ty == VAR:
            raise ValueError

        elif self.ty == CONST:
            return poly.const_fraction(self.val)

        elif self.ty == INF:
            raise ValueError

        elif self.is_plus():
            return self.args[0].to_const_poly() + self.args[1].to_const_poly()

        elif self.is_uminus():
            return -self.args[0].to_const_poly()

        elif self.is_minus():
            return self.args[0].to_const_poly() - self.args[1].to_const_poly()

        elif self.is_times():
            return self.args[0].to_const_poly() * self.args[1].to_const_poly()

        elif self.is_divides():
            a, b = self.args[0].to_const_poly(), self.args[1].to_const_poly()
            if b.is_fraction() and b.get_fraction() == 0:
                raise ZeroDivisionError("Zero denominator")
            if b.is_monomial():
                return a / b
            else:
                return a / poly.const_singleton(from_const_poly(b))

        elif self.is_power():
            a, b = self.args[0].to_const_poly(), self.args[1].to_const_poly()
            if a.is_zero() and b.is_fraction() and b.get_fraction() > 0:
                return poly.const_fraction(0)
            elif a.is_monomial() and b.is_fraction():
                return a ** b.get_fraction()
            elif b.is_fraction():
                rb = b.get_fraction()
                if rb > 0 and int(rb) == rb and rb <= 3:
                    res = poly.const_fraction(1)
                    for i in range(int(rb)):
                        res *= a
                    return res
                else:
                    return poly.const_singleton(from_const_poly(a) ** from_const_poly(b))
            else:
                return poly.const_singleton(from_const_poly(a) ** from_const_poly(b))

        elif self.ty == FUN and self.func_name == 'sqrt':
            a = self.args[0].to_const_poly()
            if a.is_fraction() and is_square(a.get_fraction()):  # is square
                return poly.const_fraction(Fraction(math.sqrt(a.get_fraction())))
            elif a.is_monomial():
                return a ** Fraction(1 / 2)
            else:
                return poly.const_singleton(sqrt(from_const_poly(a)))

        elif self.ty == FUN and self.func_name == 'pi':
            return poly.const_singleton(pi)

        elif self.ty == FUN and self.func_name == 'exp':
            a = self.args[0].to_const_poly()
            if a.is_fraction() and a.get_fraction() == 0:
                return poly.const_fraction(1)
            elif a.is_fraction():
                return poly.ConstantPolynomial([poly.ConstantMonomial(1, [(E, a.get_fraction())])])
            elif self.args[0].ty == FUN and self.args[0].func_name == "log":
                return self.args[0].args[0].to_const_poly()
            else:
                return poly.const_singleton(exp(from_const_poly(a)))

        elif self.ty == FUN and self.func_name == 'log':
            a = self.args[0].to_const_poly()
            if a.is_fraction() and a.get_fraction() == 1:
                return poly.const_fraction(0)
            elif a.is_monomial():
                mono = a.get_monomial()
                log_factors = []
                for n, e in mono.factors:
                    if isinstance(n, (int, Fraction)):
                        log_factors.append(poly.const_fraction(e) * poly.const_singleton(log(Const(n))))
                    elif isinstance(n, Expr) and n == E:
                        log_factors.append(poly.const_fraction(e))
                    elif isinstance(n, Expr) and n.is_fun() and n.func_name == "exp":
                        body = n.args[0]
                        log_factors.append(poly.const_singleton(body))
                    else:
                        log_factors.append(poly.const_fraction(e) * poly.const_singleton(log(n)))
                if mono.coeff == 1:
                    return sum(log_factors[1:], log_factors[0])
                else:
                    if isinstance(mono.coeff, int):
                        int_factors = factorint(mono.coeff)
                    elif isinstance(mono.coeff, Fraction):
                        int_factors = factorint(mono.coeff.numerator)
                        denom_factors = factorint(mono.coeff.denominator)
                        for b, e in denom_factors.items():
                            if b not in int_factors:
                                int_factors[b] = 0
                            int_factors[b] -= e
                    else:
                        raise NotImplementedError
                    log_ints = []
                    for b, e in int_factors.items():
                        log_ints.append(ConstantPolynomial([ConstantMonomial(e, [(log(Const(b)), 1)])]))
                    return sum(log_factors + log_ints[1:], log_ints[0])
            else:
                return poly.const_singleton(log(from_const_poly(a)))

        elif self.ty == FUN and self.func_name in ('sin', 'cos', 'tan', 'cot', 'csc', 'sec'):
            a = self.args[0].to_const_poly()
            norm_a = from_const_poly(a)

            c = Symbol('c', [CONST])
            if match(norm_a, c * pi):
                x = norm_a.args[0]
                n = int(x.val)
                if n % 2 == 0:
                    norm_a = Const(x.val - n) * pi
                else:
                    norm_a = Const(x.val - (n + 1)) * pi if n > 0 else Const(x.val - (n - 1)) * pi
            elif norm_a == -pi:
                norm_a = pi

            norm_a = norm_a.normalize_constant()
            if match(norm_a, c * pi) and norm_a.args[0].val < 0:
                neg_norm_a = Const(-norm_a.args[0].val) * pi
                if self.func_name in ('sin', 'tan', 'cot', 'csc'):
                    val = -Fun(self.func_name, neg_norm_a)
                else:
                    val = Fun(self.func_name, neg_norm_a)
                return val.to_const_poly()
            else:
                return poly.const_singleton(Fun(self.func_name, norm_a))

        elif self.ty == FUN and self.func_name in ('asin', 'acos', 'atan', 'acot', 'acsc', 'asec'):
            a = self.args[0].to_const_poly()
            norm_a = from_const_poly(a)
            return poly.const_singleton(Fun(self.func_name, norm_a))

        elif self.ty == FUN and self.func_name == 'abs':
            a = self.args[0].to_const_poly()
            if a.is_fraction():
                return poly.const_fraction(abs(a.get_fraction()))
            elif self.args[0].is_constant():
                if eval_expr(self.args[0]) >= 0:
                    return a
                else:
                    return -a
            else:
                return poly.const_singleton(self)

        elif self.ty == FUN and self.func_name == "binom":
            a = self.args[0].to_const_poly()
            norm_a = from_const_poly(a)
            b = self.args[1].to_const_poly()
            norm_b = from_const_poly(b)
            if norm_a.is_const() and norm_b.is_const():
                return Const(math.comb(norm_a.val, norm_b.val)).to_const_poly()
            else:
                return poly.const_singleton(binom(norm_a, norm_b))
        elif self.ty == FUN and self.func_name == 'factorial':
            a = self.args[0].to_const_poly()
            norm_a = from_const_poly(a)

            def rec(n):
                if n == 0 or n == 1:
                    return 1
                else:
                    return n * rec(n - 1)

            if norm_a.is_const() and int(norm_a.val) == float(norm_a.val):
                return Const(rec(norm_a.val)).to_const_poly()
            else:
                return poly.const_singleton(factorial(norm_a))
        elif self.ty == FUN:
            args_norm = [arg.normalize() for arg in self.args]
            return poly.const_singleton(Fun(self.func_name, *args_norm))
        else:
            print("to_const_poly:", self)
            raise NotImplementedError

    def normalize_constant(self):
        return from_const_poly(self.to_const_poly())

    def to_poly(self) -> Polynomial:
        """Convert expression to polynomial."""
        if self.ty == VAR:
            return poly.singleton(self)

        elif self.is_constant():
            # Consists of CONST, OP and FUN only.
            return poly.constant(self.to_const_poly())

        elif self.is_plus():
            return self.args[0].to_poly() + self.args[1].to_poly()

        elif self.is_uminus():
            return -self.args[0].to_poly()

        elif self.is_minus():
            return self.args[0].to_poly() - self.args[1].to_poly()

        elif self.is_times():
            a, b = self.args[0].to_poly(), self.args[1].to_poly()
            if a.is_monomial() and b.is_monomial():
                return a * b
            elif a.is_fraction() or b.is_fraction():
                return a * b
            elif a.is_monomial():
                return a * poly.singleton(from_poly(b))
            elif b.is_monomial():
                return b * poly.singleton(from_poly(a))
            else:
                return poly.singleton(from_poly(a)) * poly.singleton(from_poly(b))

        elif self.is_divides():
            a, b = self.args[0].to_poly(), self.args[1].to_poly()
            if a.is_fraction() and a.get_fraction() == 0:
                return poly.constant(poly.const_fraction(0))
            elif b.is_fraction() and b.get_fraction() == 1:
                return a
            elif a.is_monomial() and b.is_monomial():
                return a / b
            elif a.is_monomial():
                return a / poly.singleton(from_poly(b))
            elif b.is_monomial():
                return poly.singleton(from_poly(a)) / b
            else:
                return poly.singleton(from_poly(a)) / poly.singleton(from_poly(b))

        elif self.is_power():
            a, b = self.args[0].to_poly(), self.args[1].to_poly()
            if a.is_monomial() and b.is_fraction():
                return a ** b.get_fraction()
            elif b.is_fraction():
                return poly.Polynomial([poly.Monomial(poly.const_fraction(1), [(from_poly(a), b.get_fraction())])])
            else:
                return poly.Polynomial([poly.Monomial(poly.const_fraction(1), [(from_poly(a), b)])])

        elif self.ty == FUN and self.func_name == "exp":
            a = self.args[0]
            if a.ty == FUN and a.func_name == "log":
                return a.args[0].to_poly()
            else:
                return poly.Polynomial([poly.Monomial(poly.const_fraction(1), [(E, a.to_poly())])])

        elif self.ty == FUN and self.func_name in ("sin", "cos", "tan", "cot", "csc", "sec"):
            a = self.args[0]
            if a.ty == FUN and a.func_name == "a" + self.func_name:
                # sin(asin(x)) = x
                return a.args[0].to_poly()
            else:
                return poly.singleton(Fun(self.func_name, a.normalize()))

        elif self.ty == FUN and self.func_name in ("asin", "acos", "atan", "acot", "acsc", "asec"):
            a, = self.args
            if self.func_name in ("atan", "acot") and a.ty == FUN and a.func_name == self.func_name[1:]:
                # atan(tan(x)) = x
                return a.args[0].to_poly()
            else:
                return poly.singleton(Fun(self.func_name, a.normalize()))

        elif self.ty == FUN and self.func_name == "log":
            a, = self.args
            if a.ty == FUN and a.func_name == "exp":
                return a.args[0].to_poly()
            elif a.ty == OP and a.op == "^" and a.args[1].is_constant():
                return Polynomial([Monomial(a.args[1].to_const_poly(), [(log(a.args[0].normalize()), 1)])])
            else:
                return poly.singleton(log(a.normalize()))

        elif self.ty == FUN and self.func_name == "sqrt":
            return Op("^", self.args[0], Const(Fraction(1, 2))).to_poly()

        elif self.ty == FUN and self.func_name == "abs":
            if self.args[0].normalize().ty == CONST:
                return poly.constant(Const(abs(self.args[0].normalize().val)).to_const_poly())
            return poly.singleton(Fun("abs", self.args[0].normalize()))

        elif self.ty == FUN:
            args_norm = [arg.normalize() for arg in self.args]
            return poly.singleton(Fun(self.func_name, *args_norm))

        elif self.ty == EVAL_AT:
            # upper = self.body.subst(self.var, self.upper)
            # lower = self.body.subst(self.var, self.lower)
            # TODO: improper integral
            upper = self.body.subst(self.var, self.upper) if self.upper not in (POS_INF, NEG_INF) else Limit(self.var, self.upper, self.body)
            lower = self.body.subst(self.var, self.lower) if self.lower not in (POS_INF, NEG_INF) else Limit(self.var, self.lower, self.body)
            return (upper.normalize() - lower.normalize()).to_poly()

        elif self.ty == INTEGRAL:
            if self.lower == self.upper:
                return poly.constant(Const(0).to_const_poly())
            body = self.body.normalize()
            return poly.singleton(Integral(self.var, self.lower.normalize(), self.upper.normalize(), body))

        elif self.ty == LIMIT:
            return poly.singleton(Limit(self.var, self.lim.normalize(), self.body.normalize()))

        elif self.ty == INF:
            if self == Inf(Decimal("inf")):
                return poly.singleton(self)
            else:
                return -poly.singleton(Inf(Decimal("inf")))
        elif self.ty == INDEFINITEINTEGRAL:
            return poly.singleton(expr.IndefiniteIntegral(self.var, self.body.normalize(), self.skolem_args))
        else:
            return poly.singleton(self)

    def normalize(self):
        if self.is_equals():
            return Eq(self.lhs.normalize(), self.rhs.normalize())
        return from_poly(self.to_poly())

    def has_func(self, func_name: str) -> bool:
        # determine whether expression has function called func_name

        if self.is_op():
            args = self.args
            for a in args:
                if a.has_func(func_name):
                    return True
        elif self.is_fun():
            if (self.func_name == func_name):
                return True
            else:
                args = self.args
                for a in args:
                    if a.has_func(func_name):
                        return True
        elif self.is_integral():
            return self.lower.has_func(func_name) or self.upper.has_func(func_name) or self.body.has_func(func_name)
        elif self.is_deriv():
            return self.body.has_func(func_name)
        elif self.is_limit():
            return self.body.has_func(func_name)
        else:
            return False

    def separate_integral(self) -> List[Tuple[Expr, Location]]:
        """Collect the list of all integrals appearing in self."""
        result = []

        def collect(p: Expr, result):
            if p.is_integral() or p.is_indefinite_integral():
                p.selected = True
                loc = self.get_location()
                del p.selected
                result.append((p, loc))
            elif p.ty == OP:
                for arg in p.args:
                    collect(arg, result)
            elif p.ty == LIMIT:
                collect(p.body, result)
            elif p.ty == DERIV:
                collect(p.body, result)

        collect(self, result)
        return result

    @property
    def depth(self):
        """Return the depth of expression as an estimate of problem difficulty."""

        def d(expr):
            if expr.ty in (VAR, CONST):
                return 0
            elif expr.ty in (OP, FUN):
                if len(expr.args) == 0:
                    return 1
                return 1 + max([d(expr.args[i]) for i in range(len(expr.args))])
            elif expr.ty in (EVAL_AT, INTEGRAL, DERIV):
                return d(expr.body)
            elif expr.ty == SYMBOL:
                raise TypeError

        return d(self)

    def is_spec_function(self, fun_name):
        """Return true iff e is formed by rational options of fun_name."""
        v = Symbol("v", [VAR, OP, FUN])
        pat1 = sin(v)
        if len(find_pattern(self, pat1)) != 1:
            return False

        def rec(ex):
            if ex.ty == CONST:
                return True
            elif ex.ty == VAR:
                return False
            elif ex.ty == OP:
                return all(rec(arg) for arg in ex.args)
            elif ex.ty == FUN:
                return True if ex.func_name == fun_name else False
            else:
                return False

        return rec(self)

    def nonlinear_subexpr(self):
        """Return nonlinear & nonconstant subexpression."""
        subs = []
        a = Symbol('a', [CONST])
        b = Symbol('b', [CONST])
        x = Symbol('x', [VAR])
        patterns = [a * x, a * x + b, a * x - b, x, b + a * x, a + x, x + a]

        def traverse(exp):
            table = [match(exp, p) for p in patterns]
            is_linear = functools.reduce(lambda x, y: x or y, table)
            if not exp.is_constant() and not is_linear:
                if exp not in subs:
                    subs.append(exp)
            if exp.ty in (OP, FUN):
                for arg in exp.args:
                    traverse(arg)
            elif exp.ty in (INTEGRAL, EVAL_AT, DERIV):
                traverse(exp.body)

        traverse(self)
        subs.remove(self)
        return tuple(subs)

    def expand(self):
        """Expand expressions of the form c ^ a."""
        a = Symbol('a', [CONST])
        c = Symbol('c', [OP])
        pat = c ^ a
        subexpr = find_pattern(self, pat)
        expand_expr = self

        for s, _, _ in subexpr:
            base = s.args[0].to_poly()
            exp = s.args[1].val
            if isinstance(exp, int) and exp > 1:
                pw = base
                for i in range(exp - 1):
                    pw = pw * base
                expand_expr = expand_expr.replace(s, from_poly(pw))

        return expand_expr

    def inst_pat(self, mapping: Dict) -> Expr:
        """Instantiate by replacing symbols in term with mapping."""
        if self.is_var() or self.is_const() or self.is_inf():
            return self
        elif self.is_symbol():
            if self.name in mapping:
                return mapping[self.name]
            else:
                return self
        elif self.is_op():
            return Op(self.op, *(arg.inst_pat(mapping) for arg in self.args))
        elif self.is_fun():
            return Fun(self.func_name, *(arg.inst_pat(mapping) for arg in self.args))
        elif self.is_skolem_func():
            return SkolemFunc(self.name, tuple(arg.inst_pat(mapping) for arg in self.dependent_vars))
        elif self.is_integral():
            return Integral(self.var, self.lower.inst_pat(mapping), self.upper.inst_pat(mapping),
                            self.body.inst_pat(mapping))
        elif self.is_evalat():
            return EvalAt(self.var, self.lower.inst_pat(mapping), self.upper.inst_pat(mapping),
                          self.body.inst_pat(mapping))
        elif self.is_deriv():
            return Deriv(self.var, self.body.inst_pat(mapping))
        elif self.is_summation():
            return Summation(self.index_var, self.lower.inst_pat(mapping), self.upper.inst_pat(mapping), \
                             self.body.inst_pat(mapping))
        elif self.is_limit():
            return Limit(self.var, self.lim.inst_pat(mapping), self.body.inst_pat(mapping), self.drt)
        else:
            print(type(self))
            raise NotImplementedError

    def has_var(self, var):
        """Check if var occurs in self"""
        assert isinstance(var, Expr) and var.ty == VAR, \
            "%s is not a var" % var
        if self.ty in (VAR, CONST):
            return self == var
        elif self.ty == SKOLEMFUNC:
            return var in self.dependent_vars
        elif self.ty in (OP, FUN):
            return any(subexpr.has_var(var) for subexpr in self.args)
        elif self.ty == DERIV:
            return self.body.has_var(var)
        elif self.ty == INTEGRAL:
            return self.lower.has_var(var) or self.upper.has_var(var) or \
                   self.body.has_var(var)
        elif self.ty == EVAL_AT:
            return self.var != str(var) and (self.body.has_var(var) or \
                                             self.upper.has_var(var) or self.lower.has_var(var))
        else:
            raise NotImplementedError


def is_polynomial(e):
    """Detect polynomials in x."""
    if e.ty in (VAR, CONST):
        return True
    elif e.ty == OP and e.op in ('+', '-', '*'):
        return all(is_polynomial(arg) for arg in e.args)
    elif e.ty == OP and e.op == '^':
        return is_polynomial(e.args[0]) and e.args[1].ty == CONST and isinstance(e.args[1].val, int)
    else:
        return False


def match(exp: Expr, pattern: Expr) -> Optional[Dict]:
    """Match expr with given pattern.

    If successful, return a dictionary mapping symbols to expressions.
    Otherwise returns None.

    """
    d = dict()

    def rec(exp: Expr, pattern: Expr, bd_vars: Dict[str, str]):
        if isinstance(pattern, Symbol):
            if pattern in d:
                return exp == d[pattern.name]
            # Check exp does not contain bound variables
            for var in exp.get_vars():
                if var in bd_vars.values():
                    return False
            if exp.ty in pattern.pat:
                d[pattern.name] = exp
                return True
            else:
                return False
        if exp.ty != pattern.ty:
            return False
        if exp.is_var():
            return pattern.name == exp.name or \
                (pattern.name in bd_vars and bd_vars[pattern.name] == exp.name)
        elif exp.is_const():
            return pattern.val == exp.val
        elif exp.is_op():
            if exp.op != pattern.op or len(exp.args) != len(pattern.args):
                return False
            for i in range(len(exp.args)):
                if not rec(exp.args[i], pattern.args[i], bd_vars):
                    return False
            return True
        elif exp.is_fun():
            if exp.func_name != pattern.func_name or len(exp.args) != len(pattern.args):
                return False
            for i in range(len(exp.args)):
                if not rec(exp.args[i], pattern.args[i], bd_vars):
                    return False
            return True
        elif exp.is_skolem_func():
            if exp.name != pattern.name or len(exp.dependent_vars) != len(pattern.dependent_vars):
                return False
            for i in range(len(exp.dependent_vars)):
                if not rec(exp.dependent_vars[i], pattern.dependent_vars[i], bd_vars):
                    return False
            return True
        elif exp.is_indefinite_integral():
            # Note this ignores set of skolem arguments
            bd_vars[pattern.var] = exp.var
            res = rec(exp.body, pattern.body, bd_vars)
            del bd_vars[pattern.var]
            return res
        elif exp.is_integral():
            bd_vars[pattern.var] = exp.var
            res1 = rec(exp.upper, pattern.upper, bd_vars)
            res2 = rec(exp.lower, pattern.lower, bd_vars)
            res3 = rec(exp.body, pattern.body, bd_vars)
            del bd_vars[pattern.var]
            return res1 and res2 and res3
        elif exp.is_summation():
            bd_vars[pattern.index_var] = exp.index_var
            res1 = rec(exp.upper, pattern.upper, bd_vars)
            res2 = rec(exp.lower, pattern.lower, bd_vars)
            res3 = rec(exp.body, pattern.body, bd_vars)
            del bd_vars[pattern.index_var]
            return res1 and res2 and res3
        elif exp.is_inf():
            return exp.t == pattern.t
        else:
            # Currently not implemented
            return False

    bd_vars = dict()
    if rec(exp, pattern, bd_vars):
        return d
    else:
        return None


def expr_to_pattern(e: Expr) -> Expr:
    """Convert an expression to pattern."""
    vars = e.get_vars()
    for var in vars:
        e = e.subst(var, Symbol(var, [VAR, CONST, OP, FUN]))
    return e


def find_pattern(expr, pat, transform=None):
    """Find all subexpr can be matched with the given pattern.

    Return a list of: matched expression, location, mapping of symbols.
    If the transform function is provided, first apply it to the mapping
    of symbols.

    """
    c = []

    def rec(e, pat, cur_loc):
        mapping = match(e, pat)
        if mapping:
            if transform is None:
                c.append((e, cur_loc, mapping))
            else:
                c.append((e, cur_loc, transform(mapping)))
        if e.ty in (OP, FUN):
            for i in range(len(e.args)):
                rec(e.args[i], pat, cur_loc + (i,))
        elif e.ty in (INTEGRAL, DERIV, EVAL_AT):
            rec(e.body, pat, cur_loc + (0,))

    rec(expr, pat, tuple())
    return c


def collect_spec_expr(expr, symb):
    c = [p.args[0] for p, _, _ in find_pattern(expr, symb) if len(p.args) != 0]
    return c


def decompose_expr_factor(e):
    """Get production factors from expr.

    """
    if e.ty == OP and e.op == "/":
        e = e.args[0] * Op("^", e.args[1], Const(-1))

    def f(e):
        tmp = []
        if e.ty == OP and e.op == '*':
            tmp.extend(f(e.args[0]))
            tmp.extend(f(e.args[1]))
        elif e.is_uminus():
            tmp.extend(f(e.args[0]))
            tmp.append(Const(-1))
        else:
            tmp.extend([e])
        return copy.copy(tmp)

    return f(e)


def from_const_mono(m: ConstantMonomial) -> Expr:
    """Convert a ConstantMonomial to an expression."""
    factors = []
    for base, power in m.factors:
        if isinstance(base, expr.Expr) and base == E:
            factors.append(exp(Const(power)))
        else:
            if isinstance(base, int):
                base = Const(base)
            if not isinstance(base, expr.Expr):
                raise ValueError
            if power == 1:
                factors.append(base)
            elif power == Fraction(1 / 2):
                factors.append(sqrt(base))
            else:
                factors.append(base ** Const(power))

    if len(factors) == 0:
        return Const(m.coeff)
    elif m.coeff == 1:
        return functools.reduce(operator.mul, factors[1:], factors[0])
    elif m.coeff == -1:
        return - functools.reduce(operator.mul, factors[1:], factors[0])
    else:
        return functools.reduce(operator.mul, factors, Const(m.coeff))


def rsize(e: Expr) -> int:
    if e.is_const():
        return 0
    elif e.is_uminus():
        return rsize(e.args[0])
    elif e.is_times() and e.args[0].is_const():
        return rsize(e.args[1])
    else:
        return e.size()


def from_const_poly(p: ConstantPolynomial) -> Expr:
    """Convert a ConstantPolynomial to an expression."""
    if len(p.monomials) == 0:
        return Const(0)
    else:
        monos = [from_const_mono(m) for m in p.monomials]
        monos = sorted(monos, key=lambda p: rsize(p), reverse=True)
        res = monos[0]
        for mono in monos[1:]:
            if mono.is_uminus():
                res = res - mono.args[0]
            elif mono.is_times() and mono.args[0].is_uminus():
                res = res - mono.args[0].args[0] * mono.args[1]
            elif mono.is_times() and mono.args[0].is_const() and mono.args[0].val < 0:
                res = res - Const(-mono.args[0].val) * mono.args[1]
            elif mono.is_const() and mono.val < 0:
                res = res - Const(-mono.val)
            else:
                res = res + mono
        return res


def from_mono(m: Monomial) -> Expr:
    """Convert a monomial to an expression."""
    factors = []
    for base, power in m.factors:
        if isinstance(base, expr.Expr) and base == E:
            if isinstance(power, poly.Polynomial):
                factors.append(exp(from_poly(power)))
            else:
                factors.append(exp(Const(power)))
        else:
            if power == 1:
                factors.append(base)
            elif power == Fraction(1 / 2):
                factors.append(sqrt(base))
            elif isinstance(power, (int, Fraction)):
                factors.append(base ** Const(power))
            elif isinstance(power, Polynomial):
                factors.append(base ** from_poly(power))
            else:
                raise TypeError("from_mono: unexpected type %s for power" % type(power))

    if len(factors) == 0:
        return from_const_poly(m.coeff)
    elif m.coeff.is_one():
        return functools.reduce(operator.mul, factors[1:], factors[0])
    elif m.coeff.is_minus_one():
        return - functools.reduce(operator.mul, factors[1:], factors[0])
    else:
        return functools.reduce(operator.mul, factors, from_const_poly(m.coeff))


def from_poly(p: Polynomial) -> Expr:
    """Convert a polynomial to an expression."""

    if len(p.monomials) == 0:
        return Const(0)
    else:
        monos = [from_mono(m) for m in p.monomials]
        monos = sorted(monos, key=lambda p: rsize(p), reverse=True)
        res = monos[0]
        for mono in monos[1:]:
            if mono.is_uminus():
                res = res - mono.args[0]
            elif mono.is_times() and mono.args[0].is_uminus():
                res = res - mono.args[0].args[0] * mono.args[1]
            elif mono.is_times() and mono.args[0].is_const() and mono.args[0].val < 0:
                res = res - Const(-mono.args[0].val) * mono.args[1]
            elif mono.is_const() and mono.val < 0:
                res = res - Const(-mono.val)
            else:
                res = res + mono
        return res


def deriv(var: str, e: Expr) -> Expr:
    """Compute the derivative of e with respect to variable
    name var.

    """
    if e.ty == VAR:
        if e.name == var:
            # dx. x = 1
            return Const(1)
        else:
            # dx. y = 0
            return Const(0)
    elif e.ty == CONST:
        # dx. c = 0
        return Const(0)
    elif e.ty == OP:
        if e.op == "+":
            x, y = e.args
            return (deriv(var, x) + deriv(var, y)).normalize()
        elif e.op == "-" and len(e.args) == 2:
            x, y = e.args
            return (deriv(var, x) - deriv(var, y)).normalize()
        elif e.op == "-" and len(e.args) == 1:
            x, = e.args
            return (-(deriv(var, x))).normalize()
        elif e.op == "*":
            x, y = e.args
            if not x.contains_var(var):
                return (x * deriv(var, y)).normalize()
            elif not y.contains_var(var):
                return (deriv(var, x) * y).normalize()
            else:
                return (x * deriv(var, y) + deriv(var, x) * y).normalize()
        elif e.op == "/":
            x, y = e.args
            if not y.contains_var(var):
                # x / c case:
                return (deriv(var, x) / y).normalize()
            elif not x.contains_var(var) and y.ty == OP and y.op == "^":
                # c / (y0 ^ y1): rewrite to c * y0 ^ (-y1)
                return deriv(var, x * (y.args[0] ^ (-y.args[1])))
            else:
                # general case
                return ((deriv(var, x) * y - x * deriv(var, y)) / (y ^ Const(2))).normalize()
        elif e.op == "^":
            x, y = e.args
            if y.ty == CONST:
                return (y * (x ^ Const(y.val - 1)) * deriv(var, x)).normalize()
            elif var not in y.get_vars():
                return (y * (x ^ (y - 1)) * deriv(var, x)).normalize()
            else:
                return deriv(var, exp(y * log(x))).normalize()
        else:
            raise NotImplementedError
    elif e.ty == FUN:
        if e.func_name == "sin":
            x, = e.args
            return (cos(x) * deriv(var, x)).normalize()
        elif e.func_name == "cos":
            x, = e.args
            return (-(sin(x) * deriv(var, x))).normalize()
        elif e.func_name == "tan":
            x, = e.args
            return ((sec(x) ^ Const(2)) * deriv(var, x)).normalize()
        elif e.func_name == "sec":
            x, = e.args
            return (sec(x) * tan(x) * deriv(var, x)).normalize()
        elif e.func_name == "csc":
            x, = e.args
            return (-csc(x) * cot(x) * deriv(var, x)).normalize()
        elif e.func_name == "cot":
            x, = e.args
            return (-(csc(x) ^ Const(2))).normalize()
        elif e.func_name == "cot":
            x, = e.args
            return (-(sin(x) ^ Const(-2)) * deriv(var, x)).normalize()
        elif e.func_name == "log":
            x, = e.args
            return (deriv(var, x) / x).normalize()
        elif e.func_name == "exp":
            x, = e.args
            return (exp(x) * deriv(var, x)).normalize()
        elif e.func_name == "pi":
            return Const(0)
        elif e.func_name == "sqrt":
            if e.args[0].ty == CONST:
                return Const(0)
            else:
                return (deriv(var, e.args[0] ^ Const(Fraction(1 / 2)))).normalize()
        elif e.func_name == "atan":
            x, = e.args
            return (deriv(var, x) / (Const(1) + (x ^ Const(2)))).normalize()
        elif e.func_name == "asin":
            x, = e.args
            return (deriv(var, x) / sqrt(Const(1) - (x ^ Const(2)))).normalize()
        elif e.func_name == "acos":
            x, = e.args
            return -(deriv(var, x) / sqrt(Const(1) - (x ^ Const(2)))).normalize()
        elif e.func_name == "acot":
            x, = e.args
            return (-deriv(var, x)) / (Const(1) + x ^ Const(2)).normalize()
        elif e.func_name == "binom":
            # Arguments should be integers
            assert not e.contains_var(var), "deriv: binom applied to real variables"
            return Const(0)
        else:
            return Deriv(var, e)
    elif e.ty == INTEGRAL:
        return (Integral(e.var, e.lower, e.upper, deriv(var, e.body))
                + e.body.subst(e.var, e.upper) * deriv(var, e.upper)
                - e.body.subst(e.var, e.lower) * deriv(var, e.lower)).normalize()
    elif e.ty == LIMIT:
        return Limit(e.var, e.lim, deriv(var, e.body))
    elif e.ty == SUMMATION:
        return Summation(e.index_var, e.lower, e.upper, deriv(var, e.body))
    elif e.ty == INF:
        return Const(0)
    else:
        print(e)
        raise NotImplementedError


class Var(Expr):
    """Variable."""

    def __init__(self, name: str):
        assert isinstance(name, str)
        self.ty = VAR
        self.name = name

    def __hash__(self):
        return hash((VAR, self.name))

    def __eq__(self, other):
        return isinstance(other, Var) and self.name == other.name

    def __str__(self):
        return self.name

    def __repr__(self):
        return "Var(%s)" % self.name


class Const(Expr):
    """Constants."""

    def __init__(self, val: Union[int, Decimal, Fraction]):
        assert isinstance(val, (int, Decimal, Fraction))
        self.ty = CONST
        if isinstance(val, Decimal):
            val = Fraction(val)
        self.val = val

    def __hash__(self):
        return hash((CONST, self.val))

    def __eq__(self, other):
        return isinstance(other, Const) and self.val == other.val

    def __str__(self):
        return str(self.val)

    def __repr__(self):
        return "Const(%s)" % str(self.val)


class Op(Expr):
    """Operators."""

    def __init__(self, op: str, *args):
        assert isinstance(op, str) and all(isinstance(arg, Expr) for arg in args)
        if len(args) == 1:
            assert op == "-"
        elif len(args) == 2:
            assert op in ["+", "-", "*", "/", "^", "=", "!=", "<", "<=", ">", ">="]
        else:
            raise NotImplementedError
        self.ty = OP
        self.op = op
        self.args = tuple(args)

    def __hash__(self):
        return hash((OP, self.op, tuple(self.args)))

    def __eq__(self, other):
        return isinstance(other, Op) and self.op == other.op and self.args == other.args

    def __str__(self):
        if len(self.args) == 1:
            a, = self.args
            s = str(a)
            if a.priority() < self.priority():
                s = "(%s)" % s
            return "%s%s" % (self.op, s)
        elif len(self.args) == 2:
            a, b = self.args
            if self.op == '/' and a.is_const() and b.is_const() and isinstance(a.val, int) and isinstance(b.val, int):
                return "%s/%s" % (a.val, b.val)
            s1, s2 = str(a), str(b)
            if a.priority() < op_priority[self.op]:
                s1 = "(%s)" % s1
            if b.priority() <= op_priority[self.op]:
                s2 = "(%s)" % s2
            if a.priority() > op_priority[self.op]:
                if a.is_uminus() and self.op == '^':
                    s1 = "(%s)" % s1
            return "%s %s %s" % (s1, self.op, s2)
        else:
            raise NotImplementedError

    def __repr__(self):
        return "Op(%s,%s)" % (self.op, ",".join(repr(arg) for arg in self.args))


class Fun(Expr):
    """Functions."""

    def __init__(self, func_name: str, *args):
        assert isinstance(func_name, str) and all(isinstance(arg, Expr) for arg in args)

        self.ty = FUN
        self.func_name = func_name
        self.args = tuple(args)

    def __hash__(self):
        return hash((FUN, self.func_name, self.args))

    def __eq__(self, other):
        return isinstance(other, Fun) and self.func_name == other.func_name and self.args == other.args

    def __str__(self):
        if len(self.args) > 0:
            return "%s(%s)" % (self.func_name, ",".join(str(arg) for arg in self.args))
        else:
            return self.func_name

    def __repr__(self):
        if len(self.args) > 0:
            return "Fun(%s,%s)" % (self.func_name, ",".join(repr(arg) for arg in self.args))
        else:
            return "Fun(%s)" % self.func_name


class Limit(Expr):
    """Limit expression.

    - var: variable which approaches the limit
    - lim: variable
    - body: expression
    - dir: limit side

    """

    def __init__(self, var: str, lim: Expr, body: Expr, drt=None):
        assert isinstance(var, str) and isinstance(lim, Expr) and isinstance(body, Expr), \
            "Illegal expression: %s %s %s" % (type(var), type(lim), type(body))
        self.ty = LIMIT
        self.var = var
        self.lim = lim
        self.body = body
        self.drt = drt

    def __eq__(self, other):
        return isinstance(other, Limit) and other.var == self.var and \
               other.drt == self.drt and self.lim == other.lim and \
               self.body == other.body

    def __hash__(self):
        return hash((LIMIT, self.var, self.lim, self.body, self.drt))

    def __str__(self):
        if self.lim == inf() or self.lim == neg_inf():
            return "LIM {%s -> %s}. %s" % (self.var, self.lim, self.body)
        else:
            return "LIM {%s -> %s %s}. %s" % (self.var, self.lim, self.drt if self.drt != None else "", self.body)

    def __repr__(self):
        if self.lim == inf() or self.lim == neg_inf():
            return "Limit(%s, %s, %s)" % (self.var, self.lim, self.body)
        else:
            return "Limit(%s, %s%s, %s)" % (self.var, self.lim, "" if self.drt == None else self.drt \
                                                , self.body)

    def is_indeterminate_form(self):
        # determine wether e is a indeterminate form
        var, body, lim, drt = self.var, self.body.normalize(), self.lim, self.drt
        if self.drt == None:
            if body.is_constant():
                return False
            elif body.is_times():
                l = [a.subst(var, lim).normalize() for a in body.args]
                # 0 * INF or INF * 0
                if l[0].is_zero() and l[1].is_INF() or l[1].is_zero() and l[0].is_INF():
                    return True
            elif body.is_fun():
                if body.func_name in ('sin', 'cos'):
                    a0 = body.args[0]
                    if a0.subst(var, lim).is_const():
                        return False
            else:
                return False
        else:
            raise NotImplementedError


class Inf(Expr):
    """The infinity."""

    def __init__(self, t):
        assert t in (Decimal("inf"), Decimal("-inf"))
        self.ty = INF
        self.t = t

    def __str__(self):
        if self.t == Decimal("inf"):
            return "oo"
        else:
            return "-oo"

    def __repr__(self):
        return "Inf(%s)" % self.t

    def __hash__(self):
        return hash((INF, self.t))

    def __eq__(self, other):
        return isinstance(other, Inf) and self.t == other.t

    def keys(self):
        return ('ty', 't')

    def __getitem__(self, item):
        return getattr(self, item)


class Differential(Expr):
    """Differential of an expression."""

    def __init__(self, body: Expr):
        assert isinstance(body, Expr)
        self.body = body
        self.ty = DIFFERENTIAL

    def __hash__(self):
        return hash((DIFFERENTIAL, self.body))

    def __eq__(self, other):
        return isinstance(other, Differential) and self.body == other.body

    def __str__(self):
        return "DIFF. %s" % str(self.body)

    def __repr__(self):
        return "Differential(%s)" % repr(self.body)


class SkolemFunc(Expr):
    """Skolem variable or function"""
    def __init__(self, name, dep_vars: Tuple[Expr]):
        self.ty = SKOLEMFUNC
        self.name = name
        self.dependent_vars = tuple(dep_vars)

    def __eq__(self, other):
        return isinstance(other, SkolemFunc) and \
            self.dependent_vars == other.dependent_vars and self.name == other.name

    def __str__(self):
        if not self.dependent_vars:
            return "SKOLEM_CONST(" + self.name + ")"
        else:
            return "SKOLEM_FUNC(" + self.name + "(" + ", ".join(str(var) for var in self.dependent_vars) + "))"

    def __hash__(self):
        return hash((self.name, tuple(self.dependent_vars), self.ty))


NEG_INF = Inf(Decimal('-inf'))
POS_INF = Inf(Decimal('inf'))
ZERO = Const(0)

def inf():
    return Inf(Decimal("inf"))

def neg_inf():
    return Inf(Decimal("-inf"))

def sin(e):
    return Fun("sin", e)

def cos(e):
    return Fun("cos", e)

def tan(e):
    return Fun("tan", e)

def cot(e):
    return Fun("cot", e)

def sec(e):
    return Fun("sec", e)

def csc(e):
    return Fun("csc", e)

def log(e):
    return Fun("log", e)

def exp(e):
    return Fun("exp", e)

def arcsin(e):
    return Fun("asin", e)

def arccos(e):
    return Fun("acos", e)

def arctan(e):
    return Fun("atan", e)

def sqrt(e):
    return Fun("sqrt", e)


def binom(e1: Expr, e2: Expr) -> Expr:
    """Binomial coefficients"""
    return Fun("binom", e1, e2)


def factorial(e: Expr) -> Expr:
    """Factorial of e"""
    return Fun('factorial', e)


pi = Fun("pi")
E = Fun("exp", Const(1))


def Eq(s: Expr, t: Expr) -> Expr:
    return Op("=", s, t)


class Deriv(Expr):
    """Derivative of an expression."""

    def __init__(self, var: str, body: Expr):
        assert isinstance(var, str) and isinstance(body, Expr)
        self.ty = DERIV
        self.var: str = var
        self.body: Expr = body

    def __hash__(self):
        return hash((DERIV, self.var, self.body))

    def __eq__(self, other):
        return isinstance(other, Deriv) and self.var == other.var and self.body == other.body

    def __str__(self):
        return "D %s. %s" % (self.var, str(self.body))

    def __repr__(self):
        return "Deriv(%s,%s)" % (self.var, repr(self.body))


class IndefiniteIntegral(Expr):
    """Indefinite integral of an expression."""

    def __init__(self, var: str, body: Expr, skolem_args: Tuple[str]):
        assert isinstance(var, str) and isinstance(body, Expr)
        self.ty = INDEFINITEINTEGRAL
        self.var = var
        self.body = body
        self.skolem_args = tuple(skolem_args)

    def __hash__(self):
        return hash((INDEFINITEINTEGRAL, self.var, self.body, self.skolem_args))

    def __eq__(self, other):
        return isinstance(other, IndefiniteIntegral) and self.body == other.alpha_convert(self.var).body and \
            self.skolem_args == other.skolem_args

    def __str__(self):
        if self.skolem_args:
            return "INT %s [%s]. %s" % (self.var, ', '.join(self.skolem_args), self.body)
        else:
            return "INT %s. %s" % (self.var, self.body)

    def __repr__(self):
        return "IndefiniteIntegral(%s,%s,%s)" % (self.var, repr(self.body), self.skolem_args)

    def alpha_convert(self, new_name: str):
        """Change the variable of integration to new_name."""
        assert isinstance(new_name, str), "alpha_convert"
        return IndefiniteIntegral(new_name, self.body.subst(self.var, Var(new_name)), self.skolem_args)


class Integral(Expr):
    """Integral of an expression."""

    def __init__(self, var: str, lower: Expr, upper: Expr, body: Expr):
        assert isinstance(var, str) and isinstance(lower, Expr) and \
               isinstance(upper, Expr) and isinstance(body, Expr)
        self.ty = INTEGRAL
        self.var = var
        self.lower = lower
        self.upper = upper
        self.body = body

    def __hash__(self):
        return hash((INTEGRAL, self.var, self.lower, self.upper, self.body))

    def __eq__(self, other):
        return isinstance(other, Integral) and self.lower == other.lower and self.upper == other.upper and \
               self.body == other.alpha_convert(self.var).body

    def __str__(self):
        return "INT %s:[%s,%s]. %s" % (self.var, str(self.lower), str(self.upper), str(self.body))

    def __repr__(self):
        return "Integral(%s,%s,%s,%s)" % (self.var, repr(self.lower), repr(self.upper), repr(self.body))

    def alpha_convert(self, new_name):
        """Change the variable of integration to new_name."""
        assert isinstance(new_name, str), "alpha_convert"
        return Integral(new_name, self.lower, self.upper, self.body.subst(self.var, Var(new_name)))


class EvalAt(Expr):
    """Evaluation at upper and lower, then subtract."""

    def __init__(self, var: str, lower: Expr, upper: Expr, body: Expr):
        assert isinstance(var, str) and isinstance(lower, Expr) and \
               isinstance(upper, Expr) and isinstance(body, Expr)
        self.ty = EVAL_AT
        self.var = var
        self.lower = lower
        self.upper = upper
        self.body = body

    def __hash__(self):
        return hash((EVAL_AT, self.var, self.lower, self.upper, self.body))

    def __eq__(self, other):
        return isinstance(other, EvalAt) and self.var == other.var and \
               self.lower == other.lower and self.upper == other.upper and self.body == other.body

    def __str__(self):
        return "[%s]_%s=%s,%s" % (str(self.body), self.var, str(self.lower), str(self.upper))

    def __repr__(self):
        return "EvalAt(%s,%s,%s,%s)" % (self.var, repr(self.lower), repr(self.upper), repr(self.body))


class Symbol(Expr):
    """Pattern expression.
    
    It can be used to find expression with the given specific structure.
    
    """
    def __init__(self, name: str, pat: List[str]):
        self.ty = SYMBOL
        self.name = name
        self.pat = tuple(pat)

    def __eq__(self, other):
        return isinstance(other, Symbol) and self.name == other.name and self.pat == other.pat

    def __hash__(self):
        return hash((SYMBOL, self.name, self.ty, sum(self.pat)))

    def __str__(self):
        return "?%s" % self.name

    def __repr__(self):
        return "Symbol(%s, %s)" % (self.name, self.pat)


class Summation(Expr):
    """Summation of integers over some range."""
    def __init__(self, index_var: str, lower: Expr, upper: Expr, body: Expr):
        self.ty = SUMMATION
        self.index_var: str = index_var
        self.lower: Expr = lower
        self.upper: Expr = upper
        self.body: Expr = body

    def __str__(self):
        return "SUM(" + self.index_var + ", " + str(self.lower) + ", " + str(self.upper) + ", " + str(self.body) + ")"

    def __eq__(self, other):
        return isinstance(other, Summation) and self.index_var == other.index_var and \
               self.lower == other.lower and \
               self.upper == other.upper and \
               self.body == other.body

    def __hash__(self):
        return hash((SUMMATION, self.index_var, self.ty, self.lower, self.upper, self.body))

    def alpha_convert(self, new_var: str):
        """Rename the bound variable of a summation."""
        assert isinstance(new_var, str), "alpha_convert"
        return Summation(new_var, self.lower, self.upper, self.body.subst(self.index_var, Var(new_var)))


def eval_expr(e: Expr):
    if e.is_inf():
        if e == expr.POS_INF:
            return float('inf')
        else:
            return float('-inf')
    elif e.is_const():
        return e.val
    elif e.is_plus():
        return eval_expr(e.args[0]) + eval_expr(e.args[1])
    elif e.is_uminus():
        return -eval_expr(e.args[0])
    elif e.is_minus():
        return eval_expr(e.args[0]) - eval_expr(e.args[1])
    elif e.is_times():
        return eval_expr(e.args[0]) * eval_expr(e.args[1])
    elif e.is_divides():
        return eval_expr(e.args[0]) / eval_expr(e.args[1])
    elif e.is_power():
        return eval_expr(e.args[0]) ** eval_expr(e.args[1])
    elif e.is_fun():
        if e.func_name == 'sqrt':
            return math.sqrt(eval_expr(e.args[0]))
        elif e.func_name == 'exp':
            return math.exp(eval_expr(e.args[0]))
        elif e.func_name == 'abs':
            return abs(eval_expr(e.args[0]))
        elif e.func_name == 'pi':
            return math.pi
        elif e.func_name == 'sin':
            return math.sin(eval_expr(e.args[0]))
        elif e.func_name == 'cos':
            return math.cos(eval_expr(e.args[0]))
        elif e.func_name == 'tan':
            return math.tan(eval_expr(e.args[0]))
        elif e.func_name == 'cot':
            return 1.0 / math.tan(eval_expr(e.args[0]))
        elif e.func_name == 'sec':
            return 1.0 / math.cos(eval_expr(e.args[0]))
        elif e.func_name == 'csc':
            return 1.0 / math.sin(eval_expr(e.args[0]))
        elif e.func_name == 'asin':
            return math.asin(eval_expr(e.args[0]))
        elif e.func_name == 'acos':
            return math.acos(eval_expr(e.args[0]))
        elif e.func_name == 'atan':
            return math.atan(eval_expr(e.args[0]))

    print(e)
    raise NotImplementedError


def neg_expr(ex: Expr):
    if ex.is_op() and ex.op == '=':
        return Op('!=', *ex.args)
    else:
        raise NotImplementedError
