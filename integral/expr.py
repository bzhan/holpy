"""Expressions."""

import copy
import functools, operator
from typing import Dict, List, Optional, Set, TypeGuard, Tuple
from sympy import solveset, re, Interval, Eq, EmptySet
from sympy.simplify.fu import *
from sympy.parsing import sympy_parser
from sympy.ntheory.factor_ import factorint

from kernel.type import RealType
from kernel import term
from kernel.term import TFun
from logic.conv import ConvException
from data import real
from data import set as hol_set
from integral import parser
from integral import poly
from integral.poly import *

evalat = term.Const('evalat', TFun(TFun(RealType, RealType), RealType, RealType, RealType))
real_derivative = term.Const('real_derivative', TFun(TFun(RealType, RealType), RealType, RealType))
real_integral = term.Const('real_integral', TFun(hol_set.setT(RealType), TFun(RealType, RealType), RealType))

VAR, CONST, OP, FUN, DERIV, INTEGRAL, EVAL_AT, SYMBOL, LIMIT, INF, INDEFINITEINTEGRAL, DIFFERENTIAL, \
SKOLEMFUNC, SUMMATION = range(14)

op_priority = {
    "+": 65, "-": 65, "*": 70, "/": 70, "^": 75, "=": 50, "<": 50, ">": 50, "<=": 50, ">=": 50, "!=": 50
}

trig_identity = []


def is_square(r):
    return math.sqrt(r) * math.sqrt(r) == r


sin_table = {
    "0": "0",
    "1/6 * pi": "1/2",
    "1/4 * pi": "1/2 * sqrt(2)",
    "1/3 * pi": "1/2 * sqrt(3)",
    "1/2 * pi": "1",
    "2/3 * pi": "1/2 * sqrt(3)",
    "3/4 * pi": "1/2 * sqrt(2)",
    "5/6 * pi": "1/2",
    "pi": "0"
}

cos_table = {
    "0": "1",
    "1/6 * pi": "1/2 * sqrt(3)",
    "1/4 * pi": "1/2 * sqrt(2)",
    "1/3 * pi": "1/2",
    "1/2 * pi": "0",
    "2/3 * pi": "-1/2",
    "3/4 * pi": "-1/2 * sqrt(2)",
    "5/6 * pi": "-1/2 * sqrt(3)",
    "pi": "-1"
}

tan_table = {
    "0": "0",
    "1/6 * pi": "1/3 * sqrt(3)",
    "1/4 * pi": "1",
    "1/3 * pi": "sqrt(3)",
    "2/3 * pi": "-sqrt(3)",
    "3/4 * pi": "-1",
    "5/6 * pi": "-1/3 * sqrt(3)",
    "pi": "0"
}

cot_table = {
    "1/6 * pi": "sqrt(3)",
    "1/4 * pi": "1",
    "1/3 * pi": "1/3 * sqrt(3)",
    "1/2 * pi": "0",
    "2/3 * pi": "-1/3 * sqrt(3)",
    "3/4 * pi": "-1",
    "5/6 * pi": "-sqrt(3)",
}

csc_table = {
    "1/6 * pi": "2",
    "1/4 * pi": "sqrt(2)",
    "1/3 * pi": "2/3 * sqrt(3)",
    "1/2 * pi": "1",
    "2/3 * pi": "2/3 * sqrt(3)",
    "3/4 * pi": "sqrt(2)",
    "5/6 * pi": "2",
}

sec_table = {
    "0": "1",
    "1/6 * pi": "2/3 * sqrt(3)",
    "1/4 * pi": "sqrt(2)",
    "1/3 * pi": "2",
    "2/3 * pi": "-2",
    "3/4 * pi": "-sqrt(2)",
    "5/6 * pi": "-2/3 * sqrt(3)",
    "pi": "-1"
}

asin_table = {
    "-1": "-1/2 * pi",
    "-1/2 * sqrt(3)": "-1/3 * pi",
    "-1/2 * sqrt(2)": "-1/4 * pi",
    "-1/2": "-1/6 * pi",
    "0": "0",
    "1/2": "1/6 * pi",
    "1/2 * sqrt(2)": "1/4 * pi",
    "1/2 * sqrt(3)": "1/3 * pi",
    "1": "1/2 * pi",
}

atan_table = {
    "-sqrt(3)": "-1/3 * pi",
    "-1": "-1/4 * pi",
    "-1/3 * sqrt(3)": "-1/6 * pi",
    "0": "0",
    "1/3 * sqrt(3)": "1/6 * pi",
    "1": "1/4 * pi",
    "sqrt(3)": "1/3 * pi",
}

acsc_table = {
    "-2": "-1/6 * pi",
    "-sqrt(2)": "-1/4 * pi",
    "-2/3 * sqrt(3)": "-1/3 * pi",
    "-1": "-1/2 * pi",
    "1": "1/2 * pi",
    "2/3 * sqrt(3)": "1/3 * pi",
    "sqrt(2)": "1/4 * pi",
    "2": "1/6 * pi",
}


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

    def is_var(self) -> bool:
        return self.ty == VAR

    def is_diff(self) -> bool:
        return self.ty == DIFFERENTIAL

    def is_const(self) -> bool:
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
        tmp = self.normalize()
        return tmp.is_const() and tmp.val == 0

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

    def is_odd_function(self, var: str):
        if self.is_constant():
            return False
        elif self.is_var():
            if self.name != var:
                return False
            else:
                return True
        elif self.is_times():
            a1, a2 = self.args
            if a1.is_even_function(var) and a2.is_even_function(var):
                return False
            elif a1.is_even_function(var) and a2.is_odd_function(var):
                return True
            elif a1.is_odd_function(var) and a2.is_even_function(var):
                return True
            elif a1.is_odd_function(var) and a2.is_odd_function(var):
                return False
            else:
                raise False
        else:
            raise NotImplementedError

    def is_even_function(self, var: str):
        if self.is_constant():
            return True
        elif self.is_var():
            if self.name != var:
                return True
            else:
                return False
        elif self.is_times():
            a1, a2 = self.args
            if a1.is_even_function(var) and a2.is_even_function(var):
                return True
            elif a1.is_even_function(var) and a2.is_odd_function(var):
                return False
            elif a1.is_odd_function(var) and a2.is_even_function(var):
                return False
            elif a1.is_odd_function(var) and a2.is_odd_function(var):
                return True
            else:
                raise False
        elif self.is_plus():
            a1, a2 = self.args
            if a1.is_even_function(var) and a2.is_even_function(var):
                return True
            else:
                raise NotImplementedError
        elif self.is_power():
            a1, a2 = self.args
            if a2.is_constant():
                if a2.is_const():
                    if a2.val == -1:
                        return a1.is_even_function(var)
                    elif a2.val == 2:
                        return a1.is_even_function(var) or a1.is_odd_function(var)
                    else:
                        raise NotImplementedError
                else:
                    raise NotImplementedError
            else:
                raise NotImplementedError
        elif self.is_fun():
            if self.func_name == 'abs':
                if self.args[0].is_even_function(var) or self.args[0].is_odd_function(var):
                    return True
                else:
                    raise NotImplementedError
            elif self.func_name == 'cos':
                if self.args[0].is_even_function(var) or self.args[0].is_odd_function(var):
                    return True
                else:
                    raise NotImplementedError
            elif self.func_name == 'sqrt':
                a = self.args[0]
                if a.is_even_function(var):
                    return True
                else:
                    return False
            elif self.func_name == 'sin':
                a = self.args[0]
                if a.is_even_function:
                    return True
                else:
                    return False
            else:
                raise NotImplementedError
        else:
            raise NotImplementedError

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
        
    def is_summation(self):
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

        if self.ty == VAR:
            return self.name <= other.name
        elif self.ty == CONST:
            return self.val <= other.val
        elif self.ty == OP:
            return (self.op, self.args) <= (other.op, other.args)
        elif self.ty == FUN:
            return (self.func_name, self.args) <= (other.func_name, other.args)
        elif self.ty == DERIV:
            return (self.body, self.var) <= (other.body, other.var)
        elif self.ty == INTEGRAL or self.ty == EVAL_AT:
            return (self.body, self.lower, self.upper, self.var) <= \
                   (other.body, other.lower, other.upper, other.var)
        elif self.ty == SYMBOL:
            return sum(self.ty) <= sum(other.ty)
        else:
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

    def get_subexpr(self, loc):
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

    def replace_expr(self, loc, new_expr):
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

    def get_location(self):
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

        def find(e, loc: Location):
            if e == subexpr:
                locations.append(Location(loc))
            elif e.ty == OP or e.ty == FUN:
                for i, arg in enumerate(e.args):
                    find(arg, loc.append(i))
            elif e.ty == INTEGRAL or e.ty == EVAL_AT:
                find(e.lower, loc.append(1))
                find(e.upper, loc.append(2))
                find(e.body, loc.append(0))
            elif e.ty == DERIV or e.ty == LIMIT or e.ty == INDEFINITEINTEGRAL:
                find(e.body, loc.append(0))
            elif e.ty == SUMMATION:
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
        """Determine whether expr is a number."""
        if self.ty == CONST:
            return True
        elif self.ty == VAR:
            return False
        elif self.ty == FUN:
            return all(arg.is_constant() for arg in self.args)
        elif self.ty == OP:
            return all(arg.is_constant() for arg in self.args)
        else:
            return False

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
        return x in self.get_vars()

    def replace(self, e: Expr, repl_e: Expr) -> Expr:
        """Replace occurrences of e with repl_e."""
        assert isinstance(e, Expr) and isinstance(repl_e, Expr)
        if self == e:
            return repl_e
        elif self.ty in (VAR, CONST, INF):
            return self
        elif self.ty == OP:
            return Op(self.op, *[arg.replace(e, repl_e) for arg in self.args])
        elif self.ty == FUN:
            return Fun(self.func_name, *[arg.replace(e, repl_e) for arg in self.args])
        elif self.ty == DERIV:
            return Deriv(self.var, self.body.replace(e, repl_e))
        elif self.ty == INTEGRAL:
            return Integral(self.var, self.lower.replace(e, repl_e), self.upper.replace(e, repl_e),
                            self.body.replace(e, repl_e))
        elif self.ty == EVAL_AT:
            return EvalAt(self.var, self.lower.replace(e, repl_e), self.upper.replace(e, repl_e),
                          self.body.replace(e, repl_e))
        elif self.ty == SKOLEMFUNC:
            return SkolemFunc(self.name, tuple(var.replace(e, repl_e) for var in self.dependent_vars))
        elif self.ty == SUMMATION:
            return Summation(self.index_var, self.lower, self.upper, self.body.replace(e, repl_e))
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
            table = trig_table()[self.func_name]
            norm_a = norm_a.normalize_constant()
            if norm_a in table:
                return table[norm_a].to_const_poly()
            elif match(norm_a, c * pi) and norm_a.args[0].val < 0:
                neg_norm_a = Const(-norm_a.args[0].val) * pi
                if neg_norm_a in table:
                    if self.func_name in ('sin', 'tan', 'cot', 'csc'):
                        val = -table[neg_norm_a]
                    else:
                        val = table[neg_norm_a]
                    return val.to_const_poly()
                else:
                    return poly.const_singleton(self)
            else:
                return poly.const_singleton(Fun(self.func_name, norm_a))

        elif self.ty == FUN and self.func_name in ('asin', 'acos', 'atan', 'acot', 'acsc', 'asec'):
            a = self.args[0].to_const_poly()
            norm_a = from_const_poly(a)
            table = inverse_trig_table()[self.func_name]
            if norm_a in table:
                return table[norm_a].to_const_poly()
            else:
                return poly.const_singleton(self)

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

    def norm(self):
        return self.normalize()

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

        elif self.ty == FUN and self.func_name == "pi":
            return poly.singleton(self)

        elif self.ty == FUN and self.func_name == "abs":
            if self.args[0].normalize().ty == CONST:
                return poly.constant(Const(abs(self.args[0].normalize().val)).to_const_poly())
            return poly.singleton(Fun("abs", self.args[0].normalize()))

        elif self.ty == FUN and self.func_name == "binom":
            return poly.singleton(Fun("binom", self.args[0].normalize(), self.args[1].normalize()))

        elif self.ty == FUN and self.func_name == "factorial":
            return poly.singleton(Fun("factorial", self.args[0].normalize()))

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
        elif self.is_limit():
            if self.lim == POS_INF:
                from integral import limits
                res = limits.limit_of_expr(self.body, self.var)
                if res.e != None:
                    return res.e
            elif self.lim == NEG_INF:
                from integral import limits
                res = limits.limit_of_expr(self.body.subst(self.var, -Var(self.var)), self.var)
                if res.e != None:
                    return res.e
        return from_poly(self.to_poly())

    def replace_trig(self, trig_old: Expr, trig_new: Expr):
        """Replace trigonometric expression with its equivalent form in e.

        Compared to regular substitution, it makes special consideration of
        powers in trig_old. For example, if original expression is sin(x)^4,
        trig_old is sin(x)^2 and trig_new is 1-cos(x)^2, then the returned
        result is (1-cos(x)^2)^2.

        """
        assert isinstance(trig_old, Expr) and isinstance(trig_new, Expr)
        if self == trig_old:
            return trig_new

        if self.ty == OP:
            if len(self.args) == 1:
                new_arg = self.args[0].replace_trig(trig_old, trig_new)
                return Op(self.op, new_arg)
            elif len(self.args) == 2:
                if self.op == "^" and trig_old.ty == OP and trig_old.op == "^" \
                        and self.args[0] == trig_old.args[0]:
                    # The main additional case
                    return Op(self.op, trig_new, (self.args[1] / trig_old.args[1]).normalize())
                else:
                    new_arg1 = self.args[0].replace_trig(trig_old, trig_new)
                    new_arg2 = self.args[1].replace_trig(trig_old, trig_new)
                    return Op(self.op, new_arg1, new_arg2)
            else:
                raise NotImplementedError
        elif self.ty == FUN:
            if len(self.args) > 0:
                new_args = [arg.replace_trig(trig_old, trig_new) for arg in self.args]
                return Fun(self.func_name, *new_args)
            else:
                return self
        elif self.ty == INTEGRAL:
            body = self.body.replace_trig(trig_old, trig_new)
            return Integral(self.var, self.lower, self.upper, body)
        elif self.ty == LIMIT:
            body = self.body.replace_trig(trig_old, trig_new)
            return Limit(self.var, self.lim, body)
        else:
            return self

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

    def separate_integral(self):
        """Collect the list of all integrals appearing in self."""
        result = []

        def collect(p: Expr, result):
            if p.is_integral() or p.is_indefinite_integral():
                p.selected = True
                loc = self.get_location()
                del p.selected
                result.append([p, loc])
            elif p.ty == OP:
                for arg in p.args:
                    collect(arg, result)
            elif p.ty == LIMIT:
                collect(p.body, result)
            elif p.ty == DERIV:
                collect(p.body, result)

        collect(self, result)
        return result

    def separate_binom(self):
        """Collect the list of all binomial coeffcients appearing in self."""
        result = []

        def collect(p, result):
            if p.ty == FUN and p.func_name == 'binom':
                p.selected = True
                loc = self.get_location()
                del p.selected
                result.append([p, loc])
            elif p.ty in (OP, FUN):
                for arg in p.args:
                    collect(arg, result)

        collect(self, result)
        return result

    def separate_limit(self):
        """Collect the list of all limits appearing in self."""
        result = []

        def collect(p, result):
            if p.ty == LIMIT:
                p.selected = True
                loc = self.get_location()
                result.append([p, loc])
            elif p.ty == OP:
                for arg in p.args:
                    collect(arg, result)

        collect(self, result)
        return result

    def separate_abs(self):
        """Collect the list of all integral of abs expressions and abs expressions appearing in self."""
        result = []

        def collect(p, result):
            if p.ty == INTEGRAL and p.body.ty == FUN and p.body.func_name == 'abs':
                p.selected = True
                loc = self.get_location()
                result.append([p, loc])
            elif p.ty == FUN and p.func_name == 'abs':
                p.selected = True
                loc = self.get_location()
                result.append([p, loc])
            elif p.ty == OP:
                for arg in p.args:
                    collect(arg, result)

        collect(self, result)
        return result

    def separate_exp(self):
        """Collect the list of all exponential expressions appearing in self."""
        result = []

        def collect(p, result):
            if p.ty == FUN and p.func_name == 'exp':
                p.selected = True
                loc = self.get_location()
                result.append([p, loc])
            elif p.ty == OP:
                for arg in p.args:
                    collect(arg, result)
            elif p.ty == INTEGRAL:
                collect(p.lower, result)
                collect(p.upper, result)
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

    def ranges(self, var, lower, upper):
        """Find list of intervals where the expression is greater/less than zero."""
        e = sympy_style(self)
        var = sympy_style(var)
        lower = sympy_style(lower)
        upper = sympy_style(upper)
        greater_zero = solveset(re(e) > 0, var, Interval(lower, upper, left_open=True, right_open=True))
        smaller_zero = Interval(lower, upper, left_open=True, right_open=True) - greater_zero

        # Convert results SymPy's solveset into holpy style.
        def to_holpy(l):
            if isinstance(l, sympy.Union):
                return [(holpy_style(x.start), holpy_style(x.end)) for x in l.args]
            elif isinstance(l, Interval):
                return [(holpy_style(l.start), holpy_style(l.end))]
            elif l == EmptySet:
                return []
            else:
                raise NotImplementedError

        g, s = to_holpy(greater_zero), to_holpy(smaller_zero)

        # Because sympy use e represent exp, so need to convert it to exp(1).
        def e_exp(e):
            return Fun("exp", Const(1)) if e == Var("E") else e

        g = [(e_exp(i), e_exp(j)) for i, j in g]
        s = [(e_exp(i), e_exp(j)) for i, j in s]
        return g, s

    def get_abs(self):
        """Collect all absolute value in expression."""
        abs_value = []

        def abs_collect(expr):
            if expr.ty == FUN and expr.func_name == "abs":
                abs_value.append(expr)
            elif expr.ty in (OP, FUN):
                for arg in expr.args:
                    abs_collect(arg)
            elif expr.ty in (INTEGRAL, EVAL_AT, DERIV):
                abs_collect(expr.body)

        abs_collect(self)
        return abs_value

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
                expand_expr = expand_expr.replace_trig(s, from_poly(pw))

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


def sympy_style(s):
    """Transform expr to sympy object."""
    return sympy_parser.parse_expr(str(s).replace("^", "**"))


def holpy_style(s):
    """Transform sympy object to expr."""
    return parser.parse_expr(str(s).replace("**", "^")).replace_trig(Var("E"), Fun("exp", Const(1)))


def factor_polynomial(e):
    """Factorize a polynomial expr."""
    return holpy_style(sympy.factor(sympy_style(e)))


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


def trig_transform(trig: Expr, var: str, rule_list=None):
    """Compute all possible trig function equal to trig"""
    poss = set()
    poss_expr = set()
    if trig.ty == CONST:
        poss.add((trig * ((sin(Var(var)) ^ Const(2)) + (cos(Var(var)) ^ Const(2))), "TR0"))
        return poss
    i = sympy_parser.parse_expr(str(trig).replace("^", "**"))
    for rule_name, (f, rule) in trigFun.items():
        if rule_list is not None and f not in rule_list:
            continue
        j = f(sympy_parser.parse_expr(str(trig).replace("^", "**")))
        if i != j and j not in poss_expr:
            poss.add((holpy_style(j), f.__name__))
            poss_expr.add(j)
    poss.add((holpy_style(i), "Unchanged"))
    return poss


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


def decompose_expr_add(e: Expr) -> List[Expr]:
    """Decompose expression into a sum of expressions.

    Recognize +, - (unary and binary).

    Example:
        a + b - c -> [a, b, -c]

    """
    def f(e):
        tmp = []
        if e.is_plus():
            tmp.extend(f(e.args[0]))
            tmp.extend(f(e.args[1]))
        elif e.is_uminus():
            tmp.extend([-item for item in f(e.args[0])])
        elif e.is_minus():
            tmp.extend(f(e.args[0]))
            tmp.extend([-item for item in f(e.args[1])])
        else:
            tmp.extend([e])
        return copy.copy(tmp)

    return f(e)


def decompose_expr_factor(e):
    """Get production factors from expr.

    """
    factors = []
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
    # return factors


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
            if a.ty == CONST and a.val > 0:
                return "(%s%s)" % (self.op, s)
            if a.priority() < self.priority():
                s = "(%s)" % s
            return "%s%s" % (self.op, s)
        elif len(self.args) == 2:
            a, b = self.args
            s1, s2 = str(a), str(b)
            if a.priority() < op_priority[self.op]:
                s1 = "(%s)" % s1
            if b.priority() <= op_priority[self.op]:
                s2 = "(%s)" % s2
            if a.priority() > op_priority[self.op]:
                if a.ty == OP and a.is_uminus() and self.op == '^':
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

    def lim_to_inf(self):
        """
        Convert the limit to oo, e.g. LIM {x -> 0+}. 1/x will be
        converted to LIM {x -> oo}. x.

        """
        lim = self.lim.normalize()
        v = Var(self.var)
        if lim == inf():
            bd = self.body
        elif lim == neg_inf():
            bd = self.body.replace_trig(v, -self.var)
        elif self.drt == "+":
            bd = self.body.replace_trig(v, self.lim + 1 / v)
        elif self.drt == "-":
            bd = self.body.replace_trig(v, self.lim - 1 / v)
        else:
            raise NotImplementedError("dir must be + or -.")

        return Limit(self.var, inf, bd.normalize())


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


def sec(e):
    return Fun("sec", e)


def cos(e):
    return Fun("cos", e)


def csc(e):
    return Fun("csc", e)


def tan(e):
    return Fun("tan", e)


def cot(e):
    return Fun("cot", e)


def log(e):
    return Fun("log", e)


def exp(e):
    return Fun("exp", e)


def arcsin(e):
    return Fun("asin", e)


def arctan(e):
    return Fun("atan", e)


def arccos(e):
    return Fun("acos", e)


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


trigFun = {
    "TR0": (TR0, "1 to sin^2 + cos^2"),
    "TR1": (TR1, "sec-csc to cos-sin"),
    "TR2": (TR2, "tan-cot to sin-cos ratio"),
    "TR2i": (TR2i, "sin-cos ratio to tan"),
    "TR3": (TR3, "angle canonicalization"),
    "TR4": (TR4, "functions at special angles"),
    "TR5": (TR5, "powers of sin to powers of cos"),
    "TR6": (TR6, "powers of cos to powers of sin"),
    "TR7": (TR7, "reduce cos power (increase angle)"),
    "TR8": (TR8, "expand products of sin-cos to sums"),
    "TR9": (TR9, "contract sums of sin-cos to products"),
    "TR10": (TR10, "separate sin-cos arguments"),
    "TR10i": (TR10i, "collect sin-cos arguments"),
    "TR11": (TR11, "reduce double angles"),
    "TR12": (TR12, "separate tan arguments"),
    "TR12i": (TR12i, "collect tan arguments"),
    "TR13": (TR13, "expand product of tan-cot"),
    "TR14": (TR14, "factored powers of sin or cos to cos or sin power"),
    "TR15": (TR15, "negative powers of sin to cot power"),
    "TR16": (TR16, "negative powers of cos to tan power"),
    "TR22": (TR22, "tan-cot powers to negative powers of sec-csc functions"),
    "TR111": (TR111, "negative sin-cos-tan powers to csc-sec-cot"),
}

trig_table_cache = None


def trig_table():
    """Trigonometric value table on 0,pi/6,pi/4,pi/3,pi/2,(2/3)*pi,(3/4)*pi,(5/6)*pi,pi."""
    global trig_table_cache
    if trig_table_cache is None:
        trig_table_cache = {
            "sin": {parser.parse_expr(key): parser.parse_expr(value) for key, value in sin_table.items()},
            "cos": {parser.parse_expr(key): parser.parse_expr(value) for key, value in cos_table.items()},
            "tan": {parser.parse_expr(key): parser.parse_expr(value) for key, value in tan_table.items()},
            "cot": {parser.parse_expr(key): parser.parse_expr(value) for key, value in cot_table.items()},
            "csc": {parser.parse_expr(key): parser.parse_expr(value) for key, value in csc_table.items()},
            "sec": {parser.parse_expr(key): parser.parse_expr(value) for key, value in sec_table.items()},
        }
    return trig_table_cache


inverse_trig_table_cache = None


def inverse_trig_table():
    """Inverse trigonometric value table."""
    global inverse_trig_table_cache
    if inverse_trig_table_cache is None:
        inverse_trig_table_cache = {
            "asin": {parser.parse_expr(key): parser.parse_expr(value) for key, value in asin_table.items()},
            "acos": {parser.parse_expr(value): parser.parse_expr(key) for key, value in cos_table.items()},
            "atan": {parser.parse_expr(key): parser.parse_expr(value) for key, value in atan_table.items()},
            "acot": {parser.parse_expr(value): parser.parse_expr(key) for key, value in cot_table.items()},
            "acsc": {parser.parse_expr(key): parser.parse_expr(value) for key, value in acsc_table.items()},
            "asec": {parser.parse_expr(value): parser.parse_expr(key) for key, value in sec_table.items()},
        }
    return inverse_trig_table_cache


def expr_to_holpy(expr: Expr) -> term.Term:
    """Convert an expression to holpy term."""
    assert isinstance(expr, Expr), "expr_to_holpy"
    if expr.is_var():
        return term.Var(expr.name, RealType)
    elif expr.is_const():
        return term.Real(expr.val)
    elif expr.is_op():
        if expr.op == '-' and len(expr.args) == 1:
            return -(expr_to_holpy(expr.args[0]))

        if len(expr.args) != 2:
            raise NotImplementedError

        a, b = [expr_to_holpy(arg) for arg in expr.args]
        if expr.op == '+':
            return a + b
        elif expr.op == '-':
            return a - b
        elif expr.op == '*':
            return a * b
        elif expr.op == '/':
            return a / b
        elif expr.op == '^':
            if expr.args[1].is_const() and isinstance(expr.args[1].val, int) and expr.args[1].val >= 0:
                return a ** term.Nat(expr.args[1].val)
            else:
                return a ** b
        else:
            raise NotImplementedError
    elif expr.is_fun():
        if expr.func_name == 'pi':
            return real.pi

        if len(expr.args) != 1:
            raise NotImplementedError

        a = expr_to_holpy(expr.args[0])
        if expr.func_name == 'sin':
            return real.sin(a)
        elif expr.func_name == 'cos':
            return real.cos(a)
        elif expr.func_name == 'tan':
            return real.tan(a)
        elif expr.func_name == 'cot':
            return real.cot(a)
        elif expr.func_name == 'sec':
            return real.sec(a)
        elif expr.func_name == 'csc':
            return real.csc(a)
        elif expr.func_name == 'log':
            return real.log(a)
        elif expr.func_name == 'exp':
            return real.exp(a)
        elif expr.func_name == 'abs':
            return real.hol_abs(a)
        elif expr.func_name == 'sqrt':
            return real.sqrt(a)
        elif expr.func_name == 'atan':
            return real.atn(a)
        else:
            raise NotImplementedError
    elif expr.is_deriv():
        raise NotImplementedError
    elif expr.is_integral():
        a, b = expr_to_holpy(expr.lower), expr_to_holpy(expr.upper)
        var = term.Var(expr.var, RealType)
        f = term.Lambda(var, expr_to_holpy(expr.body))
        return real_integral(real.closed_interval(a, b), f)
    elif expr.is_evalat():
        a, b = expr_to_holpy(expr.lower), expr_to_holpy(expr.upper)
        var = term.Var(expr.var, RealType)
        f = term.Lambda(var, expr_to_holpy(expr.body))
        return evalat(f, a, b)
    else:
        print("expr_to_holpy: unknown expression %s" % expr)
        raise NotImplementedError


def holpy_to_expr(t: term.Term) -> Expr:
    """Convert a HOL term to expression."""
    assert isinstance(t, term.Term), "holpy_to_expr"
    if t.is_var():
        if t.T == RealType:
            return Var(t.name)
        else:
            raise NotImplementedError
    elif t == real.pi:
        return pi
    elif t.is_number():
        val = t.dest_number()
        return Const(val)
    elif t.is_plus():
        return holpy_to_expr(t.arg1) + holpy_to_expr(t.arg)
    elif t.is_minus():
        return holpy_to_expr(t.arg1) - holpy_to_expr(t.arg)
    elif t.is_uminus():
        return -holpy_to_expr(t.arg)
    elif t.is_times():
        return holpy_to_expr(t.arg1) * holpy_to_expr(t.arg)
    elif t.is_divides():
        return holpy_to_expr(t.arg1) / holpy_to_expr(t.arg)
    elif t.is_nat_power() and t.arg.is_number():
        return holpy_to_expr(t.arg1) ** t.arg.dest_number()
    elif t.is_real_power():
        return holpy_to_expr(t.arg1) ** holpy_to_expr(t.arg)
    elif t.is_comb('sqrt', 1):
        return sqrt(holpy_to_expr(t.arg))
    elif t.is_comb('abs', 1):
        return Fun('abs', holpy_to_expr(t.arg))
    elif t.is_comb('exp', 1):
        return exp(holpy_to_expr(t.arg))
    elif t.is_comb('log', 1):
        return log(holpy_to_expr(t.arg))
    elif t.is_comb('sin', 1):
        return sin(holpy_to_expr(t.arg))
    elif t.is_comb('cos', 1):
        return cos(holpy_to_expr(t.arg))
    elif t.is_comb('tan', 1):
        return tan(holpy_to_expr(t.arg))
    elif t.is_comb('cot', 1):
        return cot(holpy_to_expr(t.arg))
    elif t.is_comb('sec', 1):
        return sec(holpy_to_expr(t.arg))
    elif t.is_comb('csc', 1):
        return csc(holpy_to_expr(t.arg))
    else:
        raise NotImplementedError


def eval_hol_expr(t: term.Term):
    """Evaluate an HOL term of type real.

    First try the exact evaluation with real_eval. If that fails, fall back
    to approximate evaluation with real_approx_eval.

    """
    try:
        res = real.real_eval(t)
    except ConvException:
        res = real.real_approx_eval(t)

    return res


def eval_expr(e: Expr):
    t = expr_to_holpy(e)
    return eval_hol_expr(t)


def neg_expr(ex: Expr):
    if ex.is_op() and ex.op == '=':
        return Op('!=', *ex.args)
    else:
        raise NotImplementedError


def add(items) -> Expr:
    if len(items) == 1:
        return items[0]
    res = items[0]
    for item in items[1:]:
        res = res + item
    return res