"""Expressions."""

import copy
import math
import functools
from decimal import Decimal
from fractions import Fraction
from collections.abc import Iterable
from typing import Dict, List, Optional, Set, TypeGuard, Tuple, Union, Callable


VAR, CONST, OP, FUN, DERIV, INTEGRAL, EVAL_AT, SYMBOL, LIMIT, INF, INDEFINITEINTEGRAL, DIFFERENTIAL, \
SKOLEMFUNC, SUMMATION = range(14)

op_priority = {
    "+": 65, "-": 65, "*": 70, "/": 70, "^": 75, "=": 50, "<": 50, ">": 50, "<=": 50, ">=": 50, "!=": 50
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

    def is_odd(self, var, conds) -> bool:
        from integral import poly
        tmp1 = self
        tmp2 = self.subst(var, -Var(var))
        if poly.normalize(tmp1 + tmp2, conds) == Const(0):
            return True
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
    def lhs(self) -> "Expr":
        if self.is_equals():
            return self.args[0]
        else:
            raise AssertionError("lhs: term is not an equality")

    @property
    def rhs(self) -> "Expr":
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
        elif self.is_deriv() or self.is_indefinite_integral():
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
        elif self.is_limit():
            return (self.var, self.lim, self.body, self.drt) <= (other.var, other.lim, other.body, other.drt)
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

    def get_subexpr(self, loc) -> "Expr":
        """Given an expression, return the subexpression at location."""
        if not isinstance(loc, Location):
            loc = Location(loc)
        if loc.is_empty():
            return self
        elif self.is_var() or self.is_const():
            raise AssertionError("get_subexpr: invalid location")
        elif self.is_op() or self.is_fun():
            assert loc.head < len(self.args), "get_subexpr: invalid location"
            return self.args[loc.head].get_subexpr(loc.rest)
        elif self.is_deriv():
            assert loc.head == 0, "get_subexpr: invalid location"
            return self.body.get_subexpr(loc.rest)
        elif self.is_integral() or self.is_evalat():
            if loc.head == 0:
                return self.body.get_subexpr(loc.rest)
            elif loc.head == 1:
                return self.lower.get_subexpr(loc.rest)
            elif loc.head == 2:
                return self.upper.get_subexpr(loc.rest)
            else:
                raise AssertionError("get_subexpr: invalid location")
        elif self.is_limit():
            assert loc.head == 0, "get_subexpr: invalid location"
            return self.body.get_subexpr(loc.rest)

        else:
            raise NotImplementedError

    def replace_expr(self, loc, new_expr: "Expr") -> "Expr":
        """Replace self's subexpr at location."""
        if not isinstance(loc, Location):
            loc = Location(loc)
        if loc.is_empty():
            return new_expr
        elif self.is_var() or self.is_const():
            raise AssertionError("replace_expr: invalid location")
        elif self.is_op():
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
        elif self.is_fun():
            assert loc.head < len(self.args), "replace_expr: invalid location"
            arg = self.args[loc.head].replace_expr(loc.rest, new_expr)
            return Fun(self.func_name, arg)
        elif self.is_integral():
            if loc.head == 0:
                return Integral(self.var, self.lower, self.upper, self.body.replace_expr(loc.rest, new_expr))
            elif loc.head == 1:
                return Integral(self.var, self.lower.replace_expr(loc.rest, new_expr), self.upper, self.body)
            elif loc.head == 2:
                return Integral(self.var, self.lower, self.upper.replace_expr(loc.rest, new_expr), self.body)
            else:
                raise AssertionError("replace_expr: invalid location")
        elif self.is_evalat():
            if loc.head == 0:
                return EvalAt(self.var, self.lower, self.upper, self.body.replace_expr(loc.rest, new_expr))
            elif loc.head == 1:
                return EvalAt(self.var, self.lower.replace_expr(loc.rest, new_expr), self.upper, self.body)
            elif loc.head == 2:
                return EvalAt(self.var, self.lower, self.upper.replace_expr(loc.rest, new_expr), self.body)
            else:
                raise AssertionError("replace_expr: invalid location")
        elif self.is_deriv():
            assert loc.head == 0, "replace_expr: invalid location"
            return Deriv(self.var, self.body.replace_expr(loc.rest, new_expr))
        elif self.is_limit():
            assert loc.head == 0, "replace_expr: invalid location"
            return Limit(self.var, self.limit, self.body.replace_expr(loc.rest, new_expr))
        else:
            raise NotImplementedError

    def get_location(self) -> Location:
        """Returns the location at which the 'selected' field is True."""
        location = []

        def get(exp: Expr, loc=''):
            if hasattr(exp, 'selected') and exp.selected == True:
                location.append(loc[1:])
                exp.selected = False  # Once it is found, restore it.
            elif exp.is_op() or exp.is_fun():
                for i in range(len(exp.args)):
                    get(exp.args[i], loc + "." + str(i))
            elif exp.is_integral() or exp.is_evalat():
                get(exp.lower, loc + ".1")
                get(exp.upper, loc + ".2")
                get(exp.body, loc + ".0")
            elif exp.is_deriv() or exp.is_summation() or exp.is_limit():
                get(exp.body, loc + ".0")

        get(self)
        return location[0]

    def find_subexpr(self, subexpr: "Expr") -> List[Location]:
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
    
    def find_subexpr_pred(self, pred: Callable[["Expr"], bool]) -> List[Tuple["Expr", Location]]:
        """Find list of subexpressions satisfying a given predicate."""
        results = []

        def find(e: Expr, loc: Location):
            if pred(e):
                results.append((e, Location(loc)))
            if e.is_op() or e.is_fun():
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
        return results

    def subst(self, var: str, e: "Expr") -> "Expr":
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
            return any([arg.has_symbol() for arg in self.args])
        elif isinstance(self, Summation):
            return self.body.has_symbol()
        elif isinstance(self, Limit):
            return self.body.has_symbol() or self.lim.has_symbol()
        else:
            print(self)
            raise NotImplementedError

    def contains_var(self, x: str) -> bool:
        """Whether self contains variable x."""
        assert isinstance(x, str)
        return x in self.get_vars()

    def replace(self, e: "Expr", repl_e: "Expr") -> "Expr":
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

    def separate_integral(self) -> List[Tuple["Expr", Location]]:
        """Collect the list of all integrals appearing in self."""
        return self.find_subexpr_pred(
            lambda e: e.is_integral() or e.is_indefinite_integral())

    def separate_limits(self) -> List[Tuple["Expr", Location]]:
        """Collect the list of all integrals appearing in self."""
        return self.find_subexpr_pred(lambda e: e.is_limit())

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

    def inst_pat(self, mapping: Dict) -> "Expr":
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
            if pattern.name in d:
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
        e = e.subst(var, Symbol(var, [VAR, CONST, OP, FUN, INTEGRAL]))
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
    """Get production factors from expr."""
    num_factors, denom_factors = [], []
    def rec(e: Expr, sign):
        if e.is_times():
            rec(e.args[0], sign)
            rec(e.args[1], sign)
        elif e.is_uminus():
            num_factors.append(Const(-1))
            rec(e.args[0], sign)
        elif e.is_divides():
            rec(e.args[0], sign)
            rec(e.args[1], -1 * sign)
        elif sign == 1:
            num_factors.append(e)
        else:
            denom_factors.append(e)
    rec(e, 1)
    return num_factors, denom_factors

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
            return "LIM {%s -> %s %s}. %s" % (
                self.var, self.lim, self.drt if self.drt != None else "", self.body)

    def __repr__(self):
        if self.lim == inf() or self.lim == neg_inf():
            return "Limit(%s, %s, %s)" % (self.var, self.lim, self.body)
        else:
            return "Limit(%s, %s%s, %s)" % (
                self.var, self.lim, "" if self.drt == None else self.drt, self.body)


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
G = Fun("G")


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

        if isinstance(other, Summation):
            if self.index_var == other.index_var:
                return self.lower == other.lower and \
                self.upper == other.upper and \
                self.body == other.body
            else:
                return other.alpha_convert(self.index_var) == self
        return False

    def __hash__(self):
        return hash((SUMMATION, self.index_var, self.ty, self.lower, self.upper, self.body))

    def alpha_convert(self, new_var: str):
        """Rename the bound variable of a summation."""
        assert isinstance(new_var, str), "alpha_convert"
        return Summation(new_var, self.lower, self.upper, self.body.subst(self.index_var, Var(new_var)))


def eval_expr(e: Expr):
    if e.is_inf():
        if e == POS_INF:
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
