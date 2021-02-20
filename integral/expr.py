"""Expressions."""

from fractions import Fraction
import functools, operator
from collections.abc import Iterable
import copy
from sympy import solveset, re, Interval, Eq, Union, EmptySet, pexquo
from sympy.simplify.fu import *
from sympy.parsing import sympy_parser
from numbers import Number

from kernel.type import RealType
from kernel import term
from kernel.term import TFun
from data import real
from data import set
from integral import parser
from integral import poly
from integral.poly import *

evalat = term.Const('evalat', TFun(TFun(RealType, RealType), RealType, RealType, RealType))
real_derivative = term.Const('real_derivative', TFun(TFun(RealType, RealType), RealType, RealType))
real_integral = term.Const('real_integral', TFun(set.setT(RealType), TFun(RealType, RealType), RealType))


VAR, CONST, OP, FUN, DERIV, INTEGRAL, EVAL_AT, ABS, SYMBOL = range(9)

op_priority = {
    "+": 65, "-": 65, "*": 70, "/": 70, "^": 75
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
        if self.ty in (VAR, CONST, SYMBOL):
            return 1
        elif self.ty in (OP, FUN):
            return 1 + sum(arg.size() for arg in self.args)
        elif self.ty == DERIV:
            return 1 + self.body.size()
        elif self.ty in (INTEGRAL, EVAL_AT):
            return 1 + self.lower.size() + self.upper.size() + self.body.size()
        else:
            raise NotImplementedError

    def is_var(self):
        return self.ty == VAR

    def is_const(self):
        return self.ty == CONST

    def is_op(self):
        return self.ty == OP

    def is_fun(self):
        return self.ty == FUN

    def is_deriv(self):
        return self.ty == DERIV

    def is_integral(self):
        return self.ty == INTEGRAL

    def is_evalat(self):
        return self.ty == EVAL_AT

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
        # elif self.is_constant() and other.is_constant():
        #     return sympy_parser.parse_expr(str(self - other).replace("^", "**")) <= 0
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
            print(self)
            print(type(self))
            print(self.ty)
            raise NotImplementedError

    def __lt__(self, other):
        return self <= other and self != other

    def __gt__(self, other):
        return other <= self and self != other

    def __ge__(self, other):
        return not self < other

    def priority(self):
        if self.ty in (VAR, SYMBOL):
            return 100
        elif self.ty == CONST:
            if isinstance(self.val, Fraction):
                return op_priority['/']
            elif self.val < 0:
                return 80  # priority of uminus
            else:
                return 100
        elif self.ty == OP:
            if len(self.args) == 1:
                return 80  # priority of uminus
            elif self.op in op_priority:
                return op_priority[self.op]
            else:
                raise NotImplementedError
        elif self.ty == FUN:
            return 95
        elif self.ty in (DERIV, INTEGRAL, EVAL_AT):
            return 10

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
            assert loc.head < len(self.args), "get_subexpr: invalid location"
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
                raise AssertionError("get_subexpr: invalid location")
        elif self.ty == EVAL_AT:
            if loc.head == 0:
                return EvalAt(self.var, self.lower, self.upper, self.body.replace_expr(loc.rest, new_expr))
            elif loc.head == 1:
                return EvalAt(self.var, self.lower.replace_expr(loc.rest, new_expr), self.upper, self.body)
            elif loc.head == 2:
                return EvalAt(self.var, self.lower, self.upper.replace_expr(loc.rest, new_expr), self.body)
            else:
                raise AssertionError("get_subexpr: invalid location")
        elif self.ty == DERIV:      
            assert loc.head == 0, "get_subexpr: invalid location"
            return Deriv(self.var, self.body.replace_expr(loc.rest, new_expr))
        else:
            raise NotImplementedError

    def get_location(self):
        """Returns the location at which the 'selected' field is True."""
        location = []
        def get(exp, loc = ''):
            if hasattr(exp, 'selected') and exp.selected == True:
                location.append(loc[1:])
                exp.selected = False #Once it is found, restore it.
            elif exp.ty == OP or exp.ty == FUN:
                for i in range(len(exp.args)):
                    get(exp.args[i], loc+"."+str(i))
            elif exp.ty == INTEGRAL or exp.ty == EVAL_AT:
                get(exp.lower, loc+".1")
                get(exp.upper, loc+".2")
                get(exp.body, loc+".0")
            elif exp.ty == DERIV:
                get(exp.body, loc+".0")
        get(self)
        return location[0]

    def subst(self, var, e):
        """Substitute occurrence of var for e in self."""
        assert isinstance(var, str) and isinstance(e, Expr)
        if self.ty == VAR:
            if self.name == var:
                return e
            else:
                return self
        elif self.ty == CONST:
            return self
        elif self.ty == OP:
            return Op(self.op, *[arg.subst(var, e) for arg in self.args])
        elif self.ty == FUN:
            return Fun(self.func_name, *[arg.subst(var, e) for arg in self.args])
        else:
            raise NotImplementedError
    
    def is_constant(self):
        """Determine whether expr is a number."""
        if self.ty == CONST:
            return True
        elif self.ty == VAR:
            return False
        elif self.ty == FUN:
            if len(self.args) == 0: # pi
                return True
            else:
                return self.args[0].is_constant()
        elif self.ty == OP:
            return all(arg.is_constant() for arg in self.args)
        else:
            return False

    def replace(self, e, repl_e):
        """Replace occurrences of e with repl_e."""
        assert isinstance(e, Expr) and isinstance(repl_e, Expr)
        if self == e:
            return repl_e
        elif self.ty in (VAR, CONST):
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
        else:
            raise NotImplementedError

    def to_const_poly(self):
        """Normalize a constant expression.
        
        Assume self.is_constant() = True in this function.
        
        """
        if self.ty == VAR:
            raise ValueError

        elif self.ty == CONST:
            return poly.const_fraction(self.val)

        elif self.ty == OP and self.op == '+':
            return self.args[0].to_const_poly() + self.args[1].to_const_poly()
        
        elif self.ty == OP and self.op == '-':
            if len(self.args) == 1:
                return -self.args[0].to_const_poly()
            else:
                return self.args[0].to_const_poly() - self.args[1].to_const_poly()

        elif self.ty == OP and self.op == '*':
            return self.args[0].to_const_poly() * self.args[1].to_const_poly()

        elif self.ty == OP and self.op == '/':
            a, b = self.args[0].to_const_poly(), self.args[1].to_const_poly()
            if b.is_monomial():
                return a / b
            else:
                return a / poly.const_singleton(from_const_poly(b))

        elif self.ty == OP and self.op == '^':
            a, b = self.args[0].to_const_poly(), self.args[1].to_const_poly()
            if a.is_monomial() and b.is_fraction():
                return a ** b.get_fraction()
            elif b.is_fraction():
                rb = b.get_fraction()
                if rb > 0 and int(rb) == rb:
                    res = poly.const_fraction(1)
                    for i in range(int(rb)):
                        res *= a
                    return res
                else:
                    return poly.const_singleton(self)
            else:
                return poly.const_singleton(self)

        elif self.ty == FUN and self.func_name == 'sqrt':
            a = self.args[0].to_const_poly()
            if a.is_fraction() and is_square(a.get_fraction()):  # is square
                return poly.const_fraction(Fraction(math.sqrt(a.get_fraction())))
            elif a.is_monomial():
                return a ** Fraction(1/2)
            else:
                return poly.const_singleton(sqrt(from_const_poly(a)))

        elif self.ty == FUN and self.func_name == 'pi':
            return poly.ConstantPolynomial([poly.ConstantMonomial(1, [(pi, 1)])])

        elif self.ty == FUN and self.func_name == 'exp':
            a = self.args[0].to_const_poly()
            if a.is_fraction() and a.get_fraction() == 0:
                return poly.const_fraction(1)
            elif a.is_fraction():
                return poly.ConstantPolynomial([poly.ConstantMonomial(1, [(E, a.get_fraction())])])
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
                    return sum(log_factors, poly.const_singleton(log(Const(mono.coeff))))
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
                    norm_a = Const(x.val - (n+1)) * pi if n > 0 else Const(x.val - (n-1)) * pi
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
            else:
                return poly.const_singleton(self)

        else:
            raise NotImplementedError

    def normalize_constant(self):
        return from_const_poly(self.to_const_poly())

    def to_poly(self):
        """Convert expression to polynomial."""
        if self.ty == VAR:
            return poly.singleton(self)

        elif self.is_constant():
            return poly.constant(self.to_const_poly())
        
        elif self.ty == OP and self.op == "+":
            return self.args[0].to_poly() + self.args[1].to_poly()
        
        elif self.ty == OP and self.op == "-":
            if len(self.args) == 1:
                return -self.args[0].to_poly()
            else:
                return self.args[0].to_poly() - self.args[1].to_poly()

        elif self.ty == OP and self.op == "*":
            return self.args[0].to_poly() * self.args[1].to_poly()
        
        elif self.ty == OP and self.op == "/":
            a, b = self.args[0].to_poly(), self.args[1].to_poly()
            if b.is_monomial():
                return a / b
            else:
                return a / poly.singleton(from_poly(b))
        
        elif self.ty == OP and self.op == "^":
            a, b = self.args[0].to_poly(), self.args[1].to_poly()
            if a.is_monomial() and b.is_fraction():
                return a ** b.get_fraction()
            elif b.is_fraction():
                return poly.Polynomial([poly.Monomial(poly.const_fraction(1), [(from_poly(a), b.get_fraction())])])
            else:
                return poly.const_singleton(self)

        elif self.ty == FUN and self.func_name == "exp":
            a, = self.args
            if a.ty == FUN and a.func_name == "log":
                return a.args[0].to_poly()
            else:
                return poly.Polynomial([poly.Monomial(poly.const_fraction(1), [(E, a.to_poly())])])

        elif self.ty == FUN and self.func_name in ("sin", "cos", "tan", "cot", "csc", "sec"):
            a, = self.args
            if a.ty == FUN and a.func_name == "a" + self.func_name:
                # sin(asin(x)) = x
                return a.args[0].to_poly()
            else:
                return poly.singleton(Fun(self.func_name, a.normalize()))

        elif self.ty == FUN and self.func_name in ("asin","acos","atan","acot","acsc","asec"):
            a, = self.args
            if self.func_name in ("atan","acot") and a.ty == FUN and a.func_name == self.func_name[1:]:
                # atan(tan(x)) = x
                return a.args[0].to_poly()
            else:
                return poly.singleton(Fun(self.func_name, a.normalize()))

        elif self.ty == FUN and self.func_name == "log":
            a, = self.args
            if a.ty == FUN and a.func_name == "exp":
                return a.args[0].to_poly()
            else:
                return poly.singleton(log(a.normalize()))

        elif self.ty == FUN and self.func_name == "sqrt":
            return Op("^", self.args[0], Const(Fraction(1, 2))).to_poly()

        elif self.ty == FUN and self.func_name == "pi":
            return poly.singleton(self)

        elif self.ty == FUN and self.func_name == "abs":
            if self.args[0].normalize().ty == CONST:
                return poly.constant(Const(abs(self.args[0].normalize().val)))
            return poly.singleton(Fun("abs", self.args[0].normalize()))

        elif self.ty == EVAL_AT:
            upper = self.body.subst(self.var, self.upper)
            lower = self.body.subst(self.var, self.lower)
            return (upper.normalize() - lower.normalize()).to_poly()

        elif self.ty == INTEGRAL:
            if self.lower == self.upper:
                return poly.constant(Const(0))
            body = self.body.normalize()
            return poly.singleton(Integral(self.var, self.lower.normalize(), self.upper.normalize(), body))

        else:
            return poly.singleton(self)
    
    def normalize(self):
        return from_poly(self.to_poly())

    def replace_trig(self, trig_old, trig_new):
        """Replace the old trig to its identity trig in e."""
        assert isinstance(trig_new, Expr)
        if self == trig_old:
            return trig_new
        else:
            """Note: The old trig must exist in self.
            """
            if self.ty == OP:
                if len(self.args) == 1:
                    new_arg = self.args[0].replace_trig(trig_old, trig_new)
                    return Op(self.op, new_arg)
                elif len(self.args) == 2:
                    if self.op == "^" and trig_old.ty == OP and trig_old.op == "^" \
                      and self.args[0] == trig_old.args[0]:
                        # expr : x ^ 4 trig_old x ^ 2 trig_new u => u ^ 2
                        return Op(self.op, trig_new, (self.args[1] / trig_old.args[1]).normalize())
                    new_arg1 = self.args[0].replace_trig(trig_old, trig_new)
                    new_arg2 = self.args[1].replace_trig(trig_old, trig_new)
                    return Op(self.op, new_arg1, new_arg2)
                else:
                    return self
            elif self.ty == FUN:
                if len(self.args) > 0:
                    new_arg = self.args[0].replace_trig(trig_old, trig_new)
                    return Fun(self.func_name, new_arg)
                else:
                    return self
            elif self.ty == INTEGRAL:
                body = self.body.replace_trig(trig_old, trig_new)
                return Integral(self.var, self.lower, self.upper, body)
            else:
                return self

    def separate_integral(self):
        """Find all integrals in expr."""
        result = []
        def collect(expr, result):
            if expr.ty == INTEGRAL:
                expr.selected = True
                loc = self.get_location()
                result.append([expr, loc])
            elif expr.ty == OP:
                for arg in expr.args:
                    collect(arg, result)

        collect(self, result)
        return result
    
    def findVar(self):
        """Find variable in expr for substitution's derivation.
            Most used in trig functions substitute initial variable.
        """
        v = []
        def findv(e, v):
            if e.ty == VAR:
                v.append(e)
            elif e.ty == FUN:
                #cos(u) => u
                for arg in e.args:
                    findv(arg, v)
            elif e.ty == OP:
                for arg in e.args:
                    findv(arg, v)
        findv(self, v)
        return v

    @property
    def depth(self):
        """ Return the depth of expression. 
            Help to estimate problem difficulty.
        """
        def d(expr):
            if expr.ty in (VAR, CONST):
                return 0
            elif expr.ty in (OP, FUN):
                if len(expr.args) == 0:#pi
                    return 1
                return 1 + max([d(expr.args[i]) for i in range(len(expr.args))])
            elif expr.ty in (EVAL_AT, INTEGRAL, DERIV):
                return d(expr.body)
            elif expr.ty == SYMBOL:
                raise TypeError
        return d(self)

    def ranges(self, var, lower, upper):
        """Find expression where greater and smaller than zero in the interval: lower, upper"""
        e = sympy_style(self)
        var = sympy_style(var)
        lower = sympy_style(lower)
        upper = sympy_style(upper)
        greater_zero = solveset(re(e) > 0, var, Interval(lower, upper, left_open = True, right_open = True))
        smaller_zero = solveset(re(e) < 0, var, Interval(lower, upper, left_open = True, right_open = True))
        def to_holpy(l):
            if isinstance(l, Union):
                return [(holpy_style(x.start), holpy_style(x.end)) for x in l.args]
            elif isinstance(l, Interval):
                return [(holpy_style(l.start), holpy_style(l.end))]
            elif l == EmptySet:
                return []
            else:
                raise NotImplementedError
        g, s = to_holpy(greater_zero), to_holpy(smaller_zero)
        def e_exp(e):
            """Because sympy use e represent exp, so need to convert it to exp(1)."""
            return Fun("exp", Const(1)) if e == Var("E") else e
        g = [(e_exp(i), e_exp(j)) for i, j in g]
        s = [(e_exp(i), e_exp(j)) for i, j in s]
        return g, s

    def getAbsByMonomial(self):
        """Separate abs from monomial"""
        p = self.to_poly()
        if len(p.monomials) == 1 and len(self.getAbs()) <= 1: #Only separate 
            a = []
            b = []
            for f in p.monomials[0].factors:
                if f[0].ty == FUN and f[0].func_name == "abs":
                    a.append((f[0], 1))
                else:
                    b.append(f)
            am = from_mono(poly.Monomial(Const(1), a)) #terms with abs
            bm = from_mono(poly.Monomial(p.monomials[0].coeff, b)) #terms not with abs
            return am
        else:
            return Const(1)

    def getAbs(self):
        """Collect all absolute value in expression."""
        abs_value = []
        def abs_collect(expr):
            if expr.ty == FUN and expr.func_name == "abs":
                abs_value.append(expr)
            elif expr.ty == OP or expr.ty == FUN and expr.func_name != "abs":
                for arg in expr.args:
                    abs_collect(arg)
            elif expr.ty == INTEGRAL or expr.ty == EVAL_AT or expr.ty == DERIV:
                abs_collect(expr.body)
        abs_collect(self)
        return abs_value

    def is_spec_function(self, fun_name):
        """Return true iff e is formed by rational options of fun_name."""
        v = Symbol("v", [VAR,OP,FUN])
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

    def pre_order_pat(self):
        """Traverse the tree node in preorder and return its pattern."""
        pat = []
        def preorder(e):
            pat.append(e.ty)
            if e.ty in (OP, FUN):
                for arg in e.args:
                    preorder(arg)
            elif e.ty in (INTEGRAL, EVAL_AT):
                preorder(e.body)
        preorder(self)
        return pat

    def nonlinear_subexpr(self):
        """Return nonlinear & nonconstant subexpression."""
        subs = set()
        a = Symbol('a', [CONST])
        b = Symbol('b', [CONST])
        x = Symbol('x', [VAR])
        patterns = [a * x, a*x +b, a*x - b, x, b + a*x, a + x, x + a]
        def traverse(exp):
            table = [match(exp, p) for p in patterns]
            is_linear = functools.reduce(lambda x, y: x or y, table)
            if not exp.is_constant() and not is_linear:
                subs.add(exp)
            if exp.ty in (OP, FUN):
                for arg in exp.args:
                    traverse(arg)
            elif exp.ty in (INTEGRAL, EVAL_AT, DERIV):
                traverse(exp.body)
        traverse(self)
        subs.discard(self)
        return tuple(subs)

    def expand(self):
        """Expand the power expression.
        
        """
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
                for i in range(exp-1):
                    pw = pw * base
                expand_expr = expand_expr.replace_trig(s, from_poly(pw))

        return expand_expr

    def is_univariate(self, var=False):
        """Determine polynomial is whether univariate.
        
        If there is unique f(x) occurs in polynomial, it is univariate.
        
        If self is univariate and var is true, also return the variate.
        """
        d = set()
    
        def rec(e):
            if e.ty == VAR:
                d.add(e)
            elif e.ty == OP:
                for arg in e.args:
                    rec(arg)
            elif e.ty == FUN:
                d.add(e)
            elif e.ty not in (VAR, CONST, FUN, OP):
                return False
            
        rec(self)
        if len(d) == 1:
            return True if not var else d.pop()
        else:
            return len(d) <= 1

    def is_multivariate(self):
        """Determine whether expr has a * f(x)^k + b * g(x) ^ m + c * h(y) ^ n form
        
        """
        return not self.is_univariate()

    def inst_pat(self, mapping):
        """Instantiate by replacing symbols in term with mapping."""
        if self.ty in (VAR, CONST):
            return self
        elif self.ty == SYMBOL:
            assert self in mapping, "inst_pat: %s not found" % self.name
            return mapping[self]
        elif self.ty == OP:
            return Op(self.op, *(arg.inst_pat(mapping) for arg in self.args))
        elif self.ty == FUN:
            return Fun(self.func_name, *(arg.inst_pat(mapping) for arg in self.args))
        elif self.ty == INTEGRAL:
            return Integral(self.var, self.lower.inst_pat(mapping), self.upper.inst_pat(mapping),
                            self.body.inst_pat(mapping))
        elif self.ty == EVAL_AT:
            return EvalAt(self.var, self.lower.inst_pat(mapping), self.upper.inst_pat(mapping),
                          self.body.inst_pat(mapping))
        elif self.ty == DERIV:
            return Deriv(self.var, self.body.inst_pat(mapping))
        else:
            raise NotImplementedError


def sympy_style(s):
    """Transform expr to sympy object."""
    return sympy_parser.parse_expr(str(s).replace("^", "**"))

def holpy_style(s):
    """Transform sympy object to expr."""
    return parser.parse_expr(str(s).replace("**", "^")).replace_trig(Var("E"), Fun("exp", Const(1)))

def trig_transform(trig, var, rule_list=None):
    """Compute all possible trig function equal to trig"""
    poss = set()
    poss_expr = set()
    if trig.ty == CONST:
        poss.add((trig * ((sin(Var(var)) ^ Const(2)) + (cos(Var(var))^Const(2))), "TR0"))
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

def match(exp, pattern):
    """Match expr with given pattern. 
    
    If successful, return a dictionary mapping symbols to expressions.
    Otherwise returns None.

    """
    d = dict()
    def rec(exp, pattern):
        if not isinstance(pattern, Symbol) and exp.ty != pattern.ty:
            return None
        if exp.ty == VAR:
            if pattern.ty == VAR and pattern.name == exp.name:
                return d
            if not isinstance(pattern, Symbol) or VAR not in pattern.pat:
                return None
            if pattern in d.keys():
                return d if exp == d[pattern] else None
            else:
                d[pattern] = exp
                return d
        elif exp.ty == CONST:
            if pattern.ty == CONST and pattern.val == exp.val:
                return d
            if not isinstance(pattern, Symbol) or CONST not in pattern.pat:
                return None
            if pattern in d.keys():
                return d if exp == d[pattern] else None
            else:
                d[pattern] = exp
                return d
        elif exp.ty == OP:
            if isinstance(pattern, Symbol):
                if OP in pattern.pat:
                    if pattern in d.keys():
                        return d if d[pattern] == exp else None
                    else:
                        d[pattern] = exp
                        return d
                else:
                    return None
            if exp.op != pattern.op or len(exp.args) != len(pattern.args):
                return None
            
            table = [rec(exp.args[i], pattern.args[i]) for i in range(len(exp.args))]
            and_table = functools.reduce(lambda x, y: x and y, table)
            return d if and_table else None
        elif exp.ty == FUN:
            if isinstance(pattern, Symbol):
                if FUN in pattern.pat:
                    if pattern in d.keys():
                        return d if d[pattern] == exp else None
                    else:
                        d[pattern] = exp
                        return d
                else:
                    return None
            if exp.func_name != pattern.func_name or len(exp.args) != len(pattern.args):
                return None
            table = [rec(exp.args[i], pattern.args[i]) for i in range(len(exp.args))]
            and_table = functools.reduce(lambda x, y: x and y, table, True)
            return d if and_table else None
        elif exp.ty in (DERIV, EVAL_AT, INTEGRAL):
            return rec(exp.body, pattern)

    if exp == pattern:
        return dict()
    return rec(exp, pattern)

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
    factors = []
    if e.ty == OP and e.op == "/":
        e = e.args[0] * Op("^", e.args[1], Const(-1))
    def f(e):
        if e.ty == OP and e.op == '*':
            f(e.args[0])
            f(e.args[1])
        else:
            factors.append(e)

    f(e)
    return factors

def from_const_mono(m):
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
            elif power == Fraction(1/2):
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

def from_const_poly(p):
    """Convert a ConstantPolynomial to an expression."""
    if len(p.monomials) == 0:
        return Const(0)
    else:
        monos = [from_const_mono(m) for m in p.monomials]
        return sum(monos[1:], monos[0])

def from_mono(m):
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
            elif power == Fraction(1/2):
                factors.append(sqrt(base))
            else:
                factors.append(base ** Const(power))

    if len(factors) == 0:
        return from_const_poly(m.coeff)
    elif m.coeff.is_one():
        return functools.reduce(operator.mul, factors[1:], factors[0])
    elif m.coeff.is_minus_one():
        return - functools.reduce(operator.mul, factors[1:], factors[0])
    else:
        return functools.reduce(operator.mul, factors, from_const_poly(m.coeff))

def from_poly(p):
    """Convert a polynomial to an expression."""
    if len(p.monomials) == 0:
        return Const(0)
    else:
        monos = [from_mono(m) for m in p.monomials]
        return sum(monos[1:], monos[0]) 

def deriv(var, e):
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
            return (x * deriv(var, y) + deriv(var, x) * y).normalize()
        elif e.op == "/":
            x, y = e.args
            return (deriv(var, x) * y - x * deriv(var, y)).normalize() / (y ^ Const(2)).normalize()
        elif e.op == "^":
            x, y = e.args
            if y.ty == CONST:
                return (y * (x ^ Const(y.val - 1)) * deriv(var, x)).normalize()
            else:
                raise NotImplementedError
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
            return (sec(x) ^ Const(2) * deriv(var, x)).normalize()
        elif e.func_name == "sec":
            x, = e.args
            return (sec(x) * tan(x) * deriv(var, x)).normalize()
        elif e.func_name == "csc":
            x, = e.args
            return (-csc(x) * cot(x) * deriv(var, x)).normalize()
        elif e.func_name == "cot":
            x,  = e.args
            return -(csc(x) ^ Const(2)).normalize()
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
                return deriv(var, e.args[0] ^ Const(Fraction(1/2)))
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
        else:
            raise NotImplementedError
    else:
        raise NotImplementedError

class Var(Expr):
    """Variable."""
    def __init__(self, name):
        assert isinstance(name, str)
        self.ty = VAR
        self.name = name

    def __hash__(self):
        return hash((VAR, self.name))

    def __eq__(self, other):
        return other.ty == VAR and self.name == other.name

    def __str__(self):
        return self.name

    def __repr__(self):
        return "Var(%s)" % self.name

class Const(Expr):
    """Constants."""
    def __init__(self, val):
        assert isinstance(val, (int, Decimal, Fraction))
        self.ty = CONST
        if isinstance(val, Decimal):
            val = Fraction(val)
        self.val = val

    def __hash__(self):
        return hash((CONST, self.val))

    def __eq__(self, other):
        return other.ty == CONST and self.val == other.val

    def __str__(self):
        return str(self.val)

    def __repr__(self):
        return "Const(%s)" % str(self.val)

class Op(Expr):
    """Operators."""
    def __init__(self, op, *args):
        assert isinstance(op, str) and all(isinstance(arg, Expr) for arg in args)
        if len(args) == 1:
            assert op == "-"
        elif len(args) == 2:
            assert op in ["+", "-", "*", "/", "^"]
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
            if a.priority() <= op_priority[self.op]:
                if a.ty == OP and a.op != self.op:
                    s1 = "(%s)" % s1
                elif a.ty in (EVAL_AT, INTEGRAL, DERIV):
                    s1 = "(%s)" % s1
            if b.priority() <= op_priority[self.op] and not (b.ty == CONST and isinstance(b.val, Fraction) and b.val.denominator == 1):
                s2 = "(%s)" % s2
            elif self.op == "^" and a.ty == CONST and a.val < 0:
                s1 = "(%s)" % s1
            elif self.op == "^" and a.is_constant() and a.ty == OP and len(a.args) == 1:
                s1 = "(%s)" % s1
            elif self.op == "^" and a.is_constant() and a.ty == OP and a.op == "^":
                s1 = "(%s)" % s1
            return "%s %s %s" % (s1, self.op, s2)           
        else:
            raise NotImplementedError

    def __repr__(self):
        return "Op(%s,%s)" % (self.op, ",".join(repr(arg) for arg in self.args))

class Fun(Expr):
    """Functions."""
    def __init__(self, func_name, *args):
        assert isinstance(func_name, str) and all(isinstance(arg, Expr) for arg in args)
        if len(args) == 0:
            assert func_name in ["pi", "inf"]
        elif len(args) == 1:
            assert func_name in ["sin", "cos", "tan", "log", "exp", "sqrt", "csc", "sec", "cot", "asin", "acos", "atan", "acot", "acsc", "asec", "abs"]
        else:
            raise NotImplementedError

        self.ty = FUN
        self.func_name = func_name
        self.args = tuple(args)

    def __hash__(self):
        return hash((FUN, self.func_name, self.args))

    def __eq__(self, other):
        if isinstance(other, (int, Fraction)):
            other = Const(other)
        return other.ty == FUN and self.func_name == other.func_name and self.args == other.args

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

pi = Fun("pi")
E = Fun("exp", Const(1))


class Deriv(Expr):
    """Derivative of an expression."""
    def __init__(self, var, body):
        assert isinstance(var, str) and isinstance(body, Expr)

        self.ty = DERIV
        self.var = var
        self.body = body

    def __hash__(self):
        return hash((DERIV, self.var, self.body))

    def __eq__(self, other):
        return other.ty == DERIV and self.var == other.var and self.body == other.body

    def __str__(self):
        return "D %s. %s" % (self.var, str(self.body))

    def __repr__(self):
        return "Deriv(%s,%s)" % (self.var, repr(self.body))

class Integral(Expr):
    """Integral of an expression."""
    def __init__(self, var, lower, upper, body):
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
        return other.ty == INTEGRAL and self.lower == other.lower and self.upper == other.upper and \
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
    def __init__(self, var, lower, upper, body):
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
        return other.ty == EVAL_AT and self.var == other.var and \
            self.lower == other.lower and self.upper == other.upper and self.body == other.body

    def __str__(self):
        return "[%s]_%s=%s,%s" % (str(self.body), self.var, str(self.lower), str(self.upper))

    def __repr__(self):
        return "EvalAt(%s,%s,%s,%s)" % (self.var, repr(self.lower), repr(self.upper), repr(self.body))

class Symbol(Expr):
    """Pattern expression. It can be used to find expression with the given specific structure.
    """
    def __init__(self, name, ty):
        self.name = name
        self.ty = SYMBOL
        self.pat = tuple(ty)
    
    def __eq__(self, other):
        if not isinstance(other, Symbol):
            return False
        return self.name == other.name and self.pat == other.pat

    def __hash__(self):
        return hash((SYMBOL, self.name, self.ty, sum(self.pat)))
    
    def __str__(self):
        return "%s" % (self.name)
    
    def __repr__(self):
        return "Symbol(%s, %s)" % (self.name, self.pat)

trigFun = {
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
            "sin": {parser.parse_expr(key):parser.parse_expr(value) for key, value in sin_table.items()},
            "cos": {parser.parse_expr(key):parser.parse_expr(value) for key, value in cos_table.items()},
            "tan": {parser.parse_expr(key):parser.parse_expr(value) for key, value in tan_table.items()},
            "cot": {parser.parse_expr(key):parser.parse_expr(value) for key, value in cot_table.items()},
            "csc": {parser.parse_expr(key):parser.parse_expr(value) for key, value in csc_table.items()},
            "sec": {parser.parse_expr(key):parser.parse_expr(value) for key, value in sec_table.items()},
        }
    return trig_table_cache

inverse_trig_table_cache = None
def inverse_trig_table():
    """Inverse trigonometric value table."""
    global inverse_trig_table_cache
    if inverse_trig_table_cache is None:
        inverse_trig_table_cache = {
            "asin": {parser.parse_expr(key):parser.parse_expr(value) for key, value in asin_table.items()},
            "acos": {parser.parse_expr(value):parser.parse_expr(key) for key, value in cos_table.items()},
            "atan": {parser.parse_expr(key):parser.parse_expr(value) for key, value in atan_table.items()},
            "acot": {parser.parse_expr(value):parser.parse_expr(key) for key, value in cot_table.items()},
            "acsc": {parser.parse_expr(key):parser.parse_expr(value) for key, value in acsc_table.items()},
            "asec": {parser.parse_expr(value):parser.parse_expr(key) for key, value in sec_table.items()},
        }
    return inverse_trig_table_cache

def expr_to_holpy(expr):
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
        raise NotImplementedError

def holpy_to_expr(t):
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
