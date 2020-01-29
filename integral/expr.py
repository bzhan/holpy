"""Expressions."""

from decimal import Decimal
from fractions import Fraction
from integral import poly
from integral.poly import *
import functools, operator
from collections.abc import Iterable
from integral import parser
from sympy.parsing import sympy_parser
import copy
from sympy.simplify.fu import *
from sympy import solveset, Interval, Eq, Union, EmptySet, apart

VAR, CONST, OP, FUN, DERIV, INTEGRAL, EVAL_AT, ABS = range(8)

op_priority = {
    "+": 65, "-": 65, "*": 70, "/": 70, "^": 75
}

trig_identity = []


class Location:
    """Location within an expression."""
    def __init__(self, data):
        if isinstance(data, Iterable) and all(isinstance(n, int) for n in data):
            self.data = tuple(data)
        elif isinstance(data, str):
            self.data = tuple(int(n) for n in data.split('.'))
        else:
            raise TypeError

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
        if self.ty == CONST and other.ty == CONST:
                return Const(self.val + other.val)
        # elif self.ty == FUN and self.func_name == "log" and other.ty == FUN and other.func_name == "log":
        #     return Fun("log", self.args[0] * other.args[0])
        # elif self.ty == OP and self.op == "/" and other.ty == OP and other.op == "/" and self.args[1] == other.args[1]:
        #     return (self.args[0] + other.args[0]) / self.args[1]
        elif other.ty == OP:
            if other.args[0].ty == CONST and other.args[0].val < 0:
                return self - Op(other.op, Const(-other.args[0].val), other.args[1])
            elif other.args[0].ty == OP and len(other.args[0].args) == 1 and other.args[0].args[0].ty == CONST and other.args[0].args[0].val > 0:
                return self - Op(other.op, Const(other.args[0].args[0].val), other.args[1])
            elif len(other.args) == 1:
                return self - other.args[0]
            else:
                return Op("+", self, other)
        elif other.ty == OP and len(other.args) == 1:
            return self - other.args[0]
        else:
            return Op("+", self, other)

    def __sub__(self, other):
        if self.ty == CONST and other.ty == CONST:
            return Const(self.val - other.val)
        # elif self.ty == FUN and self.func_name == "log" and other.ty == FUN and other.func_name == "log":
        #     c = (self.args[0]) / (other.args[0])
        #     return Fun("log", (self.args[0]) / (other.args[0]))
        elif other.ty == OP and len(other.args) == 1:
            return self + other.args[0]
        else:
            return Op("-", self, other)

    def __mul__(self, other):
        if self == Const(1):
            return other
        if other == Const(1):
            return self
        if self.ty == CONST and self.val == -1:
            if other.ty == CONST and other.val < 0:
                return Const(-other.val)
            if not (other.ty == OP and len(other.args) == 1):
                return Op("-", other)
            else:
                return Op("*", self, other)
        elif other.ty == CONST and other.val == -1:
            if self.ty == CONST and self.val < 0:
                return Const(-self.val)
            elif not (self.ty == OP and len(self.args) == 1):
                return Op("-", self)
            else:
                return Op("*", self, other)
        elif self.ty == CONST and other.ty == CONST:
            return Const(self.val * other.val)
        elif self.ty == FUN and self.func_name == "exp" and other.ty == FUN and other.func_name == "exp":
            power = self.args[0] + other.args[0]
            return Fun("exp", power).normalize()
        # elif 
        else:
            return Op("*", self, other)

    def __truediv__(self, other):
        if other == Const(1):
            return self
        elif self.ty == CONST and other.ty == CONST:
            return Const(Fraction(self.val, other.val))
        elif self.ty == OP and self.op == "^" and other.ty == OP and other.op == "^" and self.args[1] == other.args[1]:
            return (self.args[0] / other.args[0]) ^ self.args[1]
        elif all(s.ty == FUN and s.func_name == "abs" for s in [self, other]):
            x, y = self.args[0], other.args[0]
            if x.is_constant() and y.is_constant():
                n = sympy_style(x/y)
                return holpy_style(n) if n > 0 else holpy_style(-n)

        else:
            return Op("/", self, other)

    def __xor__(self, other):
        if other == Const(1):
            return self
        elif self.ty == FUN and self.func_name == "exp":
            return Fun("exp", (self.args[0]*other).normalize())
        else:
            return Op("^", self, other)

    def __neg__(self):
        if self.ty == CONST:
            return Const(-self.val)
        return Op("-", self)

    def size(self):
        if self.ty in (VAR, CONST):
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

    def __le__(self, other):
        if self.size() != other.size():
            return self.size() <= other.size()

        if self.ty != other.ty:
            return self.ty <= other.ty
        
        if self.ty == VAR:
            return self.name <= other.name
        elif self.ty == CONST:
            return self.val <= other.val
        elif self.is_constant() and other.is_constant():
            return sympy_parser.parse_expr(str(self - other).replace("^", "**")) <= 0
        elif self.ty == OP:
            return (self.op, self.args) <= (other.op, other.args)
        elif self.ty == FUN:
            return (self.func_name, self.args) <= (other.func_name, other.args)
        elif self.ty == DERIV:
            return (self.body, self.var) <= (other.body, other.var)
        elif self.ty == INTEGRAL or self.ty == EVAL_AT:
            return (self.body, self.lower, self.upper, self.var) <= \
                (other.body, other.lower, other.upper, other.var)
        else:
            raise NotImplementedError

    def priority(self):
        if self.ty == VAR:
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
                arg1 = self.args[loc.head].replace_expr(loc.rest, new_expr)
                arg2 = copy.deepcopy(self.args[1 - loc.head])
                if loc.head == 0:
                    return Op(self.op, arg1, arg2)
                else:
                    return Op(self.op, arg2, arg1)
            else:
                raise NotImplementedError
        elif self.ty == FUN:
            # Can't resolve pi now.
            assert loc.head < len(self.args), "get_subexpr: invalid location"
            arg = self.args[loc.head].replace_expr(loc.rest, new_expr)
            return Fun(self.func_name, arg)
        elif self.ty == INTEGRAL or self.ty == EVAL_AT:
            arg0 = copy.deepcopy(self.body)
            arg1 = copy.deepcopy(self.lower)
            arg2 = copy.deepcopy(self.upper)
            if loc.head == 0:
                arg0 = self.body.replace_expr(loc.rest, new_expr)
            elif loc.head == 1:
                arg1 = self.lower.replace_expr(loc.rest, new_expr)
            elif loc.head == 2:
                arg2 = self.upper.replace_expr(loc.rest, new_expr)
            else:
                raise AssertionError("get_subexpr: invalid location")
            return Integral(self.var, arg1, arg2, arg0)
        elif self.ty == DERIV:      
            assert loc.head == 0, "get_subexpr: invalid location"
            return Deriv(self.var, self.body.replace_expr(loc.rest, new_expr))
        else:
            raise NotImplementedError

    def get_location(self):
        """Give an expression, return the sub-expression location which selected field is True."""
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
            name = self.func_name
            if name == "pi":
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

    def to_poly(self, simp = 1):
        """Convert expression to a polynomial."""
        p = self
        if self.is_constant() and simp == 0 and not (self.ty == OP and self.op == "^" and self.args[0] == Fun("pi")):
            p = sympy_parser.parse_expr(str(self).replace("^", "**"))
            return parser.parse_expr(str(p).replace("**", "^")).replace_trig(Var("E"), Fun("exp", Const(1))).to_poly(simp = 1)
        if self.ty == VAR:
            return poly.singleton(self)
        elif self.ty == CONST:
            return poly.constant(self)
        elif self.ty == OP:
            if self.op == "+":
                x, y = self.args
                # if x.ty == FUN and x.func_name == "log" and y.ty == FUN and y.func_name == "log":
                #     return (x.normalize()+y.normalize()).to_poly()
                if y.ty == OP and len(y.args) == 1:
                    # x + (-y) => x - y
                    return Op("-", x, y.args[0]).to_poly()
                elif x.ty == OP and x.op == "^" and x.args[0].ty == FUN and x.args[0].func_name == "sin" and x.args[1].ty == CONST and x.args[1].val == 2\
                    and y.ty == OP and y.op == "^" and y.args[0].ty == FUN and y.args[0].func_name == "cos" and y.args[1].ty == CONST and y.args[1].val == 2\
                    and x.args[0].args[0].normalize() == y.args[0].args[0].normalize():
                    return poly.singleton(Const(1))
                elif x.ty == OP and x.op == "^" and x.args[0].ty == FUN and x.args[0].func_name == "cos" and x.args[1].ty == CONST and x.args[1].val == 2\
                    and y.ty == OP and y.op == "^" and y.args[0].ty == FUN and y.args[0].func_name == "sin" and y.args[1].ty == CONST and y.args[1].val == 2\
                    and x.args[0].args[0].normalize() == y.args[0].args[0].normalize():
                    return poly.singleton(Const(1))
                return x.to_poly() + y.to_poly()
            elif self.op == "*":
                x, y = self.args
                if y.ty == OP and y.op == "/":
                    return Op("/", x * y.args[0], y.args[1]).to_poly()
                elif x.ty == FUN and x.func_name == "exp" and y.ty == FUN and y.func_name == "exp":
                    arg = x.args[0] + y.args[0]
                    return Fun("exp", arg.normalize()).to_poly()
                elif y.ty == OP and y.op == "^" and y.args[0].normalize() == x.normalize():
                    return Op("^", y.args[0], Const(1) + y.args[1]).to_poly()
                elif y.ty == OP and y.op in ("+", "-"):
                    if len(y.args) == 1:
                        return Op(y.op, (x *  y.args[0]).normalize()).to_poly()
                    else:
                        return Op(y.op, (x*y.args[0]).normalize(), (x * y.args[1]).normalize()).to_poly()
                else:
                    return x.normalize().to_poly() * y.normalize().to_poly()
            elif self.op == "-" and len(self.args) == 2:
                x, y = self.args
                # if x.ty == FUN and x.func_name == "log" and y.ty == FUN and y.func_name == "log":
                #     return (x-y).to_poly()
                return x.to_poly() - y.to_poly()
            elif self.op == "-" and len(self.args) == 1:
                x, = self.args
                if x.ty == OP and x.op == "-" and len(x.args) == 1:
                   # --x => x
                    return x.args[0].to_poly()
                elif x.ty == CONST:
                    return Const(-x.val).to_poly()
                return x.to_poly().scale(Const(-1))
            elif self.op == "/":
                x, y = self.args
                if x.normalize() == y.normalize():
                    return poly.singleton(Const(1))
                if x.ty == FUN and x.func_name == "exp" and y.ty == FUN and y.func_name == "exp":
                    return Fun("exp", (x.args[0] - y.args[0]).normalize()).to_poly()
                else:
                    return Op("*", x, Op("^", y, Const(-1))).to_poly()
            elif self.op == "^":
                x, y = self.args
                if x.ty == FUN and x.func_name == "exp":
                    return Fun("exp", y * x.args[0]).to_poly()
                if y.ty == CONST or y.ty == OP and len(y.args) == 1 and y.args[0].ty == CONST:
                    if y.ty == OP and len(y.args) == 1 and y.args[0].ty == CONST:
                        y = Const(-y.args[0].val)
                    if y.val == Fraction(0):
                        return poly.constant(Const(1))
                    elif y.val == 1:
                        return x.to_poly()
                    # elif y.val == 2:
                    #     return x.to_poly()*x.to_poly()
                    else:
                        if x.ty == CONST:
                            if isinstance(x.val, int) and (isinstance(y.val, Fraction) and y.val.denominator == 1 or isinstance(y.val, int)):
                                if y.val > 0:
                                    return poly.constant(Const(x.val ** y.val))
                                else:
                                    return poly.constant(Const(Fraction(1, x.val ** (-y.val))))
                            else:
                                return poly.constant(Op("^", x, y))
                        elif x.ty == VAR:
                            return poly.Polynomial([poly.Monomial(Const(1), [(x, Fraction(y.val))])])
                        elif x.ty == OP:
                            if x.op == "*":
                                #(x * y)^2 = x^2 * y^2
                                return Op("^", x.args[0], y).to_poly() * Op("^", x.args[1], y).to_poly()
                            elif x.op == "^":
                                #(x^(1/2))^2 = x only consider two pow are both constant
                                #(x^2)^(1/2) = abs(x)
                                if x.args[1].ty == CONST and x.args[1].val % 2 == 0:
                                    if x.args[1] * y == Const(1):
                                        return Fun("abs", x.args[0]).to_poly()
                                    elif y.ty == CONST and Fraction(y.val).denominator == 1:
                                        return Op("^", x.args[0], y * x.args[1]).to_poly()
                                    return Fun("abs", Op("^", x.args[0], y * x.args[1])).to_poly()
                                else:
                                    return Op("^", x.args[0], y * x.args[1]).to_poly()
                            elif x.op == "/":
                                return (x.normalize() ^ y).to_poly()
                            elif len(x.args) == 1:
                                return Op("^", x.args[0], y).to_poly() 
                            else:
                                return Polynomial([poly.Monomial(Const(1), [(x.normalize(), y.val)])])
                        elif x.ty == FUN and x.func_name == "sqrt":
                            return Op("^", x.args[0], Const(Fraction(y.val*(1/2)))).to_poly()
                        elif x.ty == FUN and x.func_name in ("sin", "cos", "tan", "asin", "acos", "atan") and x.normalize() != x:
                            return Op("^", x.normalize(), y).to_poly()
                        else:
                            return poly.Polynomial([poly.Monomial(Const(1), [(x.normalize(), y.val)])])
                else:
                    return poly.singleton(self)
            else:
                return poly.singleton(self)
        elif self.ty == FUN:
            if self.func_name == "exp":
                a, = self.args

                if a == Const(0):
                    return poly.constant(Const(1))
                elif a.ty == FUN and a.func_name == "log":
                    return a.args[0].to_poly()
                else:
                    return poly.singleton(Fun("exp", self.args[0].normalize()))
            elif self.func_name in ("sin", "cos", "tan", "asin", "acos", "atan", "cot", "csc", "sec"):
                p = Fun(self.func_name, self.args[0].normalize())
                p = sympy_style(p).simplify()
                p = holpy_style(p)
                if p != self:
                    return p.to_poly()
                else:
                    return poly.singleton(self)                
            elif self.func_name == "log":
                a, = self.args
                if self.args[0].ty == CONST and self.args[0].val <= 0:
                    raise ValueError
                elif self.args[0] == Const(1):
                    return poly.constant(Const(0))
                elif a.ty == FUN and a.func_name == "exp":
                    y, = a.args
                    return y.to_poly()
                elif self.args[0].ty == OP and self.args[0].op == "^":
                    i, j = self.args[0].args
                    if i.ty == FUN and i.func_name == "exp":
                        return j.to_poly()
                    else:
                        return (j * Fun("log", i)).to_poly()
                else:
                    return poly.singleton(Fun("log", self.args[0].normalize()))
            elif self.func_name == "sqrt":
                return Op("^", self.args[0], Const(Fraction(1/2))).to_poly()
            elif self.func_name == "abs":
                x, =self.args
                if x.ty == CONST:
                    return poly.constant(Const(abs(x.val)))
                elif x.is_constant():
                    if sympy_style(x) > 0:
                        return poly.constant(holpy_style(sympy_style(x)))
                    else:
                        return poly.constant(holpy_style(sympy_style(-x)))
                else:
                    return poly.singleton(self)
            else:
                return poly.singleton(self)
        elif self.ty == EVAL_AT:
            upper = self.body.subst(self.var, self.upper)
            lower = self.body.subst(self.var, self.lower)
            return (upper.normalize() - lower.normalize()).to_poly(0)
            # return upper.to_poly() - lower.to_poly()
        elif self.ty == INTEGRAL:
            a = self
            if a.lower == a.upper:
                return poly.constant(Const(0))
            a.body = a.body.normalize()
            return poly.singleton(a) 
        else:
            return poly.singleton(self)

    def normalize(self):
        """Normalizes an expression."""
        return from_poly(self.to_poly(0))

    def replace_trig(self, trig_old, trig_new):
        """Replace the old trig to its identity trig in e."""
        assert isinstance(trig_new, Expr)
        if self == trig_old:
            return trig_new
        else:
            """Note: The old trig must exist in self.
            """
            if self.ty == OP:
                self.args = list(self.args)
                if len(self.args) == 1:
                    self.args[0] = self.args[0].replace_trig(trig_old, trig_new)
                    #self.args = tuple(self.args)
                    return Op(self.op, self.args[0])
                elif len(self.args) == 2:
                    if self.op == "^" and trig_old.ty == OP and trig_old.op == "^" \
                      and self.args[0] == trig_old.args[0]:
                        # expr : x ^ 4 trig_old x ^ 2 trig_new u => u ^ 2
                        return Op(self.op, trig_new, self.args[1] / trig_old.args[1])
                    self.args[0] = self.args[0].replace_trig(trig_old, trig_new)
                    self.args[1] = self.args[1].replace_trig(trig_old, trig_new)
                    #self.args = tuple(self.args)
                    return Op(self.op, self.args[0], self.args[1])
                else:
                    return Op(self.op, self.args)
            elif self.ty == FUN:
                if len(self.args) > 0:
                    self.args = list(self.args)
                    self.args[0] = self.args[0].replace_trig(trig_old, trig_new)
                    return Fun(self.func_name, self.args[0])
                else:
                    return self
            else:
                return self

    def identity_trig_expr(self, trigs):
        """Input: A list contains the trigs expected to transform in trig_identity.
           Output: A list contains all possible transformation and it's rule occurs in self.
        """
        n = []
        for t in trigs:
            s = trig_transform(t) #transformation set
            for item in s:
                c = copy.deepcopy(self)
                c = c.replace_trig(t, parser.parse_expr(str(item[0]).replace("**", "^")))
                n.append((c, item[1]))
        return n

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

    def ranges(self, var, lower, upper):
        """Find expression where greater and smaller than zero in the interval: lower, upper"""
        e = sympy_style(self)
        var = sympy_style(var)
        lower = sympy_style(lower)
        upper = sympy_style(upper)
        greater_zero = solveset(e > 0, var, Interval(lower, upper, left_open = True, right_open = True))
        smaller_zero = solveset(e < 0, var, Interval(lower, upper, left_open = True, right_open = True))
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
        if len(p.monomials) == 1: #Only separate 
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

def sympy_style(s):
        """Transform expr to sympy object.
        """
        return sympy_parser.parse_expr(str(s).replace("^", "**"))

def holpy_style(s):
    return parser.parse_expr(str(s).replace("**", "^")).replace_trig(Var("E"), Fun("exp", Const(1)))


def valid_expr(s):
    try:
        sk = parser.parse_expr(s)
    except (exceptions.UnexpectedCharacters, exceptions.UnexpectedToken) as e:
        return False
    return True

def trig_transform(trig):
    """Compute all possible trig function equal to trig"""
    poss = set()
    poss_expr = set()
    i = sympy_parser.parse_expr(str(trig).replace("^", "**"))
    for f, rule in trigFun.items():
        j = f(sympy_parser.parse_expr(str(trig).replace("^", "**")))
        if i != j and j not in poss_expr:
            poss.add((holpy_style(j), f.__name__))
            poss_expr.add(j)
    poss.add((holpy_style(i), "Unchanged"))
    return poss

def from_mono(m):
    """Convert a monomial to an expression."""
    factors = []
    if m.coeff != Const(1):
        factors.append(m.coeff)
    exps = []
    for factor, pow in m.factors:
        if factor.ty == FUN and factor.func_name == "exp":
            exps.append(factor.args[0]*Const(pow))   
        elif pow == 1:
            factors.append(factor)
        else:
            factors.append(factor ^ Const(pow))
    new_exp = Const(1)
    if exps:
        k = sum(exps[1:], exps[0])
        if k.normalize() != Const(0):
            new_exp = Fun("exp", k.normalize())
    factors.append(new_exp)
    if len(factors) == 0:
        return Const(1)
    else:
        return functools.reduce(operator.mul, factors[1:], factors[0])

def from_poly(p):
    """Convert a polynomial to an expression."""
    if len(p.monomials) == 0:
        return Const(0)
    else:
        monos = [from_mono(m) for m in p.monomials]
        return sum(monos[1:], monos[0]) 

def extract(p):
    """If a polynomial have common factors, extract them from it.
    """
    if len(p.monomials) == 0:
        return Const(0)
    else:
        monos = [from_mono(m) for m in p.monomials]
        common_factor = collect_common_factor(monos)
        common_keys = common_factor[0].keys()
        for d in common_factor:
            common_keys &= d.keys()
        min_dic = {}
        for k in common_keys:
            min = common_factor[0][k]
            for d in common_factor:
                if d[k] < min:
                    min = d[k]
            min_dic[k] = min
        for k, v in min_dic.items():
            collect_common_factor(monos, v, k)
        return monos, min_dic 


def collect_common_factor(monos, sub = 0, el = None):
    d = []
    if sub == 0:
        for m in monos:
            res = {}
            collect(m, res)
            d.append(res)
        return d
    else:
        for i in range(len(monos)):
            monos[i] = collect(monos[i], sub = sub, el = el)


def collect(m, res = {}, sub = 0, el = None):
    if sub == 0:
        #collect information
        if m.ty == VAR:
            res[m] = 1
        elif m.ty == FUN:
            res[m] = 1
        elif m.ty == OP and m.op == "^":
            if m.args[0].ty == VAR:
                # x ^ n
                res[m.args[0]] = m.args[1].val
            elif m.args[0].ty == FUN:
                # sin(x) ^ n
                res[m.args[0]] = m.args[1].val
            else:
                raise NotImplementedError
        elif m.ty == OP and m.op == "*":
            collect(m.args[0], res)
            collect(m.args[1], res)
    elif sub > 0:
        #extract common factors
        if m.ty == VAR and m == el:
            #only exists when factor is 1
            return Const(1)
        elif m.ty == FUN and isinstance(el, Fun) and m == el:
            #only exists when factor is 1
            return Const(1)
        elif m.ty == OP and m.op == "^":
            if m.args[0].ty == VAR and m.args[0] == el:
                # x ^ n => x ^ (n - sub)
                m.args[1].val -= sub
                return Op(m.op, m.args[0], m.args[1])
            elif m.args[0].ty == FUN and m.args[0] == el:
                # sin(x) ^ n => sin(x) ^ (n - sub)
                m.args[1].val -= sub
                return Op(m.op, m.args[0], m.args[1])
            else:
                return m
        elif m.ty == OP and m.op == "*":
            if m.args[1].ty == VAR and m.args[1] == el:
                #because op'args is a tuple which is immutable
                return m.args[0]
            else:         
                a = collect(m.args[0], res, sub, el)
                b = collect(m.args[1], res, sub, el)
                return a * b
        else:
            return m
    else:
        raise NotImplementedError

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
            return -(csc(x) ^ 2).normalize()
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
        elif e.func_name == "atan":
            x, = e.args
            return (deriv(var, x) / sqrt(Const(1) + x ^ Const(2))).normalize()
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
        assert isinstance(val, (int, Fraction, Decimal))
        self.ty = CONST
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
            if a.priority() < 70:
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
                if not (b.ty == OP and b.op in ("+", "*") and b.op == self.op):
                    s2 = "(%s)" % s2
            elif self.op == "^" and a.ty == CONST and a.val < 0:
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
            assert func_name in ["pi"]
        elif len(args) == 1:
            assert func_name in ["sin", "cos", "tan", "log", "exp", "sqrt", "csc", "sec", "cot", "asin", "acos", "atan", "abs"]
        else:
            raise NotImplementedError

        self.ty = FUN
        self.func_name = func_name
        self.args = tuple(args)

    def __hash__(self):
        return hash((FUN, self.func_name, self.args))

    def __eq__(self, other):
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
        if other.ty != INTEGRAL:
            return False
        condition1 = other.ty == INTEGRAL and other.lower == self.lower and other.upper == self.upper
        other_copy = copy.deepcopy(other).alpha_convert(self.var) 
        return other.ty == INTEGRAL and self.lower == other.lower and self.upper == other.upper and self.body == other_copy.body

    def __str__(self):
        return "INT %s:[%s,%s]. %s" % (self.var, str(self.lower), str(self.upper), str(self.body))

    def __repr__(self):
        return "Integral(%s,%s,%s,%s)" % (self.var, repr(self.lower), repr(self.upper), repr(self.body))

    def alpha_convert(self, alpha):
        alpha_eq_integral = copy.deepcopy(self)
        return Integral(alpha, alpha_eq_integral.lower, alpha_eq_integral.upper, alpha_eq_integral.body.replace_trig(parser.parse_expr(self.var), parser.parse_expr(alpha)))

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

trigFun = {     
    TR0: "simplify expression",
    TR1: "sec-csc to cos-sin",
    TR2: "tan-cot to sin-cos ratio",
    TR2i: "sin-cos ratio to tan",
    TR3: "angle canonicalization",
    TR4: "functions at special angles",
    TR5: "powers of sin to powers of cos",
    TR6: "powers of cos to powers of sin",
    TR7: "reduce cos power (increase angle)",
    TR8: "expand products of sin-cos to sums",
    TR9: "contract sums of sin-cos to products",
    TR10: "separate sin-cos arguments",
    TR10i: "collect sin-cos arguments",
    TR11: "reduce double angles",
    TR12: "separate tan arguments",
    TR12i: "collect tan arguments",
    TR13: "expand product of tan-cot",
    TRmorrie: "prod(cos(x*2**i), (i, 0, k: 1)) -> sin(2**k*x)/(2**k*sin(x))",
    TR14: "factored powers of sin or cos to cos or sin power",
    TR15: "negative powers of sin to cot power",
    TR16: "negative powers of cos to tan power",
    TR22: "tan-cot powers to negative powers of sec-csc functions",
    TR111: "negative sin-cos-tan powers to csc-sec-cot"
}