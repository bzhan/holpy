"""Expressions."""

from decimal import Decimal
from fractions import Fraction
from integral import poly
from integral.poly import *
import functools, operator
from integral import parser
import sympy

VAR, CONST, OP, FUN, DERIV, INTEGRAL, EVAL_AT = range(7)

op_priority = {
    "+": 65, "-": 65, "*": 70, "/": 70, "^": 75
}

class Expr:
    """Expressions."""
    def __add__(self, other):
        return Op("+", self, other)

    def __sub__(self, other):
        return Op("-", self, other)

    def __mul__(self, other):
        if self == Const(1):
            return other
        else:
            return Op("*", self, other)

    def __truediv__(self, other):
        if other == Const(1):
            return self
        else:
            return Op("/", self, other)

    def __xor__(self, other):
        if other == Const(1):
            return self
        else:
            return Op("^", self, other)

    def __neg__(self):
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

    def __le__(self, other):
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
        else:
            raise NotImplementedError

    def priority(self):
        if self.ty == VAR:
            return 100
        elif self.ty == CONST:
            if isinstance(self.val, Fraction):
                return 70  # priority of division
            else:
                return 100
        elif self.ty == OP:
            if len(self.args) == 1:
                return 80
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

    def to_poly(self):
        """Convert expression to a polynomial."""
        if self.ty == VAR:
            return poly.singleton(self)
        elif self.ty == CONST:
            return poly.constant(self.val)
        elif self.ty == OP:
            if self.op == "+":
                x, y = self.args
                return x.to_poly() + y.to_poly()
            elif self.op == "*":
                x, y = self.args
                if x == Const(0) or y == Const(0):
                    return poly.constant(0) 
                return x.to_poly() * y.to_poly()
            elif self.op == "-" and len(self.args) == 2:
                x, y = self.args
                return x.to_poly() - y.to_poly()
            elif self.op == "-" and len(self.args) == 1:
                x, = self.args
                return -(x.to_poly())
            elif self.op == "/":
                x, y = self.args
                xp = x.to_poly()
                yp = y.to_poly()
                if yp.is_nonzero_constant():
                    return xp.scale(Fraction(1) / Fraction(yp.get_constant()))
                elif xp.is_nonzero_constant() and xp.get_constant() != 1:
                    #normalize assures constant always on the right
                    return (Const(1)/y.normalize()).to_poly().scale(Fraction(xp.get_constant()))
                elif xp.is_nonzero_constant() and xp.get_constant() == 1:
                    #can't find a better way to normalize the denominator now
                    return poly.singleton(self)
                else:
                    return poly.singleton(self)
            elif self.op == "^":
                x, y = self.args
                if y.ty == CONST and y.val == 0:
                    return poly.constant(1)
                if x.ty == CONST and y.ty == CONST:
                    if x.val == 0: 
                        if y.val == 0:
                            return poly.constant(1)
                        else:
                            return poly.constant(0)
                    if isinstance(y.val, int):
                        if y.val < 0:
                            return poly.constant(Fraction(x.val) ** y.val)
                        else:
                            return poly.constant(Fraction(x.val ** y.val))
                    elif isinstance(y.val, Fraction):
                        k = Fraction(x.val ** y.val)
                        if k.denominator == 1:
                            return poly.constant(k.numerator)
                        else: 
                            return poly.Polynomial([poly.Monomial(1, [(x, y.val)])])
                elif y.ty == CONST and y.val == 1:
                    return x.to_poly()
                elif y.ty == CONST and y.val != 1:
                    return poly.Polynomial([poly.Monomial(1, [(x, y.val)])])
                else:
                    return poly.singleton(self)
            else:
                return poly.singleton(self)
        elif self.ty == FUN:
            if self.func_name == "exp" and self.args[0] == Const(0):
                return poly.constant(1)
            elif self.func_name == "cos":
                if self.args[0] == Const(0):
                    return poly.constant(1)
                elif self.args[0].ty == OP and self.args[0].op == "/" and \
                        self.args[0].args[0] == pi and self.args[0].args[1].ty == CONST:
                    p = parser.parse_expr(str(sympy.cos(sympy.pi/self.args[0].args[1].val)))
                    return p.to_poly()
                elif self.args[0].ty == OP and self.args[0].op == "*" and \
                        self.args[0].args[0].ty == CONST and self.args[0].args[1] == pi:
                    p = parser.parse_expr(str(sympy.cos(sympy.pi*self.args[0].args[0].val)))
                    return p.to_poly()
                elif self.args[0].ty == OP and self.args[0].op == "-" and len(self.args[0].args) == 1:
                    #cos(-x)
                    a = self.args[0].args[0]
                    if a.ty == FUN and a.func_name == "pi":
                        return poly.constant(-1)
                    elif a.ty == CONST:
                        p = parser.parse_expr(str(sympy.cos(-a.val)))
                        return p.to_poly()
                    else:
                        return poly.singleton(self)
                elif self.args[0] == pi:
                    return poly.constant(-1)
                else:
                    return poly.singleton(self)                
            elif self.func_name == "sin":
                if self.args[0] == Const(0):
                    return poly.constant(0)
                elif self.args[0].ty == OP and self.args[0].op == "/" and \
                        self.args[0].args[0] == pi and self.args[0].args[1].ty == CONST:
                    p = parser.parse_expr(str(sympy.sin(sympy.pi/self.args[0].args[1].val)))
                    return p.to_poly()
                elif self.args[0].ty == OP and self.args[0].op == "*" and \
                        self.args[0].args[0].ty == CONST and self.args[0].args[1] == pi:
                    p = parser.parse_expr(str(sympy.sin(sympy.pi*self.args[0].args[0].val)))
                    return p.to_poly()
                elif self.args[0] == pi:
                    return poly.constant(0)
                elif self.args[0].ty == OP and self.args[0].op == "-" and len(self.args[0].args) == 1:
                    a = self.args[0].args[0]
                    if a.ty == FUN and a.func_name == "pi":
                        return poly.constant(0)
                    elif a.ty == CONST:
                        p = parser.parse_expr(str(sympy.sin(-a.val)))
                        return p.to_poly()
                    else:
                        return poly.singleton(self)
                else:
                    return poly.singleton(self)
            elif self.func_name == "tan":
                if self.args[0] == Const(0):
                    raise ValueError
                elif self.args[0].ty == OP and self.args[0].op == "/" and \
                        self.args[0].args[0] == pi and self.args[0].args[1].ty == CONST:
                    p = parser.parse_expr(str(sympy.tan(sympy.pi/self.args[0].args[1].val)))
                    return p.to_poly()
                elif self.args[0].ty == OP and self.args[0].op == "*" and \
                        self.args[0].args[0].ty == CONST and self.args[0].args[1] == pi:
                    p = parser.parse_expr(str(sympy.tan(sympy.pi*self.args[0].args[0].val)))
                    return p.to_poly()
                elif self.args[0] == pi:
                    #haven't implemented infinitely positive symbol
                    raise ValueError  
                elif self.args[0].ty == OP and self.args[0].op == "-" and len(self.args[0].args) == 1:
                    a = self.args[0].args[0]
                    if a.ty == FUN and a.func_name == "pi":
                        raise ValueError
                    elif a.ty == CONST:
                        p = parser.parse_expr(str(sympy.tan(-a.val)))
                        return p.to_poly()
                    else:
                        return poly.singleton(self)
                else:
                    return poly.singleton(self)
            elif self.func_name == "arctan":
                arg = self.args[0]
                if arg == Const(0):
                    return poly.constant(0)
                elif arg.ty == FUN and arg.func_name == "sqrt" and arg.args[0].ty == CONST:
                    #arctan(sqrt(3))
                    val = str(sympy.atan(sympy.sqrt(arg.args[0].val)))
                    return parser.parse_expr(val).to_poly()
                elif arg.ty == OP and arg.op == "/" and arg.args[0].ty == FUN and \
                        arg.args[0].func_name == "sqrt" and arg.args[0].args[0].ty == CONST and \
                            arg.args[1].ty == CONST:
                    #arctan(sqrt(3)/3)
                    val = str(sympy.atan(sympy.sqrt(arg.args[0].args[0].val)/arg.args[1].val))
                    return parser.parse_expr(val).to_poly()
                elif arg.ty == CONST:
                    val = str(sympy.atan(arg.val))
                    return parser.parse_expr(val).to_poly()
                else:
                    return poly.singleton(self)
            elif self.func_name == "log":
                if self.args[0].ty == CONST and self.args[0].val <= 0:
                    raise ValueError
                elif self.args[0] == Const(1):
                    return poly.constant(0)
                elif self.args[0].ty == FUN and self.args[0].func_name == "exp":
                    return poly.constant(1)
                else:
                    return poly.singleton(Fun("log", self.args[0].normalize()))
            else:
                return poly.singleton(self)
        elif self.ty == EVAL_AT:
            upper = self.body.subst(self.var, self.upper)
            lower = self.body.subst(self.var, self.lower)
            return (upper - lower).normalize().to_poly()
        elif self.ty == INTEGRAL:
            a = self
            if a.lower == a.upper:
                return poly.constant(0)
            a.body = a.body.normalize()
            return poly.singleton(a) 
        else:
            return poly.singleton(self)

    def normalize(self):
        """Normalizes an expression."""
        return from_poly(self.to_poly())

def from_mono(m):
    """Convert a monomial to an expression."""
    factors = []
    if m.coeff != 1:
        factors.append(Const(m.coeff))
    for factor, pow in m.factors:
        if pow == 1:
            factors.append(factor)
        else:
            factors.append(factor ^ Const(pow))

    if len(factors) == 0:
        return Const(1)
    else:
        return functools.reduce(operator.mul, factors[1:], factors[0])

def from_poly(p):
    """Convert a polynomial to an expression."""
    if len(p.monomials) == 0:
        return Const(0)
    else:
        if p.is_zero_constant():
            monos = [from_mono(m) for m in p.monomials]
        else:
            monos = [from_mono(m) for m in p.del_zero_mono().monomials]
        return sum(monos[1:], monos[0]) 

def extract(p):
    """If a polynomial have common factors, extract them from it.
    """
    if len(p.monomials) == 0:
        return Const(0)
    else:
        if p.is_zero_constant():
            monos = [from_mono(m) for m in p.monomials]
        else:
            monos = [from_mono(m) for m in p.del_zero_mono().monomials]
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
                return m
            elif m.args[0].ty == FUN and m.args[0] == el:
                # sin(x) ^ n => sin(x) ^ (n - sub)
                m.args[1].val -= sub
                return m
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
            return (deriv(var, x) * y - x * deriv(var, y)).normalize() / (y ^ Const(2))
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
        elif e.func_name == "log":
            x, = e.args
            return (deriv(var, x) / x).normalize()
        elif e.func_name == "exp":
            x, = e.args
            return (exp(x) * deriv(var, x)).normalize()
        elif e.func_name == "pi":
            return Const(0)
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
        return hash((OP, self.op, self.args))

    def __eq__(self, other):
        return other.ty == OP and self.op == other.op and self.args == other.args

    def __str__(self):
        if len(self.args) == 1:
            a, = self.args
            s = str(a)
            if a.priority() < 80:
                s = "(%s)" % s
            return "%s%s" % (self.op, s)
        elif len(self.args) == 2:
            a, b = self.args
            s1, s2 = str(a), str(b)
            if a.priority() < op_priority[self.op]:
                s1 = "(%s)" % s1
            if b.priority() <= op_priority[self.op]:
                s2 = "(%s)" % s2
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
            assert func_name in ["sin", "cos", "log", "exp", "sqrt", "arcsin", "arctan"]
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

def cos(e):
    return Fun("cos", e)

def tan(e):
    return Fun("tan", e)

def log(e):
    return Fun("log", e)

def exp(e):
    return Fun("exp", e)

def arcsin(e):
    return Fun("arcsin", e)

def arctan(e):
    return Fun("arctan", e)

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
        return other.ty == INTEGRAL and self.var == other.var and \
            self.lower == other.lower and self.upper == other.upper and self.body == other.body

    def __str__(self):
        return "INT %s:[%s,%s]. %s" % (self.var, str(self.lower), str(self.upper), str(self.body))

    def __repr__(self):
        return "Integral(%s,%s,%s,%s)" % (self.var, repr(self.lower), repr(self.upper), repr(self.body))

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

