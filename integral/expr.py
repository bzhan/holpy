"""Expressions."""

from decimal import Decimal
from fractions import Fraction
from integral import poly
from integral.poly import *
import functools, operator
from integral import parser
import sympy
from sympy.simplify.fu import *
from sympy.parsing import sympy_parser
import copy
from sympy.simplify.fu import *

VAR, CONST, OP, FUN, DERIV, INTEGRAL, EVAL_AT, ABS = range(8)

op_priority = {
    "+": 65, "-": 65, "*": 70, "/": 70, "^": 75
}

trig_identity = []

class Expr:
    """Expressions."""
    def __add__(self, other):
        if self.ty == CONST and other.ty == CONST:
                return Const(self.val + other.val)
        elif self.ty == FUN and self.func_name == "log" and other.ty == FUN and other.func_name == "log":
            return Fun("log", self.args[0]*other.args[0])
        else:
            return Op("+", self, other)

    def __sub__(self, other):
        if self.ty == CONST and other.ty == CONST:
            return Const(self.val - other.val)
        elif self.ty == FUN and self.func_name == "log" and other.ty == FUN and other.func_name == "log":
            return Fun("log", self.args[0]/other.args[0])
        else:
            return Op("-", self, other)

    def __mul__(self, other):
        if self == Const(1):
            return other
        if other == Const(1):
            return self
        elif self.ty == CONST and other.ty == CONST:
            return Const(self.val * other.val)
        else:
            return Op("*", self, other)

    def __truediv__(self, other):
        if other == Const(1):
            return self
        elif self.ty == CONST and other.ty == CONST:
            return Const(Fraction(self.val, other.val))
        elif self.ty == OP and self.op == "/" and other.ty == OP and other.op == "/" and self.args[1] == other.args[1]:
            return Op("/", self.args[0] + other.args[0], self.args[1])
        else:
            return Op("/", self, other)

    def __xor__(self, other):
        if other == Const(1):
            return self
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
        if self.is_constant() and simp == 0:
            p = sympy_parser.parse_expr(str(self).replace("^", "**"))
            return parser.parse_expr(str(p).replace("**", "^")).to_poly(simp = 1)
        if self.ty == VAR:
            return poly.singleton(self)
        elif self.ty == CONST:
            return poly.constant(self)
        elif self.ty == OP:
            if self.op == "+":
                x, y = self.args
                if x.ty == FUN and x.func_name == "log" and y.ty == FUN and y.func_name == "log":
                    return (x+y).to_poly()
                # elif x.ty == OP and x.op == "/" and y.ty == OP and y.op == "/" and x.args[1] == y.args[1]:
                #     # 1 / x + 1 / x = 2 / x
                #     return Op("/", x.args[0] + y.args[0], x.args[1]).to_poly()
                return x.to_poly() + y.to_poly()
            elif self.op == "*":
                x, y = self.args
                if x.ty == CONST and y.ty == INTEGRAL:
                    return Integral(y.var, y.lower, y.upper, x * y.body).to_poly()
                elif y.ty == OP and y.op == "/":
                    return Op("/", x * y.args[0], y.args[1]).to_poly()
                else:
                    return x.to_poly() * y.to_poly()
            elif self.op == "-" and len(self.args) == 2:
                x, y = self.args
                if x.ty == FUN and x.func_name == "log" and y.ty == FUN and y.func_name == "log":
                    return (x-y).to_poly()
                return x.to_poly() - y.to_poly()
            elif self.op == "-" and len(self.args) == 1:
                x, = self.args
                return -(x.to_poly())
            elif self.op == "/":
                x, y = self.args
                xp = x.to_poly()
                yp = y.to_poly()
                if x.ty == CONST and x.val == 0:
                    return poly.constant(Const(0))
                elif y.ty == CONST and y.val != 0:
                    return xp.scale(Const(Fraction(1, y.val)))                
                if len(yp.monomials) == 1:
                    k = yp.monomials[0]
                    k.coeff = Const(Fraction(1, k.coeff.val))
                    k_factor = list(k.factors)
                    k_factor = [(f1, -f2) for (f1, f2) in k_factor]
                    k.factors = tuple(k_factor)
                    return poly.Polynomial([m*k for m in xp.monomials])
                else:
                    return poly.singleton(Op("/", from_poly(xp), from_poly(yp)))
            elif self.op == "^":
                x, y = self.args
                if y.ty == CONST:
                    if y.val == Fraction(0):
                        return poly.constant(Const(1))
                    elif y.val == 1:
                        return x.to_poly()
                    else:
                        if x.ty == CONST:
                            if isinstance(x.val, int) and (isinstance(y.val, Fraction) and y.val.denominator == 1 or isinstance(y.val, int)):
                                return poly.constant(Const(x.val**y.val))
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
                                return Op("^", x.args[0], y * x.args[1]).to_poly()
                            elif x.op == "/":
                                return x.args[0].to_poly() / x.args[1].to_poly()
                            else:
                                return Polynomial([poly.Monomial(Const(1), [(x.normalize(), y.val)])])
                        elif x.ty == FUN and x.func_name == "sqrt":
                            return Op("^", x.args[0], Const(Fraction(y.val*(1/2)))).to_poly()
                        else:
                            return poly.Polynomial([poly.Monomial(Const(1), [(x, y.val)])])
                else:
                    return poly.singleton(self)
            else:
                return poly.singleton(self)
        elif self.ty == FUN:
            if self.func_name == "exp":
                if self.args[0] == Const(0):
                    return poly.constant(Const(1))
                else:
                    return poly.singleton(Fun("exp", self.args[0].normalize()))
            elif self.func_name in ("sin", "cos", "tan", "asin", "acos", "atan"):
                p = sympy_parser.parse_expr(str(self).replace("^", "**"))
                p = parser.parse_expr(str(p).replace("**", "^"))
                if p != self:
                    return p.to_poly()
                else:
                    return poly.singleton(self)                
            elif self.func_name == "log":
                if self.args[0].ty == CONST and self.args[0].val <= 0:
                    raise ValueError
                elif self.args[0] == Const(1):
                    return poly.constant(0)
                elif self.args[0].ty == FUN and self.args[0].func_name == "exp":
                    return poly.constant(1)
                elif self.args[0].ty == OP and self.args[0].op == "^":
                    i, j = self.args[0].args
                    if i.ty == FUN and i.func_name == "exp":
                        return j.to_poly()
                    else:
                        return (j * Fun("log", i)).to_poly()
                else:
                    return poly.singleton(Fun("log", self.args[0].normalize()))
            elif self.func_name == "sqrt":
                return Op("^", self.args[0].normalize(), Const(Fraction(1/2))).to_poly()
            else:
                return poly.singleton(self)
        elif self.ty == EVAL_AT:
            upper = self.body.subst(self.var, self.upper)
            lower = self.body.subst(self.var, self.lower)
            return upper.to_poly() - lower.to_poly()
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
                result.append(expr)
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
        return v[0]

def trig_transform(trig):
    """Compute all possible trig function equal to trig"""
    poss = set()
    poss_expr = set()
    i = sympy_parser.parse_expr(str(trig).replace("^", "**"))
    for f, rule in trigFun.items():
        j = f(sympy_parser.parse_expr(str(trig).replace("^", "**")))
        if i != j and j not in poss_expr:
            poss.add((j, rule))
            poss_expr.add(j)
    poss.add((i, "Unchanged"))
    return poss

def from_mono(m):
    """Convert a monomial to an expression."""
    factors = []
    if m.coeff != Const(1):
            factors.append(m.coeff)
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
        if self.val < 0:
            return "(" + str(self.val) + ")"
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
        return isinstance(other, Op) and self.op == other.op and self.args == other.args

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
            if b.priority() <= op_priority[self.op] and not (b.ty == CONST and b.val < 0):
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
            assert func_name in ["sin", "cos", "tan", "log", "exp", "sqrt", "csc", "sec", "cot", "asin", "acos", "atan"]
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
    return Fun("asin", e)

def arctan(e):
    return Fun("atan", e)

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

class Abs(Expr):
    """Absolute expression."""
    def __init__(self, exp):
        assert isinstance(exp, Expr)
        self.exp = exp
        self.ty = ABS

    def __hash__(self):
        return hash((ABS, self.exp))

    def __eq__(self, other):
        return other.ty == ABS and self.exp == other.exp

    def __str__(self):
        return "|%s|" % str(self.exp)

    def __repr__(self):
        return "Abs(%s)" % (repr(self.exp))

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