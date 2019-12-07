"""Polynomials."""

from lark import Lark, Transformer, v_args, exceptions
from fractions import Fraction
from decimal import Decimal
from collections.abc import Iterable

def collect_pairs(ps):
    """Reduce a list of pairs by collecting into groups according to
    first components, and adding the second component for each group.

    It is assumed that the first components are hashable.

    e.g. [("x", 1), ("y", 2), ("x", 3)] => [("x", 4), ("y", 2)]

    """
    res = {}
    for v, c in ps:
        if v in res:
            res[v] += c
        else:
            res[v] = c
    return tuple(sorted(((k, v) for k, v in res.items()),reverse=True))

def collect_pairs1(ps):
    """Reduce a list of pairs by collecting into groups according to
    first components, and adding the second component for each group.

    It is assumed that the first components are hashable.

    e.g. [("x", 1), ("y", 2), ("x", 3)] => [("x", 4), ("y", 2)]

    """
    res = {}
    for v, c in ps:
        if v in res:
            res[v] += c
        else:
            res[v] = c
    return tuple(sorted(((k, v) for k, v in res.items())))

class Monomial:
    """Represents a monomial."""
    def __init__(self, coeff, factors):
        """Construct a monomial from coefficient and tuple of factors,
        where each factor is associated its power. For example,

        (2, ()) -> 2
        (2, ((x, 1))) -> 2 * x
        (2, ((x, 2), (y, 1))) -> 2 * x^2 * y

        """
        assert isinstance(coeff, (int, Fraction, Decimal))
        assert all(isinstance(factor, Iterable) and len(factor) == 2 and \
            isinstance(factor[1], (int, Fraction)) for factor in factors), \
            "Unexpected argument for factors: %s" % str(factors)
        self.coeff = coeff
        self.factors = collect_pairs1(factors)
        self.var = None if self.is_constant() else factors[0][0]
        self.degree = 0 if self.is_constant() else self.factors[0][1]

    def __eq__(self, other):
        return isinstance(other, Monomial) and self.coeff == other.coeff and \
            self.factors == other.factors

    def __str__(self):
        res = ""
        if self.coeff != 1:
            res += str(self.coeff)
        for var, p in self.factors:
            s = str(var)
            if len(s) != 1:
                s = "(" + s + ")"
            if str(p) != "1":
                if isinstance(p, Fraction):
                    assert p.denominator != 0
                    if p.denominator == 1:
                        s = s + "^" + str(p.numerator)
                    else:
                        s = s + " ^ " + str(p)
                else:
                    s = s + "^" + str(p)
            res += s

        if res == "":
            res = "1"
        return res

    def __repr__(self):
        return "Monomial(%s)" % str(self)

    def __le__(self, other):
        return (self.factors, self.coeff) < (other.factors, other.coeff)

    def __lt__(self, other):
        return self <= other and self != other

    def __mul__(self, other):
        return Monomial(self.coeff * other.coeff, self.factors + other.factors)

    def __truediv__(self, other):
        assert other.coeff != 0
        c = Fraction(self.coeff, other.coeff)
        if self.is_constant(): 
            if other.is_constant():
                return Monomial(c, tuple())
            else:
                return Monomial(c, ((self.var, -other.degree),))
        else:
            if other.is_constant():
                return Monomial(c, ((self.var, self.degree),))
            else:
                if self.degree - other.degree != 0:
                    return Monomial(c, ((self.var, self.degree-other.degree),))
                else:
                    return Monomial(c, tuple())
    def scale(self, c):
        assert isinstance(c, (int, Fraction, Decimal))
        if c == 1:
            return self
        else:
            return Monomial(c * self.coeff, self.factors)

    def __neg__(self):
        return self.scale(-1)

    def is_constant(self):
        return len(self.factors) == 0

    def get_constant(self):
        if len(self.factors) == 0:
            return self.coeff
        else:
            raise AssertionError

class Polynomial:
    """Represents a polynomial."""
    def __init__(self, monomials):
        monomials = tuple(monomials)
        assert all(isinstance(mono, Monomial) for mono in monomials)
        ts = collect_pairs((mono.factors, mono.coeff) for mono in monomials)
        self.monomials = tuple(Monomial(coeff, factor) for factor, coeff in ts)
        self.var = None
        if not self.is_nonzero_constant():
            self.var = self.monomials[0].var
        self.degree = 0 if self.is_nonzero_constant() else self.monomials[0].degree

    def __eq__(self, other):
        return isinstance(other, Polynomial) and self.monomials == other.monomials

    def __str__(self):
        if len(self.monomials) == 0:
            return "0"
        else:
            return " + ".join(str(mono) for mono in self.monomials)

    def __repr__(self):
        return "Polynomial(%s)" % str(self)

    def __add__(self, other):
        return Polynomial(self.monomials + other.monomials)

    def scale(self, c):
        return Polynomial(mono.scale(c) for mono in self.monomials)

    def __neg__(self):
        return self.scale(-1)

    def __sub__(self, other):
        return self + (-other)

    def __mul__(self, other):
        return Polynomial(m1 * m2 for m1 in self.monomials for m2 in other.monomials)

    def is_nonzero_constant(self):
        return len(self.monomials) == 1 and self.monomials[0].is_constant() and self.monomials[0].coeff != 0

    def is_zero_constant(self):
        return len(self.monomials) == 1 and self.monomials[0].is_constant() and self.monomials[0].coeff == 0 \
            or all(m.coeff == 0 for m in self.monomials)

    def del_zero_mono(self):
        np = []
        for m in self.monomials:
            if m.coeff != 0:
                np.append(m)
        return Polynomial(np)

    def get_constant(self):
        """If self is a constant, return the constant. Otherwise raise an exception."""
        if len(self.monomials) == 0:
            return 0
        elif len(self.monomials) == 1 and self.monomials[0].is_constant():
            return self.monomials[0].get_constant()
        else:
            raise AssertionError

    def standardize(self):
        """Sort the polynomial by the power value by descending order

        5*x^2 + 3*x^4 + 2 => 3*x^4 + 0*x^3 + 5*x^2 + 0*x^1 + 2

        """
        if self.is_nonzero_constant():
            return Polynomial(self.monomials)
        if self.monomials[-1].is_constant():
            np = list(self.monomials[:-1])
        else:
            np = list(self.monomials)
        de = self.degree
        for m in self.monomials:
            if not m.is_constant():
                while de != m.degree:
                    np.append(Monomial(0, ((self.var, de),)))
                    de -= 1
                de -= 1
        while de != 0:
            np.append(Monomial(0, ((self.var, de),)))
            de -= 1
        if self.monomials[-1].is_constant():
            np.append(self.monomials[-1])
        else:
            np.append(Monomial(0, tuple()))
        return Polynomial(np)


def singleton(s):
    """Polynomial for 1*s^1."""
    return Polynomial([Monomial(1, [(s, 1)])])

def constant(c):
    """Polynomial for c (numerical constant)."""
    assert isinstance(c, (int, Fraction, Decimal))
    return Polynomial([Monomial(c, tuple())])

# A simple parser for polynomials, where all variables are characters.
grammar = r"""
    ?factor: LETTER -> unit_factor
        | LETTER "^" INT -> factor

    ?monomial: (factor)* -> monomial
        | INT (factor)* -> int_monomial
        | DECIMAL (factor)* -> decimal_monomial

    ?polynomial: monomial ("+" monomial)* -> polynomial

    %import common.LETTER
    
    %import common.INT
    %import common.DECIMAL
    %import common.WS

    %ignore WS
"""

@v_args(inline=True)
class PolyTransformer(Transformer):
    def __init__(self):
        pass

    def unit_factor(self, name):
        return (str(name), 1)

    def factor(self, name, pow):
        return (str(name), int(pow))

    def monomial(self, *factors):
        return Monomial(1, factors)

    def int_monomial(self, n, *factors):
        return Monomial(int(n), factors)

    def decimal_factors(self, n, *factors):
        return Monomial(Decimal(n), factors)

    def polynomial(self, *monomials):
        return Polynomial(monomials)

mono_parser = Lark(grammar, start="monomial", parser="lalr", transformer=PolyTransformer())
poly_parser = Lark(grammar, start="polynomial", parser="lalr", transformer=PolyTransformer())

def parse_mono(s):
    return mono_parser.parse(s)

def parse_poly(s):
    try:
        return poly_parser.parse(s)
    except exceptions.UnexpectedCharacters as e:
        print("When parsing:", s)
        raise e