"""Polynomials over arbitrary terms."""

from fractions import Fraction
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
    return tuple(sorted((k, v) for k, v in res.items() if v != 0))

class Monomial:
    """Represents a monomial."""
    def __init__(self, coeff, factors):
        """Construct a monomial from coefficient and tuple of factors,
        where each factor is associated its power. For example,

        (2, ()) -> 2
        (2, ((x, 1))) -> 2 * x
        (2, ((x, 2), (y, 1))) -> 2 * x^2 * y

        """
        assert isinstance(coeff, (int, Fraction))
        assert all(isinstance(factor, Iterable) and len(factor) == 2 and \
            isinstance(factor[1], int) for factor in factors), \
            "Unexpected argument for factors: %s" % str(factors)
        self.coeff = coeff
        self.factors = collect_pairs(factors)

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
            if p != 1:
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

    def scale(self, c):
        if c == 1:
            return self
        else:
            return Monomial(c * self.coeff, self.factors)

    def __neg__(self):
        return self.scale(-1)

    def is_constant(self):
        return len(self.factors) == 0

    def get_constant(self):
        assert self.is_constant()
        return self.coeff


class Polynomial:
    """Represents a polynomial."""
    def __init__(self, monomials):
        monomials = tuple(monomials)
        assert all(isinstance(mono, Monomial) for mono in monomials)
        ts = collect_pairs((mono.factors, mono.coeff) for mono in monomials)
        self.monomials = tuple(Monomial(coeff, factor) for factor, coeff in ts)

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

    def __pow__(self, other):
        assert isinstance(other, int) and other >= 0
        if other == 0:
            return Polynomial([Monomial(1, [])])

        res = self
        for i in range(other-1):
            res *= self
        return res

    def is_nonzero_constant(self):
        return len(self.monomials) == 1 and self.monomials[0].is_constant()

    def is_zero_constant(self):
        return len(self.monomials) == 0

    def is_constant(self):
        return self.is_nonzero_constant() or self.is_zero_constant()

    def get_constant(self):
        if self.is_zero_constant():
            return 0
        elif self.is_nonzero_constant():
            return self.monomials[0].get_constant()
        else:
            raise AssertionError


def singleton(s):
    """Polynomial for 1*s^1."""
    return Polynomial([Monomial(1, [(s, 1)])])

def constant(c):
    """Polynomial for c (numerical constant)."""
    assert isinstance(c, (int, Fraction))
    if isinstance(c, Fraction) and c.denominator == 1:
        return Polynomial([Monomial(c.numerator, tuple())])
    else:
        return Polynomial([Monomial(c, tuple())])
