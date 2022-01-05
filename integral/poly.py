"""Polynomials."""

from lark import Lark, Transformer, v_args, exceptions
from fractions import Fraction
from decimal import Decimal
from collections.abc import Iterable
import sympy
import math

from integral import expr


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
    
    def zero_for(v):
        if isinstance(v, expr.Expr):
            return expr.Const(0)
        elif isinstance(v, ConstantPolynomial):
            return ConstantPolynomial(tuple())
        else:
            return 0

    res_list = []
    for k, v in res.items():
        if v != zero_for(v):
            res_list.append((k, v))
    
    return tuple(sorted(res_list, key=lambda p: p[0]))

def reduce_power(n, e):
    """Reduce n^e to normal form."""
    if isinstance(n, expr.Expr):
        return ((n, e),)
    elif isinstance(n, int):
        if n >= 0:
            return tuple((ni, e * ei) for ni, ei in sympy.factorint(n).items())
        else:
            assert Fraction(e).denominator % 2 == 1, 'reduce_power'
            return ((-1, 1),) + tuple((ni, e * ei) for ni, ei in sympy.factorint(-n).items())
    else:
        raise NotImplementedError

def extract_frac(ps):
    """Given a list of pairs (n, e), reduce list by collecting rational coefficient."""
    res = []
    coeff = 1

    for n, e in ps:
        if isinstance(n, int):
            if e >= 1:
                coeff *= (n ** math.floor(e))
            if e < 0:
                coeff *= Fraction(1, n ** (-math.floor(e)))
            if e - math.floor(e) != 0:
                res.append((n, e - math.floor(e)))
        else:
            res.append((n, e))
    return tuple(res), coeff


class ConstantMonomial:
    """Represents a monomial constant expression.

    The expression is in the form

    c * p_1 ^ e_1 * p_2 ^ e_2 ... * p_k ^ e_k * Pi ^ e_Pi * exp(n) *
        t_1 ^ f_1 * t_2 ^ f_2 ... * t_k ^ f_k

    Here c is a rational number, each p_i are primes and e_i are fractions
    between 0 and 1 (exclusive). e_Pi is the exponent of Pi and n is the
    exponent of e (both arbitrary fractions). Each t_i is a distinct
    term that cannot be further simplified. Each f_i are non-zero fractions.

    """
    def __init__(self, coeff, factors):
        """Construct a monomial from coefficient and tuple of factors."""
        assert isinstance(coeff, (int, Fraction)) or \
            coeff == Decimal("inf") or coeff == Decimal("-inf"), \
                "coeff: %s, factors: %s" % (coeff, factors)

        reduced_factors = []
        for n, e in factors:
            reduced_factors.extend(reduce_power(n, e))

        reduced_factors = tuple((i, j) for i, j in collect_pairs(reduced_factors) if j != 0)
        self.factors, coeff2 = extract_frac(reduced_factors)
        self.coeff = coeff * coeff2

    def __hash__(self):
        return hash(("CMONO", self.coeff, self.factors))

    def __str__(self):
        def print_pair(n, e):
            if isinstance(n, expr.Expr) and n == expr.E:
                str_base = "e"
            elif isinstance(n, int) or (isinstance(n, expr.Expr) and n.priority() > expr.op_priority['^']):
                str_base = str(n)
            else:
                str_base = "(" + str(n) + ")"
            if e == 1:
                return str_base
            elif isinstance(e, int) or (isinstance(e, Fraction) and e.denominator == 1):
                str_exp = str(e)
            else:
                str_exp = "(" + str(e) + ")"
            return str_base + "^" + str_exp

        if not self.factors:
            return str(self.coeff)

        str_factors = " * ".join(print_pair(n, e) for n, e in self.factors)
        if self.coeff == 1:
            return str_factors
        else:
            return str(self.coeff) + " * " + str_factors

    def __repr__(self) -> str:
        return str(self)

    def __le__(self, other):
        if len(self.factors) < len(other.factors):
            return True
        elif len(self.factors) > len(other.factors):
            return False
        else:
            return (self.factors, self.coeff) <= (other.factors, other.coeff)

    def __lt__(self, other):
        return self <= other and self != other

    def __neg__(self):
        return ConstantMonomial(-1 * self.coeff, self.factors)

    def __mul__(self, other):
        if isinstance(other, (int, Fraction)):
            return ConstantMonomial(self.coeff * other, self.factors)
        elif isinstance(other, ConstantMonomial):
            return ConstantMonomial(self.coeff * other.coeff, self.factors + other.factors)
        else:
            raise NotImplementedError

    def __truediv__(self, other):
        inv_factors = tuple((n, -e) for n, e in other.factors)
        return ConstantMonomial(self.coeff * Fraction(1,other.coeff), self.factors + inv_factors)

    def __pow__(self, exp):
        # Assume the power is a fraction
        if isinstance(exp, (int, Fraction)) and int(exp) == exp:
            return ConstantMonomial(Fraction(self.coeff) ** exp, [(n, e * exp) for n, e in self.factors])
        elif isinstance(exp, Fraction):
            coeff = Fraction(self.coeff)
            num, denom = coeff.numerator, coeff.denominator
            return ConstantMonomial(1, [(num, exp), (denom, -exp)] + [(n, e * exp) for n, e in self.factors])
        else:
            raise ValueError

    def is_fraction(self):
        return len(self.factors) == 0

    def get_fraction(self):
        return self.coeff


class ConstantPolynomial:
    """Represents a sum of constant monomials"""
    def __init__(self, monomials):
        ts = collect_pairs((mono.factors, mono.coeff) for mono in monomials)
        self.monomials = tuple(ConstantMonomial(coeff, factor) for factor, coeff in ts if coeff != 0)

    def __str__(self):
        if len(self.monomials) == 0:
            return "0"
        else:
            return " + ".join(str(mono) for mono in self.monomials)

    def __hash__(self):
        return hash(("CPOLY", self.monomials))

    def __eq__(self, other):
        if isinstance(other, (int, Fraction)):
            return self.is_fraction() and self.get_fraction() == other
        
        return isinstance(other, ConstantPolynomial) and self.monomials == other.monomials

    def __le__(self, other):
        return self.monomials <= other.monomials

    def __lt__(self, other):
        return self <= other and self != other

    def __add__(self, other):
        return ConstantPolynomial(self.monomials + other.monomials)

    def __neg__(self):
        return ConstantPolynomial([-m for m in self.monomials])

    def __sub__(self, other):
        return self + (-other)

    def __mul__(self, other):
        if isinstance(other, (int, Fraction)):
            return ConstantPolynomial(m * other for m in self.monomials)
        elif isinstance(other, ConstantPolynomial):
            return ConstantPolynomial(m1 * m2 for m1 in self.monomials for m2 in other.monomials)
        else:
            raise NotImplementedError

    def __truediv__(self, other):
        # Assume the denominator is a monomial
        if len(other.monomials) == 1:
            return ConstantPolynomial([m / other.monomials[0] for m in self.monomials])
        else:
            raise ValueError

    def __pow__(self, exp):
        # Assume self is a monomial and exp is a fraction
        if len(self.monomials) == 1 and isinstance(exp, (int, Fraction)):
            return ConstantPolynomial([self.monomials[0] ** exp])
        else:
            raise ValueError('%s, %s' % (self, exp))

    def is_zero(self):
        return len(self.monomials) == 0

    def is_monomial(self):
        """Whether self has only one monomial."""
        return len(self.monomials) == 1

    def get_monomial(self):
        """Returns the only monomial in self."""
        return self.monomials[0]

    def is_fraction(self):
        """Whether self is a fraction."""
        if len(self.monomials) == 0:
            return True
        return self.is_monomial() and self.get_monomial().is_fraction()

    def get_fraction(self):
        """Convert self to fraction."""
        if len(self.monomials) == 0:
            return 0
        else:
            return self.get_monomial().get_fraction()

    def is_one(self):
        return self.is_fraction() and self.get_fraction() == 1

    def is_minus_one(self):
        return self.is_fraction() and self.get_fraction() == -1

def const_singleton(t):
    return ConstantPolynomial([ConstantMonomial(1, [(t, 1)])])

def const_fraction(r):
    return ConstantPolynomial([ConstantMonomial(r, [])])

class Monomial:
    """Represents a monomial."""
    def __init__(self, coeff, factors):
        """Construct a monomial from coefficient and tuple of factors,
        where each factor is associated its power. For example,

        (2, ()) -> 2
        (2, ((x, 1))) -> 2 * x
        (2, ((x, 2), (y, 1))) -> 2 * x^2 * y

        """
        if isinstance(coeff, (int, Fraction)):
            coeff = const_fraction(coeff)
        elif isinstance(coeff, expr.Expr):
            coeff = const_singleton(coeff)
        assert isinstance(coeff, ConstantPolynomial), "Unexpected coeff: %s" % str(coeff)
        assert all(isinstance(factor, Iterable) and len(factor) == 2 and \
            isinstance(factor[1], (int, Fraction, Polynomial)) for factor in factors), \
            "Unexpected argument for factors: %s" % str(factors)

        self.coeff = coeff
        self.factors = tuple((i, j) for i, j in collect_pairs(factors) if j != 0)

    def __hash__(self):
        return hash(("MONO", self.coeff, self.factors))

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
        return (self.factors, self.coeff) <= (other.factors, other.coeff)

    def __lt__(self, other):
        return self <= other and self != other

    def __mul__(self, other):
        if isinstance(other, (int, Fraction)):
            return Monomial(self.coeff * other, self.factors)
        elif isinstance(other, Monomial):
            return Monomial(self.coeff * other.coeff, self.factors + other.factors)
        else:
            raise NotImplementedError

    def __neg__(self):
        return Monomial(const_fraction(-1) * self.coeff, self.factors)

    def __truediv__(self, other):
        inv_factors = tuple((n, -e) for n, e in other.factors)
        return Monomial(self.coeff / other.coeff, self.factors + inv_factors)

    def __pow__(self, exp):
        # Assume the power is a fraction
        if isinstance(exp, int) or (isinstance(exp, Fraction) and exp.denominator % 2 == 1):
            return Monomial(self.coeff ** exp, [(n, e * exp) for n, e in self.factors])
        elif isinstance(exp, Fraction) and exp.denominator % 2 == 0:
            sqrt_factors = []
            for n, e in self.factors:
                if isinstance(n, expr.Expr) and isinstance(e, int) and e % 2 == 0:
                    sqrt_factors.append((expr.Fun('abs', n), e * exp))
                else:
                    sqrt_factors.append((n, e * exp))
            return Monomial(self.coeff ** exp, sqrt_factors)
        else:
            raise ValueError

    def is_constant(self):
        return len(self.factors) == 0

    def get_constant(self):
        if len(self.factors) == 0:
            return self.coeff
        else:
            raise AssertionError

    def is_fraction(self):
        return len(self.factors) == 0 and self.coeff.is_fraction()

    def get_fraction(self):
        return self.coeff.get_fraction()

    @property
    def degree(self):
        if len(self.factors) == 0:
            return 0
        else:
            return self.factors[-1][1]


class Polynomial:
    """Represents a polynomial."""
    def __init__(self, monomials):
        monomials = tuple(monomials)
        assert all(isinstance(mono, Monomial) for mono in monomials)
        ts = collect_pairs((mono.factors, mono.coeff) for mono in monomials)
        self.monomials = tuple(Monomial(coeff, factor) for factor, coeff in ts if coeff != 0)

    def __eq__(self, other):
        if isinstance(other, (int, Fraction)):
            return self.is_fraction() and self.get_fraction() == other

        return isinstance(other, Polynomial) and self.monomials == other.monomials

    def __le__(self, other):
        return self.monomials <= other.monomials

    def __lt__(self, other):
        return self <= other and self != other

    def __hash__(self):
        return hash(("POLY", self.monomials))

    def __str__(self):
        if len(self.monomials) == 0:
            return "0"
        else:
            return " + ".join(str(mono) for mono in self.monomials)

    def __repr__(self):
        return "Polynomial(%s)" % str(self)

    def __add__(self, other):
        return Polynomial(self.monomials + other.monomials)

    def __neg__(self):
        return Polynomial([-m for m in self.monomials])

    def __sub__(self, other):
        return self + (-other)

    def __mul__(self, other):
        if isinstance(other, (int, Fraction)):
            return Polynomial(m * other for m in self.monomials)
        elif isinstance(other, Polynomial):
            return Polynomial(m1 * m2 for m1 in self.monomials for m2 in other.monomials)
        else:
            raise NotImplementedError

    def __truediv__(self, other):
        # Assume the denominator is a monomial
        if len(other.monomials) == 1:
            return Polynomial([m / other.monomials[0] for m in self.monomials])
        else:
            raise ValueError

    def __pow__(self, exp):
        # Assume self is a monomial and exp is a fraction
        if len(self.monomials) == 1 and isinstance(exp, (int, Fraction)):
            return Polynomial([self.monomials[0] ** exp])
        else:
            raise ValueError('%s, %s' % (self, exp))

    def is_monomial(self):
        return len(self.monomials) == 1

    def get_monomial(self):
        return self.monomials[0]

    def is_fraction(self):
        if len(self.monomials) == 0:
            return True
        return self.is_monomial() and self.get_monomial().is_fraction()

    def get_fraction(self):
        if len(self.monomials) == 0:
            return 0
        else:
            return self.get_monomial().get_fraction()
        
    def get_constant(self):
        """If self is a constant, return the constant. Otherwise raise an exception."""
        if len(self.monomials) == 0:
            return 0
        elif len(self.monomials) == 1 and self.monomials[0].is_constant():
            return self.monomials[0].get_constant()
        else:
            raise AssertionError

    def is_univariate(self):
        """Determine polynomial is whether univariate.
        
        If there is unique f(x) occurs in polynomial, it is univariate.
        """
        d = set()
        for mono in self.monomials:
            if len(mono.factors) > 1:
                return False
            if len(mono.factors) == 1:
                d.add(mono.factors[0][0])
        
        return len(d) <= 1

    def is_multivariate(self):
        return not self.is_univariate()

    @property
    def degree(self):
        return self.monomials[-1].degree

def singleton(s):
    """Polynomial for 1*s^1."""
    return Polynomial([Monomial(const_fraction(1), [(s, 1)])])

def constant(c):
    """Polynomial for c (numerical constant)."""
    assert isinstance(c, ConstantPolynomial), "Unexpected constant: %s, type: %s" % (str(c), type(c))
    return Polynomial([Monomial(c, tuple())])
