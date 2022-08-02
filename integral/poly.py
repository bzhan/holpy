"""Polynomials."""

from fractions import Fraction
from decimal import Decimal
from collections.abc import Iterable
from typing import Union
import sympy
import math

from integral import expr


def collect_pairs(ps):
    """
    Reduce a list of pairs by collecting into groups according to
    first components, and adding the second component for each group.

    It is assumed that the first components are hashable. The second
    components are either Expr, ConstantPolynomial, or numbers. Pairs
    whose second component equals zero are removed.

    e.g.    

    - [("x", 1), ("y", 2), ("x", 3)] => [("x", 4), ("y", 2)]
    - [("x", 1), ("x", -1), ("y", 1)] => [("y", 1)]

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
        elif isinstance(v, Polynomial):
            return Polynomial(tuple())
        elif isinstance(v, (int, Fraction)):
            return 0
        else:
            raise NotImplementedError

    res_list = []
    for k, v in res.items():
        if v != zero_for(v):
            res_list.append((k, v))
    
    return tuple(sorted(res_list, key=lambda p: p[0]))

def reduce_power(n, e):
    """Reduce n ^ e to normal form.
    
    Returns a list of (n_i, e_i), so that n ^ e equals (n_1 ^ e^1) * ... (n_k ^ e_k).

    If n has type Expr, n ^ e is left unchanged. If n is an integer,
    it is factored to simplify the representation.

    """
    if isinstance(n, expr.Expr):
        return ((n, e),)
    elif isinstance(n, int):
        if n >= 0:
            # Compute factors of n. Let n = (n_1 ^ e_1) * ... * (n_k ^ e_k), then
            # n ^ e = (n_1 ^ (e * e_1)) * ... * (n_k ^ (e * e_k)).
            return tuple((ni, e * ei) for ni, ei in sympy.factorint(n).items())
        else:
            # If n is negative, the denominator of e must be odd.
            # If the numerator of e is also odd, add an extra -1 factor.
            assert Fraction(e).denominator % 2 == 1, 'reduce_power: exponent has even denominator'
            if Fraction(e).numerator % 2 == 0:
                return tuple((ni, e * ei) for ni, ei in sympy.factorint(-n).items())
            else:
                return ((-1, 1),) + tuple((ni, e * ei) for ni, ei in sympy.factorint(-n).items())
    else:
        raise NotImplementedError

def extract_frac(ps):
    """Reduce (n_1 ^ e_1) * ... * (n_k ^ e_k) by extracting fractions.
    
    Collects the integer part of e_i into a separate coefficient. E.g.
    2 ^ (3/2) => 2 * 2^(1/2),
    2 ^ (-1/2) => 1/2 * 2^(1/2)
    
    """
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
    """
    Represents a monomial constant expression.

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
        assert isinstance(coeff, (int, Fraction)), \
                "ConstantMonomial: invalid coeff %s (type %s)" % (coeff, type(coeff))

        reduced_factors = []
        for n, e in factors:
            reduced_factors.extend(reduce_power(n, e))

        reduced_factors = tuple((i, j) for i, j in collect_pairs(reduced_factors) if j != 0)
        self.factors, coeff2 = extract_frac(reduced_factors)
        self.coeff = coeff * coeff2

    def __hash__(self):
        return hash(("CMONO", self.coeff, self.factors))

    def __eq__(self, other):
        if isinstance(other, (int, Fraction)):
            return self.is_fraction() and self.get_fraction() == other
        elif not isinstance(other, ConstantMonomial):
            return False
        else:
            return self.coeff == other.coeff and self.factors == other.factors

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

    def __repr__(self):
        return "ConstantMonomial(%s)" % str(self)

    def __le__(self, other):
        # Comparison is for ordering within a ConstantPolynomial only,
        # not intended for comparing the value of the ConstantMonomial.
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
        if isinstance(other, ConstantMonomial):
            inv_factors = tuple((n, -e) for n, e in other.factors)
            return ConstantMonomial(self.coeff * Fraction(1, other.coeff), self.factors + inv_factors)
        else:
            raise NotImplementedError

    def __pow__(self, exp):
        if isinstance(exp, (int, Fraction)) and int(exp) == exp:
            # Integer case
            return ConstantMonomial(Fraction(self.coeff) ** exp, [(n, e * exp) for n, e in self.factors])
        elif isinstance(exp, Fraction):
            # Fraction case
            coeff = Fraction(self.coeff)
            num, denom = coeff.numerator, coeff.denominator
            return ConstantMonomial(1, [(num, exp), (denom, -exp)] + [(n, e * exp) for n, e in self.factors])
        else:
            raise ValueError

    def is_fraction(self) -> bool:
        """Whether a constant monomial is a fraction.
        
        A ConstantMonomial is a fraction if the list of factors is empty.
        
        """
        return len(self.factors) == 0

    def get_fraction(self) -> Union[int, Fraction]:
        """Obtain the fraction of a ConstantMonomial."""
        return self.coeff


class ConstantPolynomial:
    """
    Represents a sum of constant monomials

    monomials - a list of ConstantMonomial.

    """
    def __init__(self, monomials):
        ts = collect_pairs((mono.factors, mono.coeff) for mono in monomials)
        self.monomials = tuple(ConstantMonomial(coeff, factor) for factor, coeff in ts)

    def __str__(self):
        if len(self.monomials) == 0:
            return "0"
        else:
            return " + ".join(str(mono) for mono in self.monomials)

    def __repr__(self) -> str:
        return "ConstantPolynomial(%s)" % str(self)

    def __hash__(self):
        return hash(("CPOLY", self.monomials))

    def __eq__(self, other):
        if isinstance(other, (int, Fraction)):
            return self.is_fraction() and self.get_fraction() == other
        elif not isinstance(other, ConstantPolynomial):
            return False
        else:
            return self.monomials == other.monomials

    def __le__(self, other):
        return self.monomials <= other.monomials

    def __lt__(self, other):
        return self <= other and self != other

    def __add__(self, other):
        if isinstance(other, ConstantPolynomial):
            return ConstantPolynomial(self.monomials + other.monomials)
        else:
            raise AssertionError("other: %s" % other)

    def __neg__(self):
        return ConstantPolynomial([-m for m in self.monomials])

    def __sub__(self, other):
        return self + (-other)

    def __mul__(self, other):
        if isinstance(other, (int, Fraction)):
            return ConstantPolynomial(m * other for m in self.monomials)
        elif isinstance(other, ConstantPolynomial):
            return ConstantPolynomial(m1 * m2 for m1 in self.monomials for m2 in other.monomials)
        elif isinstance(other, Polynomial):
            return Polynomial([Monomial(self * mono.coeff, mono.factors) for mono in other.monomials])
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

    def is_zero(self) -> bool:
        """Whether self equals zero."""
        return len(self.monomials) == 0

    def is_monomial(self) -> bool:
        """Whether self has only one monomial."""
        return len(self.monomials) == 1

    def get_monomial(self) -> ConstantMonomial:
        """Returns the only monomial in self."""
        return self.monomials[0]

    def is_fraction(self) -> bool:
        """Whether self is a fraction."""
        if len(self.monomials) == 0:
            return True
        return self.is_monomial() and self.get_monomial().is_fraction()

    def get_fraction(self) -> Union[int, Fraction]:
        """Convert self to fraction."""
        if len(self.monomials) == 0:
            return 0
        else:
            return self.get_monomial().get_fraction()

    def is_one(self) -> bool:
        return self.is_fraction() and self.get_fraction() == 1

    def is_minus_one(self) -> bool:
        return self.is_fraction() and self.get_fraction() == -1


def const_singleton(t: expr.Expr) -> ConstantPolynomial:
    """Returns the constant polynomial equals to t."""
    return ConstantPolynomial([ConstantMonomial(1, [(t, 1)])])

def const_fraction(r: Union[int, Fraction]) -> ConstantPolynomial:
    """Returns the constant polynomial equals to fraction r."""
    return ConstantPolynomial([ConstantMonomial(r, [])])


class Monomial:
    """Represents a monomial."""
    def __init__(self, coeff, factors):
        """Construct a monomial from coefficient and tuple of factors,
        where each factor is associated its power. For example,

        (2, ()) -> 2
        (2, ((x, 1))) -> 2 * x
        (2, ((x, 2), (y, 1))) -> 2 * x^2 * y

        coeff: ConstantPolynomial - coefficient of the monomial.

        """
        if isinstance(coeff, (int, Fraction)):
            coeff = const_fraction(coeff)
        elif isinstance(coeff, expr.Expr):
            coeff = const_singleton(coeff)
        assert isinstance(coeff, ConstantPolynomial), "Unexpected coeff: %s" % str(coeff)

        self.coeff = coeff
        self.factors = []
        for base, power in factors:
            if isinstance(power, (int, Fraction)):
                power = constant(const_fraction(power))
            assert isinstance(power, Polynomial), "Unexpected power: %s" % str(power)
            self.factors.append((base, power))
        self.factors = tuple((i, j) for i, j in collect_pairs(self.factors))

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
            if res:
                res += " * " + s
            else:
                res = s

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
        if isinstance(other, Monomial):
            inv_factors = tuple((n, -e) for n, e in other.factors)
            return Monomial(self.coeff / other.coeff, self.factors + inv_factors)
        else:
            raise NotImplementedError

    def __pow__(self, exp):
        # Assume the power is a fraction
        if isinstance(exp, int) or (isinstance(exp, Fraction) and exp.denominator % 2 == 1):
            return Monomial(self.coeff ** exp, [(n, e * exp) for n, e in self.factors])
        elif isinstance(exp, Fraction) and exp.denominator % 2 == 0:
            sqrt_factors = []
            for n, e in self.factors:
                if isinstance(n, expr.Expr) and e.is_fraction() and e.get_fraction() % 2 == 0:
                    sqrt_factors.append((expr.Fun('abs', n), e * exp))
                else:
                    sqrt_factors.append((n, e * exp))
            return Monomial(self.coeff ** exp, sqrt_factors)
        else:
            raise ValueError

    def is_constant(self) -> bool:
        return len(self.factors) == 0

    def get_constant(self) -> ConstantPolynomial:
        if len(self.factors) == 0:
            return self.coeff
        else:
            raise AssertionError

    def is_fraction(self) -> bool:
        return len(self.factors) == 0 and self.coeff.is_fraction()

    def get_fraction(self) -> Union[int, Fraction]:
        return self.coeff.get_fraction()

    def to_frac(self) -> "FracPoly":
        """Convert the monomial to a fraction of Polynomials.
        
        This is done by collecting factors with positive power into the numerator
        and factors with negative power into the denominator.
        
        """
        pos_facs, neg_facs = [], []
        for i, j in self.factors:
            if isinstance(j, Polynomial):
                if len(j.monomials) == 1:
                    coeff = j.monomials[0].coeff.get_fraction()
                    if coeff > 0:
                        pos_facs.append((i, j))
                    elif coeff < 0:
                        neg_facs.append((i, -j))
                    else:
                        raise ValueError
                else:
                    pos_facs.append((i, j))
            elif isinstance(j, int) or isinstance(j, Fraction):
                if j > 0:
                    pos_facs.append((i, j))
                elif j < 0:
                    neg_facs.append((i, -j))
                else:
                    raise ValueError
            else:
                raise TypeError
        nm = Polynomial([Monomial(self.coeff, pos_facs)])
        denom = Polynomial([Monomial(1, neg_facs)])
        return FracPoly(nm, denom)


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

    def __len__(self):
        return len(self.monomials)

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
            # Applies distributivity - could expand the number of terms exponentially
            return Polynomial(m1 * m2 for m1 in self.monomials for m2 in other.monomials)
        elif isinstance(other, ConstantPolynomial):
            return other * self
        else:
            raise NotImplementedError

    def __truediv__(self, other):
        # Assume the denominator is a monomial
        if isinstance(other, Polynomial):
            if len(other.monomials) == 1:
                return Polynomial([m / other.monomials[0] for m in self.monomials])
            else:
                raise ValueError
        else:
            raise NotImplementedError

    def __pow__(self, exp):
        # Assume self is a monomial and exp is a fraction
        if len(self.monomials) == 1 and isinstance(exp, (int, Fraction)):
            return Polynomial([self.monomials[0] ** exp])
        else:
            raise ValueError('%s, %s' % (self, exp))

    def is_monomial(self) -> bool:
        return len(self.monomials) == 1

    def get_monomial(self) -> Monomial:
        if self.is_monomial():
            return self.monomials[0]
        else:
            raise AssertionError("get_monomial")

    def is_fraction(self) -> bool:
        if len(self.monomials) == 0:
            return True
        return self.is_monomial() and self.get_monomial().is_fraction()

    def get_fraction(self) -> Union[int, Fraction]:
        if len(self.monomials) == 0:
            return 0
        else:
            return self.get_monomial().get_fraction()
        
    def get_constant(self) -> Union[int, ConstantPolynomial]:
        """If self is a constant, return the constant. Otherwise raise an exception."""
        if len(self.monomials) == 0:
            return 0
        elif len(self.monomials) == 1 and self.monomials[0].is_constant():
            return self.monomials[0].get_constant()
        else:
            raise AssertionError

    def to_frac(self) -> "FracPoly":
        """Convert self to a fraction."""
        frac_monos = [m.to_frac() for m in self.monomials]
        return sum(frac_monos[1:], frac_monos[0])

    def is_one(self) -> bool:
        return len(self.monomials) == 1 and self.monomials[0].is_one()


def singleton(s: expr.Expr) -> Polynomial:
    """Polynomial for 1*s^1."""
    return Polynomial([Monomial(const_fraction(1), [(s, 1)])])

def constant(c: ConstantPolynomial) -> Polynomial:
    """Polynomial for c (numerical constant)."""
    assert isinstance(c, ConstantPolynomial), "Unexpected constant: %s, type: %s" % (str(c), type(c))
    return Polynomial([Monomial(c, tuple())])

class FracPoly:
    """A fraction in which both of numerator and denominator are polynomials.
    """
    def __init__(self, numerator, denom):
        assert isinstance(numerator, Polynomial) and isinstance(denom, Polynomial)
        self.nm = numerator
        self.denom = denom

    def __str__(self):
        return "%s / %s" % (self.nm, self.denom)

    def __repr__(self):
        return "FracPoly(%s)" % str(self)

    def __hash__(self):
        return hash(("FracPoly", self.nm, self.denom))

    def __add__(self, other):
        if self.denom == other.denom:
            return FracPoly(self.nm + other.nm, self.denom)
        comm_denoms = set(self.denom.monomials) | set(other.denom.monomials)
        left = set(other.denom.monomials) - set(self.denom.monomials)
        right = set(self.denom.monomials) - set(other.denom.monomials)
        return FracPoly(self.nm * Polynomial(list(left)) +
                        other.nm * Polynomial(list(right)), Polynomial(list(comm_denoms)))
