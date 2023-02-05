"""Polynomials."""

from fractions import Fraction
from typing import Union
import functools
import operator
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

    def is_one(self) -> bool:
        return len(self.monomials) == 1 and self.monomials[0].is_one()


def singleton(s: expr.Expr) -> Polynomial:
    """Polynomial for 1*s^1."""
    return Polynomial([Monomial(const_fraction(1), [(s, 1)])])

def constant(c: ConstantPolynomial) -> Polynomial:
    """Polynomial for c (numerical constant)."""
    assert isinstance(c, ConstantPolynomial), "Unexpected constant: %s, type: %s" % (str(c), type(c))
    return Polynomial([Monomial(c, tuple())])

"""
Conversion from expressions to polynomials.
"""

def is_square(r):
    return math.sqrt(r) * math.sqrt(r) == r

def to_const_poly(e: expr.Expr) -> ConstantPolynomial:
    """Normalize a constant expression.

    Assume e.is_constant() = True in this function.

    """
    if e.is_var():
        raise ValueError

    elif e.is_const():
        return const_fraction(e.val)

    elif e.is_inf():
        raise ValueError

    elif e.is_plus():
        return to_const_poly(e.args[0]) + to_const_poly(e.args[1])

    elif e.is_uminus():
        return -to_const_poly(e.args[0])

    elif e.is_minus():
        return to_const_poly(e.args[0]) - to_const_poly(e.args[1])

    elif e.is_times():
        return to_const_poly(e.args[0]) * to_const_poly(e.args[1])

    elif e.is_divides():
        a, b = to_const_poly(e.args[0]), to_const_poly(e.args[1])
        if b.is_fraction() and b.get_fraction() == 0:
            raise ZeroDivisionError("Zero denominator")
        if b.is_monomial():
            return a / b
        else:
            return a / const_singleton(from_const_poly(b))

    elif e.is_power():
        a, b = to_const_poly(e.args[0]), to_const_poly(e.args[1])
        if a.is_zero() and b.is_fraction() and b.get_fraction() > 0:
            return const_fraction(0)
        elif a.is_monomial() and b.is_fraction():
            return a ** b.get_fraction()
        elif b.is_fraction():
            rb = b.get_fraction()
            if rb > 0 and int(rb) == rb and rb <= 3:
                res = const_fraction(1)
                for i in range(int(rb)):
                    res *= a
                return res
            else:
                return const_singleton(from_const_poly(a) ** from_const_poly(b))
        else:
            return const_singleton(from_const_poly(a) ** from_const_poly(b))

    elif e.is_fun() and e.func_name == 'sqrt':
        a = to_const_poly(e.args[0])
        if a.is_fraction() and is_square(a.get_fraction()):
            return const_fraction(Fraction(math.sqrt(a.get_fraction())))
        elif a.is_monomial():
            return a ** Fraction(1 / 2)
        else:
            return const_singleton(expr.sqrt(from_const_poly(a)))

    elif e.is_fun() and e.func_name == 'pi':
        return const_singleton(expr.pi)

    elif e.is_fun() and e.func_name == 'exp':
        a = to_const_poly(e.args[0])
        if a.is_fraction() and a.get_fraction() == 0:
            return const_fraction(1)
        elif a.is_fraction():
            return ConstantPolynomial([ConstantMonomial(1, [(expr.E, a.get_fraction())])])
        elif e.args[0].is_fun() and e.args[0].func_name == "log":
            return to_const_poly(e.args[0].args[0])
        else:
            return const_singleton(expr.exp(from_const_poly(a)))

    elif e.is_fun() and e.func_name == 'log':
        a = to_const_poly(e.args[0])
        if a.is_fraction() and a.get_fraction() == 1:
            return const_fraction(0)
        elif a.is_monomial():
            mono = a.get_monomial()
            log_factors = []
            for n, e in mono.factors:
                if isinstance(n, (int, Fraction)):
                    log_factors.append(const_fraction(e) * const_singleton(expr.log(expr.Const(n))))
                elif isinstance(n, expr.Expr) and n == expr.E:
                    log_factors.append(const_fraction(e))
                elif isinstance(n, expr.Expr) and n.is_fun() and n.func_name == "exp":
                    body = n.args[0]
                    log_factors.append(const_singleton(body))
                else:
                    log_factors.append(const_fraction(e) * const_singleton(expr.log(n)))
            if mono.coeff == 1:
                return sum(log_factors[1:], log_factors[0])
            else:
                if isinstance(mono.coeff, int):
                    int_factors = sympy.factorint(mono.coeff)
                elif isinstance(mono.coeff, Fraction):
                    int_factors = sympy.factorint(mono.coeff.numerator)
                    denom_factors = sympy.factorint(mono.coeff.denominator)
                    for b, e in denom_factors.items():
                        if b not in int_factors:
                            int_factors[b] = 0
                        int_factors[b] -= e
                else:
                    raise NotImplementedError
                log_ints = []
                for b, e in int_factors.items():
                    log_ints.append(ConstantPolynomial([ConstantMonomial(e, [(expr.log(expr.Const(b)), 1)])]))
                return sum(log_factors + log_ints[1:], log_ints[0])
        else:
            return const_singleton(expr.log(from_const_poly(a)))

    elif e.is_fun() and e.func_name in ('sin', 'cos', 'tan', 'cot', 'csc', 'sec'):
        a = to_const_poly(e.args[0])
        norm_a = from_const_poly(a)

        c = expr.Symbol('c', [expr.CONST])
        if expr.match(norm_a, c * expr.pi):
            x = norm_a.args[0]
            n = int(x.val)
            if n % 2 == 0:
                norm_a = expr.Const(x.val - n) * expr.pi
            else:
                if n > 0:
                    norm_a = expr.Const(x.val - (n + 1)) * expr.pi
                else:
                    norm_a = expr.Const(x.val - (n - 1)) * expr.pi
        elif norm_a == -expr.pi:
            norm_a = expr.pi

        norm_a = normalize_constant(norm_a)
        if expr.match(norm_a, c * expr.pi) and norm_a.args[0].val < 0:
            neg_norm_a = expr.Const(-norm_a.args[0].val) * expr.pi
            if e.func_name in ('sin', 'tan', 'cot', 'csc'):
                val = -expr.Fun(e.func_name, neg_norm_a)
            else:
                val = expr.Fun(e.func_name, neg_norm_a)
            return to_const_poly(val)
        else:
            return const_singleton(expr.Fun(e.func_name, norm_a))

    elif e.is_fun() and e.func_name == "binom":
        norm_a = normalize_constant(e.args[0])
        norm_b = normalize_constant(e.args[1])
        if norm_a.is_const() and norm_b.is_const():
            return to_const_poly(expr.Const(math.comb(norm_a.val, norm_b.val)))
        else:
            return const_singleton(expr.binom(norm_a, norm_b))

    elif e.is_fun() and e.func_name == 'factorial':
        norm_a = normalize_constant(e.args[0])
        if norm_a.is_const() and int(norm_a.val) == float(norm_a.val):
            return to_const_poly(expr.Const(math.factorial(norm_a.val)))
        else:
            return const_singleton(expr.factorial(norm_a))

    elif e.is_fun():
        args_norm = [normalize_constant(arg) for arg in e.args]
        return const_singleton(expr.Fun(e.func_name, *args_norm))

    else:
        print("to_const_poly:", e)
        raise NotImplementedError

def normalize_constant(e):
    return from_const_poly(to_const_poly(e))

def to_poly(e: expr.Expr) -> Polynomial:
    """Convert expression to polynomial."""
    if e.is_var():
        return singleton(e)

    elif e.is_constant():
        # Consists of CONST, OP and FUN only.
        return constant(to_const_poly(e))

    elif e.is_plus():
        return to_poly(e.args[0]) + to_poly(e.args[1])

    elif e.is_uminus():
        return -to_poly(e.args[0])

    elif e.is_minus():
        return to_poly(e.args[0]) - to_poly(e.args[1])

    elif e.is_times():
        a, b = to_poly(e.args[0]), to_poly(e.args[1])
        if a.is_monomial() and b.is_monomial():
            return a * b
        elif a.is_fraction() or b.is_fraction():
            return a * b
        elif a.is_monomial():
            return a * singleton(from_poly(b))
        elif b.is_monomial():
            return b * singleton(from_poly(a))
        else:
            return singleton(from_poly(a)) * singleton(from_poly(b))

    elif e.is_divides():
        a, b = to_poly(e.args[0]), to_poly(e.args[1])
        if a.is_fraction() and a.get_fraction() == 0:
            return constant(const_fraction(0))
        elif b.is_fraction() and b.get_fraction() == 1:
            return a
        elif a.is_monomial() and b.is_monomial():
            return a / b
        elif a.is_monomial():
            return a / singleton(from_poly(b))
        elif b.is_monomial():
            return singleton(from_poly(a)) / b
        else:
            return singleton(from_poly(a)) / singleton(from_poly(b))

    elif e.is_power():
        a, b = to_poly(e.args[0]), to_poly(e.args[1])
        if a.is_monomial() and b.is_fraction():
            return a ** b.get_fraction()
        elif b.is_fraction():
            return Polynomial([Monomial(const_fraction(1), [(from_poly(a), b.get_fraction())])])
        else:
            return Polynomial([Monomial(const_fraction(1), [(from_poly(a), b)])])

    elif e.is_fun() and e.func_name == "exp":
        a = e.args[0]
        if a.is_fun() and a.func_name == "log":
            return to_poly(a.args[0])
        else:
            return Polynomial([Monomial(const_fraction(1), [(expr.E, to_poly(a))])])

    elif e.is_fun() and e.func_name in ("sin", "cos", "tan", "cot", "csc", "sec"):
        a = e.args[0]
        if a.is_fun() and a.func_name == "a" + e.func_name:
            # sin(asin(x)) = x
            return to_poly(a.args[0])
        else:
            return singleton(expr.Fun(e.func_name, normalize(a)))

    elif e.is_fun() and e.func_name in ("asin", "acos", "atan", "acot", "acsc", "asec"):
        a, = e.args
        if e.func_name in ("atan", "acot") and a.is_fun() and a.func_name == e.func_name[1:]:
            # atan(tan(x)) = x
            return to_poly(a.args[0])
        else:
            return singleton(expr.Fun(e.func_name, normalize(a)))

    elif e.is_fun() and e.func_name == "log":
        a, = e.args
        if a.is_fun() and a.func_name == "exp":
            return to_poly(a.args[0])
        elif a.is_op() and a.op == "^" and a.args[1].is_constant():
            return Polynomial([Monomial(to_const_poly(a.args[1]), [(expr.log(normalize(a.args[0])), 1)])])
        else:
            return singleton(expr.log(normalize(a)))

    elif e.is_fun() and e.func_name == "sqrt":
        return to_poly(expr.Op("^", e.args[0], expr.Const(Fraction(1, 2))))

    elif e.is_fun():
        args_norm = [normalize(arg) for arg in e.args]
        return singleton(expr.Fun(e.func_name, *args_norm))

    elif e.is_evalat():
        upper = e.body.subst(e.var, e.upper) if not e.upper.is_inf() else expr.Limit(e.var, e.upper, e.body)
        lower = e.body.subst(e.var, e.lower) if not e.lower.is_inf() else expr.Limit(e.var, e.lower, e.body)
        return to_poly(normalize(upper) - normalize(lower))

    elif e.is_integral():
        if e.lower == e.upper:
            return constant(to_const_poly(expr.Const(0)))
        body = normalize(e.body)
        return singleton(expr.Integral(e.var, normalize(e.lower), normalize(e.upper), body))

    elif e.is_limit():
        return singleton(expr.Limit(e.var, normalize(e.lim), normalize(e.body)))

    elif e.is_inf():
        if e == expr.POS_INF:
            return singleton(e)
        else:
            return -singleton(expr.POS_INF)
    elif e.is_indefinite_integral():
        return singleton(expr.IndefiniteIntegral(e.var, normalize(e.body), e.skolem_args))
    else:
        return singleton(e)

def normalize(e: expr.Expr) -> expr.Expr:
    if e.is_equals():
        return expr.Eq(normalize(e.lhs), normalize(e.rhs))
    return from_poly(to_poly(e))

"""
Conversion from polynomials to terms.
"""

def from_const_mono(m: ConstantMonomial) -> expr.Expr:
    """Convert a ConstantMonomial to an expression."""
    factors = []
    for base, power in m.factors:
        if isinstance(base, expr.Expr) and base == expr.E:
            factors.append(expr.exp(expr.Const(power)))
        else:
            if isinstance(base, int):
                base = expr.Const(base)
            if not isinstance(base, expr.Expr):
                raise ValueError
            if power == 1:
                factors.append(base)
            elif power == Fraction(1 / 2):
                factors.append(expr.sqrt(base))
            else:
                factors.append(base ** expr.Const(power))

    if len(factors) == 0:
        return expr.Const(m.coeff)
    elif m.coeff == 1:
        return functools.reduce(operator.mul, factors[1:], factors[0])
    elif m.coeff == -1:
        return - functools.reduce(operator.mul, factors[1:], factors[0])
    else:
        return functools.reduce(operator.mul, factors, expr.Const(m.coeff))


def rsize(e: expr.Expr) -> int:
    if e.is_const():
        return 0
    elif e.is_uminus():
        return rsize(e.args[0])
    elif e.is_times() and e.args[0].is_const():
        return rsize(e.args[1])
    else:
        return e.size()


def from_const_poly(p: ConstantPolynomial) -> expr.Expr:
    """Convert a ConstantPolynomial to an expression."""
    if len(p.monomials) == 0:
        return expr.Const(0)
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
                res = res - expr.Const(-mono.args[0].val) * mono.args[1]
            elif mono.is_const() and mono.val < 0:
                res = res - expr.Const(-mono.val)
            else:
                res = res + mono
        return res


def from_mono(m: Monomial) -> expr.Expr:
    """Convert a monomial to an expression."""
    factors = []
    for base, power in m.factors:
        if isinstance(base, expr.Expr) and base == expr.E:
            if isinstance(power, Polynomial):
                factors.append(expr.exp(from_poly(power)))
            else:
                factors.append(expr.exp(expr.Const(power)))
        else:
            if power == 1:
                factors.append(base)
            elif power == Fraction(1 / 2):
                factors.append(expr.sqrt(base))
            elif isinstance(power, (int, Fraction)):
                factors.append(base ** expr.Const(power))
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


def from_poly(p: Polynomial) -> expr.Expr:
    """Convert a polynomial to an expression."""

    if len(p.monomials) == 0:
        return expr.Const(0)
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
                res = res - expr.Const(-mono.args[0].val) * mono.args[1]
            elif mono.is_const() and mono.val < 0:
                res = res - expr.Const(-mono.val)
            else:
                res = res + mono
        return res
