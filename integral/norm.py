"""Normalization of expressions."""

import math
from typing import Union
from fractions import Fraction

from integral.expr import Expr, Const, Integral
from integral import poly, expr
from integral.poly import Polynomial, from_poly, to_poly


def unfold_power(p: Polynomial, n: int) -> Polynomial:
    """Unfold power of a polynomial."""
    assert n >= 0
    if n == 0:
        return poly.constant(poly.const_fraction(1))

    res = p
    for i in range(n-1):
        res = p * res
    return res

class NormalQuotient:
    def __init__(self, num: Polynomial, denom: Polynomial):
        self.num = to_poly(from_poly(num))
        self.denom = to_poly(from_poly(denom))
    
    def __str__(self):
        return "(%s, %s)" % (from_poly(self.num), from_poly(self.denom))

    def to_expr(self) -> Expr:
        denom = from_poly(self.denom)
        if denom == Const(1):
            return from_poly(self.num)
        else:
            return from_poly(self.num) / denom

def add_normal_quotient(n1: NormalQuotient, n2: NormalQuotient) -> NormalQuotient:
    num = n1.num * n2.denom + n1.denom * n2.num
    denom = n1.denom * n2.denom
    return NormalQuotient(num, denom)

def uminus_normal_quotient(n: NormalQuotient) -> NormalQuotient:
    return NormalQuotient(-n.num, n.denom)

def minus_normal_quotient(n1: NormalQuotient, n2: NormalQuotient) -> NormalQuotient:
    return add_normal_quotient(n1, uminus_normal_quotient(n2))

def mult_normal_quotient(n1: NormalQuotient, n2: NormalQuotient) -> NormalQuotient:
    return NormalQuotient(n1.num * n2.num, n1.denom * n2.denom)

def inverse_normal_quotient(n: NormalQuotient) -> NormalQuotient:
    return NormalQuotient(n.denom, n.num)

def divide_normal_quotient(n1: NormalQuotient, n2: NormalQuotient) -> NormalQuotient:
    return mult_normal_quotient(n1, inverse_normal_quotient(n2))

def exp_normal_quotient(base: NormalQuotient, val: int):
    if val == 1:
        return base
    elif val == -1:
        return inverse_normal_quotient(base)
    elif isinstance(val, int):
        if val >= 0:
            return NormalQuotient(unfold_power(base.num, val),
                                  unfold_power(base.denom, val))
        else:
            return NormalQuotient(unfold_power(base.denom, -val),
                                  unfold_power(base.num, -val))
    elif isinstance(val, Fraction):
        if val >= 0:
            return NormalQuotient(poly.singleton(from_poly(base.num) ** val),
                                  poly.singleton(from_poly(base.denom) ** val))
        else:
            return NormalQuotient(poly.singleton(from_poly(base.denom) ** -val),
                                  poly.singleton(from_poly(base.num) ** -val))
    else:
        raise TypeError

def equal_normal_quotient(n1: NormalQuotient, n2: NormalQuotient) -> bool:
    e1 = from_poly(n1.num * n2.denom)
    e2 = from_poly(n1.denom * n2.num)
    return e1 == e2

def normalize_quotient(e: Expr) -> NormalQuotient:
    def rec(e: Expr) -> NormalQuotient:
        if e.is_plus():
            return add_normal_quotient(rec(e.args[0]), rec(e.args[1]))
        elif e.is_uminus():
            return uminus_normal_quotient(rec(e.args[0]))
        elif e.is_minus():
            return minus_normal_quotient(rec(e.args[0]), rec(e.args[1]))
        elif e.is_times():
            return mult_normal_quotient(rec(e.args[0]), rec(e.args[1]))
        elif e.is_divides():
            return divide_normal_quotient(rec(e.args[0]), rec(e.args[1]))
        elif e.is_power():
            if e.args[1].is_const():
                return exp_normal_quotient(rec(e.args[0]), e.args[1].val)
        elif e.is_fun():
            if e.func_name == 'sqrt':
                return rec(e.args[0] ** Const(Fraction(1,2)))
            else:
                e = expr.Fun(e.func_name, *(quotient_normalize(arg) for arg in e.args))

        # Un-handled cases
        return NormalQuotient(poly.singleton(e), poly.constant(poly.const_fraction(1)))

    return rec(e)

def quotient_normalize(t: Expr) -> Expr:
    return normalize_quotient(t).to_expr()

def eq_quotient(t1: Expr, t2: Expr) -> bool:
    n1 = normalize_quotient(t1)
    n2 = normalize_quotient(t2)
    return equal_normal_quotient(n1, n2)


class NormalPower:
    """A more general normal form for polynomials.
    
    NormalPower(p, q, m) represents the expression (p/q)^(1/m), where
    p and q are polynomials, and m is an integer >= 1.
    
    """
    def __init__(self, num: Polynomial, denom: Polynomial, root: int):
        self.num = num
        self.denom = denom
        self.root = root

    def __str__(self):
        return "(%s, %s, %s)" % (self.num, self.denom, self.root)

    def to_expr(self) -> Expr:
        denom = from_poly(self.denom)
        if denom == Const(1):
            inner = from_poly(self.num)
        else:
            inner = from_poly(self.num) / denom
        if self.root == Const(1):
            return inner
        else:
            return inner ** Const(Fraction(1, self.root))

def add_normal_power(n1: NormalPower, n2: NormalPower) -> NormalPower:
    """Add two normal forms.
    
    If both sides do not have roots, take common denominators.
    Not much is done otherwise.

    """
    if n1.root == 1 and n2.root == 1:
        num = n1.num * n2.denom + n1.denom * n2.num
        denom = n1.denom * n2.denom
        return NormalPower(num, denom, 1)
    elif n1.root == 1 and n2.root > 1:
        # p/q + y^(1/n) = (p + q * y^(1/n)) / q
        num = n1.num + n1.denom * poly.singleton(n2.to_expr())
        denom = n1.denom
        return NormalPower(num, denom, 1)
    elif n1.root > 1 and n2.root == 1:
        return add_normal_power(n2, n1)
    else:
        return NormalPower(poly.singleton(n1.to_expr()) + poly.singleton(n2.to_expr()),
                           poly.constant(poly.const_fraction(1)), 1)

def uminus_normal_power(n: NormalPower) -> NormalPower:
    """Negation of a normal form.
    
    If argument has roots, not much is done.

    """
    if n.root == 1:
        return NormalPower(-n.num, n.denom, 1)
    else:
        return NormalPower(-poly.singleton(n.to_expr()), n.denom, 1)

def minus_normal_power(n1: NormalPower, n2: NormalPower) -> NormalPower:
    return add_normal_power(n1, uminus_normal_power(n2))

def mult_normal_power(n1: NormalPower, n2: NormalPower) -> NormalPower:
    """Multiply two normal forms.
    
    If the two sides are (p/q)^(1/m) and (r/s)^(1/n), take the
    lcm of m and n to be k, then the product is
    
      (p^(k/m) * r^(k/n) / q^(k/m) * s^(k/n)) ^ (1/k)

    """
    root = math.lcm(n1.root, n2.root)
    p1 = root // n1.root
    p2 = root // n2.root
    num = unfold_power(n1.num, p1) * unfold_power(n2.num, p2)
    denom = unfold_power(n1.denom, p1) * unfold_power(n2.denom, p2)
    return NormalPower(num, denom, root)

def inverse_normal_power(n: NormalPower) -> NormalPower:
    """Inverse of normal form.
    
    The inverse of (p/q)^(1/m) is (q/p)^(1/m).

    """
    return NormalPower(n.denom, n.num, n.root)

def divide_normal_power(n1: NormalPower, n2: NormalPower) -> NormalPower:
    return mult_normal_power(n1, inverse_normal_power(n2))

def exp_normal_power(base: NormalPower, val: Union[int, Fraction]) -> NormalPower:
    if val == 1:
        return base
    elif val == -1:
        return inverse_normal_power(base)
    elif isinstance(val, int):
        if val >= 0:
            return NormalPower(unfold_power(base.num, val),
                               unfold_power(base.denom, val),
                               base.root)
        else:
            return NormalPower(unfold_power(base.denom, -val),
                               unfold_power(base.num, -val),
                               base.root)
    elif isinstance(val, Fraction):
        if val >= 0:
            return NormalPower(unfold_power(base.num, val.numerator),
                               unfold_power(base.denom, val.numerator),
                               base.root * val.denominator)
        else:
            return NormalPower(unfold_power(base.denom, -val.numerator),
                               unfold_power(base.num, -val.numerator),
                               base.root * val.denominator)
    else:
        raise TypeError

def equal_normal_power(n1: NormalPower, n2: NormalPower) -> bool:
    e1 = from_poly(n1.num * n2.denom)
    e2 = from_poly(n1.denom * n2.num)
    return n1.root == n2.root and e1 == e2

def normalize_power(e: Expr) -> NormalPower:
    def rec(e: Expr) -> NormalPower:
        if e.is_plus():
            return add_normal_power(rec(e.args[0]), rec(e.args[1]))
        elif e.is_uminus():
            return uminus_normal_power(rec(e.args[0]))
        elif e.is_minus():
            return minus_normal_power(rec(e.args[0]), rec(e.args[1]))
        elif e.is_times():
            return mult_normal_power(rec(e.args[0]), rec(e.args[1]))
        elif e.is_divides():
            return divide_normal_power(rec(e.args[0]), rec(e.args[1]))
        elif e.is_power():
            if e.args[1].is_const():
                return exp_normal_power(rec(e.args[0]), e.args[1].val)
        elif e.is_fun():
            if e.func_name == 'sqrt':
                return rec(e.args[0] ** Const(Fraction(1,2)))

        # Un-handled cases
        return NormalPower(poly.singleton(e), poly.constant(poly.const_fraction(1)), 1)

    return rec(e)

def power_normalize(t: Expr) -> Expr:
    return normalize_power(t).to_expr()

def eq_power(t1: Expr, t2: Expr) -> bool:
    n1 = normalize_power(t1)
    n2 = normalize_power(t2)
    return equal_normal_power(n1, n2)


class NormalLog:
    def __init__(self, e: Polynomial):
        self.e = e

    def __str__(self):
        return "(%s)" % from_poly(self.e)

    def to_expr(self) -> Expr:
        return from_poly(self.e)

def minus_normal_log(a: NormalLog, b: NormalLog) -> NormalLog:
    return NormalLog(a.e / b.e)

def add_normal_log(a: NormalLog, b: NormalLog) -> NormalLog:
    return NormalLog(a.e * b.e)

def normalize_log(e: Expr):
    def rec(e: Expr) -> NormalLog:
        if e.is_minus():
            return minus_normal_log(rec(e.args[0]), rec(e.args[1]))
        elif e.is_uminus():
            return NormalLog(rec(e.args[0]) ^ Const(-1))
        elif e.is_plus():
            return add_normal_log(rec(e.args[0]), rec(e.args[1]))
        elif e.is_fun() and e.func_name == 'log':
            return NormalLog(poly.singleton(e.args[0]))
        return NormalLog(poly.singleton(expr.Fun("exp",e)))

    return rec(e)

def equal_normal_log(t1: NormalLog, t2: NormalLog):
    e1 = from_poly(t1.e)
    e2 = from_poly(t2.e)
    return e1 == e2

def eq_log(t1: Expr, t2: Expr) -> bool:
    n1 = normalize_log(t1)
    n2 = normalize_log(t2)
    return equal_normal_log(n1, n2)

class NormalDefiniteIntegral:
    def __init__(self, var:str, lower: Polynomial, upper: Polynomial, body: Polynomial):
        self.var = var
        self.lower = to_poly(from_poly(lower))
        self.upper = to_poly(from_poly(upper))
        self.body = to_poly(from_poly(body))

    def __str__(self):
        return "INT(%s, %s, %s, %s)" % (self.var, from_poly(self.lower),from_poly(self.upper),from_poly(self.body))

    def to_expr(self) -> Expr:
        return from_poly(self.e)


def equal_normal_definite_integral(t1: NormalDefiniteIntegral, t2: NormalDefiniteIntegral):
    e1 = from_poly(t1.body),from_poly(t1.lower), from_poly(t1.upper)
    e2 = from_poly(t2.body),from_poly(t2.lower), from_poly(t2.upper)
    return e1 == e2

def add_normal_definite_integral(t1: NormalDefiniteIntegral, t2: NormalDefiniteIntegral):
    tmp = from_poly(t2.body)
    tmp = to_poly(tmp.subst(t2.var, expr.Var(t1.var)))
    return NormalDefiniteIntegral(t1.var, t1.lower, t1.upper, t1.body + tmp)

def minus_normal_definite_integral(t1: NormalDefiniteIntegral, t2: NormalDefiniteIntegral):
    tmp = from_poly(t2.body)
    tmp = to_poly(tmp.subst(t2.var, expr.Var(t1.var)))
    return NormalDefiniteIntegral(t1.var, t1.lower, t1.upper, t1.body - tmp)

def normalize_definite_integral(e: Expr):
    def rec(e: Expr) -> NormalDefiniteIntegral:
        if e.is_plus():
            return add_normal_definite_integral(rec(e.args[0]), rec(e.args[1]))
        elif e.is_minus():
            return minus_normal_definite_integral(rec(e.args[0]), rec(e.args[1]))
        elif e.is_integral():
            return NormalDefiniteIntegral(e.var, to_poly(e.lower), to_poly(e.upper), to_poly(e.body))
        return NormalDefiniteIntegral("_x", to_poly(Const(0)), to_poly(Const(1)), to_poly(e))
    return rec(e)

def eq_definite_integral(t1: Expr, t2: Expr) -> bool:
    n1 = normalize_definite_integral(t1)
    n2 = normalize_definite_integral(t2)
    return equal_normal_definite_integral(n1, n2)

def simp_definite_integral(e: Integral) -> Expr:
    if not e.is_integral():
        return e
    if e.body.is_odd(e.var) and from_poly(to_poly(e.lower)) == from_poly(to_poly(expr.Op("-", e.upper))):
        return Const(0)
    return e

