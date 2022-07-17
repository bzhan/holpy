"""Unit test for polynomial module."""

import unittest

from integral import expr
from integral.expr import Var, Const, pi, E
from integral.poly import ConstantMonomial, Monomial
from decimal import Decimal
from fractions import Fraction

class PolynomialTest(unittest.TestCase):
    def testPrintMonomial(self):
        test_data = [
            (Monomial(1, []), "1"),
            (Monomial(2, []), "2"),
            (Monomial(0, []), "0"),
            (Monomial(2, [("x", 1)]), "2 * x"),
            (Monomial(2, [("x", 2)]), "2 * x^2"),
            (Monomial(2, [("x", 2), ("y", 2)]), "2 * x^2 * y^2"),
            (Monomial(2, [("y", 2), ("x", 2)]), "2 * x^2 * y^2"),
            (Monomial(2, [("x+y", 2)]), "2 * (x+y)^2"),
            (Monomial(2, [("x", 1), ("x", 2)]), "2 * x^3"),
            (Monomial(1, [("x", Fraction(1, 2))]), "x ^ 1/2"),
            (Monomial(1, [("x", Fraction(1, 2)), ("x", Fraction(1, 2))]), "x")
        ]

        for m, s in test_data:
            self.assertEqual(str(m), s)

    def testConstantMonomial(self):
        test_data = [
            (1, [], "1"),
            (1, [(2, "1/2")], "2^(1/2)"),
            (1, [(2, "3/2")], "2 * 2^(1/2)"),
            (1, [(2, "-1/2")], "1/2 * 2^(1/2)"),
            (1, [(6, "1/2")], "2^(1/2) * 3^(1/2)"),
            (1, [(pi, "1/2")], "pi^(1/2)"),
            (1, [(E, "1/2")], "e^(1/2)"),
            (1, [(9, "1/2")], "3"),
            (1, [(2, 2)], "4"),
            (1, [(8, "1/2"), (6, "1/2"), (9, "1/3")], "12 * 3^(1/6)"),
            (1, [(expr.sin(Const(1)), 2)], "sin(1)^2"),
            (1, [(expr.sin(Const(1)) + expr.sin(Const(2)), 2)], "(sin(1) + sin(2))^2"),
        ]

        for coeff, factors, res in test_data:
            factors = [(n, Fraction(e)) for n, e in factors]
            mono = ConstantMonomial(coeff, factors)
            self.assertEqual(str(mono), res)

    def testMultConstantMonomial(self):
        test_data = [
            (1, [(2, "1/2")], 1, [(2, "3/2")], "4"),
            (2, [(2, "1/2")], 3, [(3, "3/2")], "18 * 2^(1/2) * 3^(1/2)"),
            (2, [(3, "1/2")], 3, [(2, "3/2")], "12 * 2^(1/2) * 3^(1/2)"),
        ]

        for coeff1, factors1, coeff2, factors2, res in test_data:
            factors1 = [(n, Fraction(e)) for n, e in factors1]
            factors2 = [(n, Fraction(e)) for n, e in factors2]
            mono1 = ConstantMonomial(coeff1, factors1)
            mono2 = ConstantMonomial(coeff2, factors2)
            self.assertEqual(str(mono1 * mono2), res)


if __name__ == "__main__":
    unittest.main()
