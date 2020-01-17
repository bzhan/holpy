"""Unit test for polynomial module."""

import unittest

from integral.expr import Var, Const
from integral.poly import Monomial, parse_mono, parse_poly
from decimal import Decimal
from fractions import Fraction

class PolynomialTest(unittest.TestCase):
    def testPrintMonomial(self):
        test_data = [
            (Monomial(Const(1), []), "1"),
            (Monomial(Const(2), []), "2"),
            (Monomial(Const(0), []), "0"),
            (Monomial(Const(2), [("x", 1)]), "2x"),
            (Monomial(Const(2), [("x", 2)]), "2x^2"),
            (Monomial(Const(2), [("x", 2), ("y", 2)]), "2x^2y^2"),
            (Monomial(Const(2), [("y", 2), ("x", 2)]), "2x^2y^2"),
            (Monomial(Const(2), [("x+y", 2)]), "2(x+y)^2"),
            (Monomial(Const(2), [("x", 1), ("x", 2)]), "2x^3"),
            (Monomial(Const(1), [("x", Fraction(1, 2))]), "x ^ 1/2"),
            (Monomial(Const(1), [("x", Fraction(1, 2)), ("x", Fraction(1, 2))]), "x")
        ]

        for m, s in test_data:
            self.assertEqual(str(m), s)

    def testParsePolynomial(self):
        test_data = [
            "1", "2", "0", "2x", "2x^2", "2xy", "2x^2y^2",
        ]

        for s in test_data:
            p = parse_poly(s)
            self.assertEqual(str(p), s)

    def testMultMonomial(self):
        test_data = [
            ("2", "3", "6"),
            ("2x", "3x^2", "6x^3"),
            ("2x", "3y^2", "6xy^2"),
        ]

        for m1, m2, m3 in test_data:
            m1 = parse_mono(m1)
            m2 = parse_mono(m2)
            m3 = parse_mono(m3)
            self.assertEqual(m1 * m2, m3)

    def testDivMonomial(self):
        """Only consider when there is only one variable.
        """

        test_data = [
            ("6", "3", "2"),
            ("9x^2", "3", "3x^2"),
            ("16x^8","2x^4","8x^4")
        ]

    def testAddPolynomial(self):
        test_data = [
            ("2", "3", "5"),
            ("2x", "2y", "2x + 2y"),
            ("2x", "3x", "5x"),
            ("2x + 2z", "3y", "2x + 3y + 2z"),
        ]

        for p1, p2, p3 in test_data:
            p1 = parse_poly(p1)
            p2 = parse_poly(p2)
            p3 = parse_poly(p3)
            self.assertEqual(p1 + p2, p3)

    def testSubPolynomial(self):
        test_data = [
            ("5", "2", "3"),
            ("x", "0", "x"),
        ]

        for p1, p2, p3 in test_data:
            p1 = parse_poly(p1)
            p2 = parse_poly(p2)
            p3 = parse_poly(p3)
            c = p1 - p2
            self.assertEqual(p1 - p2, p3)

    def testMultPolynomial(self):
        test_data = [
            ("2", "3", "6"),
            ("2x", "2y", "4xy"),
            ("2x + 2y", "2z", "4xz + 4yz"),
            ("x + y", "x + y", "x^2 + y^2 + 2xy"),
            ("x", "x", "x^2")
        ]

        for p1, p2, p3 in test_data:
            p1 = parse_poly(p1)
            p2 = parse_poly(p2)
            p3 = parse_poly(p3)
            self.assertEqual(p1 * p2, p3)


if __name__ == "__main__":
    unittest.main()
