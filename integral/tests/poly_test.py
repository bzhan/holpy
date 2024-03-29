"""Unit test for polynomial module."""

import unittest

from integral import expr
from integral.expr import Var, Const, pi, E
from integral.poly import reduce_power, extract_frac, ConstantMonomial, Monomial, normalize_constant
from fractions import Fraction
from integral.parser import parse_expr


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
            (Monomial(1, [("x", Fraction(1, 2))]), "x^1/2"),
            (Monomial(1, [("x", Fraction(1, 2)), ("x", Fraction(1, 2))]), "x")
        ]

        for m, s in test_data:
            self.assertEqual(str(m), s)

    def testReducePower(self):
        test_data = [
            (2, 2, ((2, 2),)),
            (-2, 2, ((2, 2),)),
            (-1, 3, ((-1, 1),)),
            (-2, 3, ((-1, 1), (2, 3))),
            (-2, Fraction(3, 5), ((-1, 1), (2, Fraction(3, 5)))),
            (-2, Fraction(2, 5), ((2, Fraction(2, 5)),)),
        ]

        for n, e, res in test_data:
            self.assertEqual(reduce_power(n, e), res)

    def testExtractFrac(self):
        test_data = [
            (((2, Fraction(3, 2)),), (((2, Fraction(1, 2)),), 2)),
            (((2, Fraction(-1, 2)),), (((2, Fraction(1, 2)),), Fraction(1, 2))),
        ]

        for ps, res in test_data:
            self.assertEqual(extract_frac(ps), res)

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

    def testNormalizeConstant(self):
        test_data = [
            ("1/2 * pi", "pi / 2"),
            ("-1/2 * pi", "-(pi / 2)"),
            ("exp(2)", "exp(2)"),
            ("-1/2", "-1/2"),
        ]

        for e, res in test_data:
            e = parse_expr(e)
            self.assertEqual(str(normalize_constant(e)), res)


if __name__ == "__main__":
    unittest.main()
