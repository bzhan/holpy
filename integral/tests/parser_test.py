"""Unit test for parsing."""

import unittest
from fractions import Fraction
from decimal import Decimal

from integral.expr import Var, Const, Op, Fun, trig_identity
from integral.parser import parse_expr


class ParserTest(unittest.TestCase):
    def testParseTerm(self):
        test_data = [
            "x", "1", "11/10", "-1", "-11/10",
            "x + y", "x - y", "-x", "x * y", "x / y", "x ^ y",
            "x + y * z", "(x + y) * z",
            "x * y + z", "x * (y + z)",
            "x * y ^ 2", "(x * y) ^ 2",
            "sin(x)", "cos(x)", "log(x)", "exp(x)",
            "D x. 3 * x",
            "INT x:[1,2]. 3 * x",
            "[3 * x]_x=1,2",
            "INT x:[0,pi / 4]. sin(x)",
            "x ^ (1/2)"
        ]

        for s in test_data:
            e = parse_expr(s)
            self.assertEqual(str(e), s)

    def testParseTerm2(self):
        test_data = [
            ("-x", -Var("x")),
            ("-2", Const(-2)),
            ("1/2", Const(Fraction(1) / 2)),
            ("-1/2", Const(Fraction(-1) / 2)),
            ("0.5", Const(Decimal("0.5"))),
            ("pi", Fun("pi")),
            ("-x^2", Op("-", Op("^", Var("x"), Const(2))))
        ]

        for s, e, in test_data:
            self.assertEqual(parse_expr(s), e)

    def testParseTerm3(self):
        test_data = [
            ("$sin(x)^2$*sin(x)", Op("*", Op("^",Fun("sin",Var("x")),Const(2)), Fun("sin",Var("x")))),
            ("x + $x + y$", Op("+", Var("x"), Op("+", Var("x"), Var("y")))),
        ]
        
        for s, e in test_data:
            self.assertEqual(parse_expr(s), e)
            self.assertTrue(Op("^",Fun("sin",Var("x")),Const(2)) in trig_identity)


if __name__ == "__main__":
    unittest.main()
