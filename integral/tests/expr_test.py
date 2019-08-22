"""Unit test for expressions."""

import unittest
from decimal import Decimal

from integral import expr
from integral.expr import Var, Const, Op, Fun, sin, cos, log, Deriv, Integral
from integral.parser import parse_expr

class ExprTest(unittest.TestCase):
    def testPrintExpr(self):
        test_data = [
            (Var("x"), "x"),
            (Const(1), "1"),
            (Const(Decimal("1.1")), "1.1"),
            (Const(-1), "-1"),
            (Var("x") + Var("y"), "x + y"),
            (Var("x") - Var("y"), "x - y"),
            (-Var("x"), "-x"),
            (Var("x") * Var("y"), "x * y"),
            (Var("x") / Var("y"), "x / y"),
            (Var("x") ^ Var("y"), "x ^ y"),
            (sin(Var("x")), "sin(x)"),
            (cos(Var("x")), "cos(x)"),
            (log(Var("x")), "log(x)"),
            (Deriv("x", Const(3) * Var("x")), "D x. 3 * x"),
            (Integral("x", Const(1), Const(2), Const(3) * Var("x")), "INT x:[1,2]. 3 * x"),
        ]

        for e, s in test_data:
            self.assertEqual(str(e), s)

    def testCompareExpr(self):
        test_data = [
            (Var("x"), Var("y")),
            (Var("x"), Const(3)),
            (Const(3), Const(4)),
            (Const(4), Var("x") * Var("y")),
            (Var("x") * Var("y"), Var("x") + Var("y")),
            (Var("x") * Var("y"), Var("x") * Var("z")),
            (Var("x") * Var("y"), Var("z") * Var("y")),
            (sin(Var("x")), Var("x") * Var("y")),
            (Var("x") * Var("y"), sin(sin(Var("x")))),
            (sin(Var("x")), Deriv("x", Var("x"))),
            (Deriv("x", Var("x")), Integral("x", Const(1), Const(2), Var("x"))),
        ]

        for s, t in test_data:
            self.assertTrue(s <= t)
            self.assertTrue(s < t)
            self.assertFalse(t <= s)
            self.assertFalse(t < s)

    def testReduce(self):
        test_data = [
            ("2 + 3", "5"),
            ("2 * 3", "6"),
            ("2 + (3*x) + 4", "6 + 3 * x")
        ]

        for s, res in test_data:
            t = parse_expr(s)
            self.assertEqual(str(t.normalize()), res)


if __name__ == "__main__":
    unittest.main()
