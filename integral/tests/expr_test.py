"""Unit test for expressions."""

import unittest
from decimal import Decimal

from integral import expr
from integral.expr import Var, Const, Op, Fun, sin, cos, log, Deriv, Integral, EvalAt
from integral.parser import parse_expr

class ExprTest(unittest.TestCase):
    def testPrintExpr(self):
        x, y, z = Var("x"), Var("y"), Var("z")
        test_data = [
            (x, "x"),
            (Const(1), "1"),
            (Const(Decimal("1.1")), "1.1"),
            (Const(-1), "-1"),
            (x + y, "x + y"),
            (x - y, "x - y"),
            (-x, "-x"),
            (x * y, "x * y"),
            (x / y, "x / y"),
            (x ^ y, "x ^ y"),
            ((x + y) * z, "(x + y) * z"),
            (x + (y * z), "x + y * z"),
            (x * y + z, "x * y + z"),
            (x * (y + z), "x * (y + z)"),
            (x + y + z, "x + y + z"),
            (x + (y + z), "x + (y + z)"),
            (x * (y ^ Const(2)), "x * y ^ 2"),
            ((x * y) ^ Const(2), "(x * y) ^ 2"),
            (-(x + y), "-(x + y)"),
            (-x + y, "-x + y"),
            (sin(x), "sin(x)"),
            (cos(x), "cos(x)"),
            (log(x), "log(x)"),
            (sin(x ^ Const(2)), "sin(x ^ 2)"),
            (sin(x) * cos(x), "sin(x) * cos(x)"),
            (Deriv("x", Const(3) * x), "D x. 3 * x"),
            (Integral("x", Const(1), Const(2), Const(3) * x), "INT x:[1,2]. 3 * x"),
            (Deriv("x", Const(3) * x) * x, "(D x. 3 * x) * x"),
            (Integral("x", Const(1), Const(2), Const(3) * x) * x, "(INT x:[1,2]. 3 * x) * x"),
            (EvalAt("x", Const(1), Const(2), Const(3) * x), "[3 * x]_x=1,2"),
            (EvalAt("x", Const(1), Const(2), Const(3) * x) * x, "([3 * x]_x=1,2) * x"),
        ]

        for e, s in test_data:
            self.assertEqual(str(e), s)

    def testCompareExpr(self):
        x, y, z = Var("x"), Var("y"), Var("z")
        test_data = [
            (x, y),
            (x, Const(3)),
            (Const(3), Const(4)),
            (Const(4), x * y),
            (x * y, x + y),
            (x * y, x * z),
            (x * y, z * y),
            (sin(x), x * y),
            (x * y, sin(sin(x))),
            (sin(x), Deriv("x", x)),
            (Deriv("x", x), Integral("x", Const(1), Const(2), x)),
        ]

        for s, t in test_data:
            self.assertTrue(s <= t)
            self.assertTrue(s < t)
            self.assertFalse(t <= s)
            self.assertFalse(t < s)

    def testNormalize(self):
        test_data = [
            ("2 + 3", "5"),
            ("2 * 3", "6"),
            ("2 + 3 * x + 4", "6 + 3 * x"),
            ("2 + x / y + 2 * (x / y) + 3", "5 + 3 * (x / y)"),
            ("(x + y) ^ 2", "(x + y) ^ 2"),
        ]

        for s, res in test_data:
            t = parse_expr(s)
            self.assertEqual(str(t.normalize()), res)


if __name__ == "__main__":
    unittest.main()
