"""Unit test for expressions."""

import unittest
from decimal import Decimal

from integral import expr
from integral.expr import Var, Const, Op, Fun, sin, cos, log, exp, Deriv, Integral, EvalAt
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
            (exp(x), "exp(x)"),
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
            ("(x + y) * (x - y)", "x ^ 2 + -1 * y ^ 2"),
            ("[x]_x=a,b", "-1 * a + b"),
            ("[x ^ 2 * y]_x=a,b", "-1 * y * a ^ 2 + y * b ^ 2"),
            ("[x ^ 2]_x=3,4", "7"),
            ("cos(pi/4)", "1/2 * sqrt(2)"),
            ("cos(0) - cos(pi/4)", "1 + -1/2 * sqrt(2)"),
            ("cos(0) - cos(pi/2)", "1"),
            ("([x]_x=a,b) + 2 * ([x ^ 2 / 2]_x=a,b) + [x ^ 3 / 3]_x=a,b",
             "-1 * a + b + -1 * a ^ 2 + -1/3 * a ^ 3 + b ^ 2 + 1/3 * b ^ 3"),
            ("x ^ (1/2) * x ^ (1/2) ","x"),
            ("2 * (1 + 3)","8")
        ]

        for s, res in test_data:
            t = parse_expr(s)
            self.assertEqual(str(t.normalize()), res)

    def testReplace(self):
        test_data = [
            ("1 / (x ^ 2 + 1)", "x ^ 2 + 1", "u", "1 / u"),
            ("(3 * x + 1) ^ -2", "3 * x + 1", "u", "u ^ -2"),
            ("(x + y) * (x + y + z)", "x + y", "u", "u * (u + z)"),
        ]

        for s, e, repl_e, res in test_data:
            s = parse_expr(s)
            e = parse_expr(e)
            repl_e = parse_expr(repl_e)
            res = parse_expr(res)
            self.assertEqual(s.replace(e, repl_e), res)

    def testDeriv(self):
        test_data = [
            ("1", "0"),
            ("x", "1"),
            ("2 * x", "2"),
            ("x ^ 2", "2 * x"),
            ("x * y", "y"),
            ("1 / x", "- 1 / x ^ 2"),
            ("3 * x + 1", "3"),
            ("sin(x)", "cos(x)"),
            ("sin(x^2)", "2 * x * cos(x^2)"),
            ("cos(x)", "-1 * sin(x)"),
            ("cos(x^2)", "-2 * x * sin(x^2)"),
            ("log(x)", "1 / x"),
            ("x * log(x)", "x * (1 / x) + log(x)"),
            ("exp(x)", "exp(x)"),
            ("exp(x^2)", "2 * x * exp(x^2)"),
        ]

        for s, s2 in test_data:
            s = parse_expr(s)
            s2 = parse_expr(s2)
            self.assertEqual(expr.deriv("x", s), s2)


if __name__ == "__main__":
    unittest.main()
