"""Unit test for expressions."""

import unittest
from decimal import Decimal
from fractions import Fraction
import copy

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
            (Const((-1)), "-1"),
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
            (x ^ Const(Fraction("1/2")), "x ^ (1/2)"),
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
            ("x + 0", "x"),
            ("2 * 3", "6"),
            ("1 + 1/3", "4/3"),
            ("2 + 3 * x + 4", "6 + 3 * x"),
            (" 0 / (x + y)", "0"),
            ("2 + x / y + 2 * (x / y) + 3", "5 + 3 * x * y ^ -1"),
            ("(x + y) ^ 2", "(x + y) ^ 2"),
            ("x^(1.5)","x ^ (3/2)"),
            ("(x + y) * (x - y)", "x ^ 2 + -1 * y ^ 2"),
            ("[x]_x=a,b", "-1 * a + b"),
            ("[x ^ 2 * y]_x=a,b", "-1 * a ^ (2) * y + b ^ (2) * y"),
            ("[x ^ 2]_x=3,4", "7"),
            ("cos(x ^ 2)", "cos(x ^ 2)"),
            ("cos(pi/4)", "1/2 * 2 ^ (1/2)"),
            ("-(-x)", "x"),
            ("cos(0) - cos(pi/4)", "1 + -1 * (1/2 * 2 ^ (1/2))"),
            ("cos(0) - cos(pi/2)", "1"),
            ("([x]_x=a,b) + 2 * ([x ^ 2 / 2]_x=a,b) + [x ^ 3 / 3]_x=a,b",
             "-1 * a + -1 * a ^ (2) + -1/3 * a ^ (3) + b + b ^ (2) + 1/3 * b ^ (3)"),
            ("x ^ (1/2) * x ^ (1/2) ", "x"),
            ("2 * (1 + 3)", "8"),
            ("atan(1)", "1/4 * pi"),
            ("atan(sqrt(3)/3)", "1/6 * pi"),
            ("atan(sqrt(3))", "1/3 * pi"),
            ("sin(3/4 * pi)", "1/2 * 2 ^ (1/2)"),
            ("pi + pi / 3", "4/3 * pi"),
            ("1 - cos(x) ^ 2", "1 + -1 * cos(x) ^ 2"),
            ("x^2 * 6", "6 * x ^ (2)"),
            ("((-1)) * INT x:[0, 2].(1 - x)", "INT x:[0,2]. -1 + x"),
            ("(x * y)^2", "x ^ (2) * y ^ (2)"),
            ("(2*sin(x))^2", "4 * sin(x) ^ 2"),
            ("(2^(1/2)*sin(x))^(2)", "2 * sin(x) ^ 2"),
            ("2 * 8 ^ (1/2) * 1 * cos(t) ^ 2", "2 * 8 ^ (1/2) * cos(t) ^ 2"),
            ("8 ^ (1/2) * cos(t) ^ 2 * 1", "8 ^ (1/2) * cos(t) ^ 2"),
            ("1/3 * 3 ^ (3)", "9"),
            ("(-1) * (1/3 * 2 ^ (3))", "-8/3"),
            ("5 + (1/3 * 3 ^ (3) + (-1) * (1/3 * 2 ^ (3)))", "34/3"),
            ("2 * 8 ^ (1/2) * (1/2)", "2 * 2 ^ (1/2)"),
            ("x / sqrt(5 - 4 * x)", "x * (5 + -4 * x) ^ -1/2"),
            ("1/(1+sqrt(x))", "1 / (1 + x ^ (1/2))"),
            ("log(2) - log(3)", "log(2/3)"),
            ("log(2) + log(x)", "log(2 * x)"),
            ("(3 * x + 1) ^ -2", "(1 + 3 * x) ^ -2"),
            ("-u/2","-1/2 * u"),
            ("exp(-u/2)", "exp(-1/2 * u)"),
            ("log(exp(2))", "2"),
            ("log(x^2)", "2 * log(x)"),
            ("sqrt(cos(x) - cos(x)^3)", "(cos(x) + -1 * cos(x) ^ 3) ^ (1/2)"),
            ("sqrt(cos(x) * (1 - cos(x)^2))","(cos(x) + -1 * cos(x) ^ 3) ^ (1/2)"),
            ("1/2 * u ^ ((-1)) * 2 * u", "1"),
            ("1/2 * u ^ ((-1)) * (2 * u / (1 + u ^ (2)))", "1 / (1 + u ^ (2))"),
            # ("[log(1 + u ^ 2)]_u=(-1),1", "0"),
            ("sqrt(x ^ 2)", "abs(x)"),
            ("[abs(x)]_x=-2,3", "1"),
            ("([log(abs(u))]_u=1/2 * 2 ^ (1/2),1/2 * 3 ^ (1/2))", "log(1/2 * 6 ^ (1/2))"),
            ("exp(1)", "exp(1)"),
            ("[exp(u) * sin(u)]_u=0,1", "sin(1) * exp(1)"),
            ("exp(1) ^ 2", "exp(2)")
            # ("1/2 * (-2 * (INT t:[0,(-1)/2]. exp(t)))", "(INT t:[0,(-1)/2]. (-1) * exp(t)))")
        ]

        for s, res in test_data:
            t = parse_expr(s)
            self.assertEqual(str(t.normalize()), res)

    def testGetSubExpr(self):
        test_data = [
            ("x + y", "0", "x"),
            ("x + y", "1", "y"),
            ("x + y + z", "0.0", "x"),
            ("x + y + z", "0.1", "y"),
            ("x + sin(x)", "1", "sin(x)"),
            ("x + sin(x)", "1.0", "x"),
            ("[sin(x)]_x=2,3", "0", "sin(x)"),
            ("[sin(x)]_x=2,3", "1", "2"),
            ("[sin(x) * cos(x)]_x=2,3", "0.1", "cos(x)"),
            ("D x. 3 * x", "0", "3 * x"),
            ("D x. 3 * x", "0.1", "x"),
            ("INT x:[1,2]. 3 * x", "0", "3 * x"),
            ("INT x:[1,2]. 3 * x", "0.1", "x"),
        ]

        for s, loc, res in test_data:
            t = parse_expr(s)
            res = parse_expr(res)
            self.assertEqual(t.get_subexpr(loc), res)

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

    def testReplace1(self):
        test_data = [
            ("x ^ 4", "x ^ 2", "u", "u ^ 2"),
            ("1/2 * x ^ ((-1)/2)", "x ^ (1/2)", "u", "1/2 * u ^ (-1)")
        ]

        for s, e, repl_e, res in test_data:
            s = parse_expr(s)
            e = parse_expr(e)
            repl_e = parse_expr(repl_e)
            res = parse_expr(res)
            self.assertEqual(s.replace_trig(e, repl_e), res)

    def testDeriv(self):
        test_data = [
            ("1", "0"),
            ("x", "1"),
            ("2 * x", "2"),
            ("x ^ 2", "2 * x"),
            ("x * y", "y"),
            ("1 / x", "- 1 / x ^ 2"),
            ("3 * x + 1", "3"),
            ("x + pi / 3", "1"),
            ("2 * x + pi / 3", "2"),
            ("sin(x)", "cos(x)"),
            ("sin(x^2)", "2 * x * cos(x^2)"),
            ("cos(x)", "(-1) * sin(x)"),
            ("cos(x^2)", "-2 * x * sin(x^2)"),
            ("log(x)", "x ^ (-1)"),
            ("x * log(x)", "1 + log(x)"),
            ("exp(x)", "exp(x)"),
            ("exp(x^2)", "2 * x * exp(x^2)"),
        ]

        for s, s2 in test_data:
            s = parse_expr(s)
            s2 = parse_expr(s2)
            self.assertEqual(expr.deriv("x", s), s2)
    
    def testTrig(self):
        test_data = [
            ("$sin(x)^2$*sin(x)", {"sin(x) ^ 2 * sin(x)","(1 - cos(x) ^ 2) * sin(x)", \
                "(1/2 - cos(2 * x) / 2) * sin(x)"}),
        ]

        for t, s in test_data:
            t = parse_expr(t)
            n = t.identity_trig_expr(expr.trig_identity)
            c = []
            for i in range(len(n)):
                c.append(str(n[i][0]))
            self.assertEqual(set(c), s)

    def testSeparateIntegral(self):
        test_data = [
            ("((-1))*(INT x:[a, b].x+1) + (INT x:[a, b].1) + 3",
            {"INT x:[a,b]. x + 1", "INT x:[a,b]. 1"})
        ]

        for s, s2 in test_data:
            t = parse_expr(s).separate_integral()
            for i in range(len(t)):
                t[i] = str(t[i])
            self.assertEqual(set(t), s2)

    def testConstant(self):
        test_data = [
            ("1", True),
            ("x", False),
            ("sin(pi/5)",True),
            ("sqrt(2)",True),
            ("2^(1/2)",True),
            ("1 + sqrt(3)/2",True),
            ("2 - 2^(1/2) / 3", True),
            ("x ^ (1/2)", False),
            ("sin(x)", False),
            ("2 * 8 ^ (1/2) * (1/2)", True)
        ]

        for s, s2 in test_data:
            s = parse_expr(s)
            self.assertEqual(s.is_constant(), s2)
    
    def testExtract(self):
        test_data = [
            "x^2 + x",
            "2 + 2*log(2)"
        ]

    def testGetAbs(self):
        test_data = [
            ("x * abs(x)", ["x","x"]),
            ("sqrt(cos(x)) * abs(sin(x))", ["sin(x)", "cos(x)^(1/2)"]),
            ("abs(x) * abs(y)", ["x*y", "1"])
        ]

        for s, s2 in test_data:
            s = parse_expr(s)
            for i in range(len(s2)):
                s2[i] = parse_expr(s2[i])
            self.assertEqual(s.getAbs(), tuple(s2))

    def testPriority(self):
        x = parse_expr("x")
        test_data = [
            (Const(1) + (x ^ Const(2)), "1 + x^2"),
        ]

        for s, s2 in test_data:
            self.assertEqual(s, parse_expr(s2))

if __name__ == "__main__":
    unittest.main()
