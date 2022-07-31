"""Unit test for expressions."""

import unittest
from decimal import Decimal
from fractions import Fraction
import copy

import integral
from logic import basic
from logic import context
from integral import expr, proof
from integral.expr import Var, Const, Op, Fun, sin, cos, log, exp, Deriv, Integral, EvalAt, Symbol, \
    VAR, CONST, OP, FUN, match, pi, Const, expr_to_holpy
from integral.parser import parse_expr

basic.load_theory('transcendentals')


class ExprTest(unittest.TestCase):
    def testPrintExpr(self):
        x, y, z = Var("x"), Var("y"), Var("z")
        test_data = [
            (x, "x"),
            (Const(1), "1"),
            (Const(Decimal("1.1")), "11/10"),
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
            (x - (x - y), "x - (x - y)"),
            (x - (x + y), "x - (x + y)"),
            (x / (x / y), "x / (x / y)"),
            (x / (x * y), "x / (x * y)"), 
            (sin(x), "sin(x)"),
            (cos(x), "cos(x)"),
            (log(x), "log(x)"),
            (exp(x), "exp(x)"),
            (-x * exp(x), "-x * exp(x)"),
            (-(x * exp(x)), "-(x * exp(x))"),
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

    def testNormalizeConstant(self):
        test_data = [
            ("(3 + sqrt(2)) * (2 + sqrt(2))", "8 + 5 * sqrt(2)"),
            ("(3 + sqrt(2)) * (2 + sqrt(3))", "6 + 2 * sqrt(2) + sqrt(2) * sqrt(3) + 3 * sqrt(3)"),
            ("sqrt(8)", "2 * sqrt(2)"),
            ("sqrt(8) + 3 * sqrt(2)", "5 * sqrt(2)"),
            ("sqrt(18)", "3 * sqrt(2)"),
            ("sqrt(18) + 2 * sqrt(2)", "5 * sqrt(2)"),
            ("2 ^ (1/2) * 2 ^ (1/3)", "2 ^ (5/6)"),
            ("(-9)^(1/3)", "-(3 ^ (2/3))"),
            ("(-8)^(2/3)", "4"),
            ("0 ^ 5", "0"),
            ("sqrt(8) / sqrt(10)", "2/5 * sqrt(5)"),
            ("sqrt(8) / (1 + sqrt(10))", "2 * sqrt(2) * (1 + sqrt(2) * sqrt(5)) ^ -1"),
            ("sqrt(8) ^ 2", "8"),
            ("(3 + sqrt(2)) ^ 2", "11 + 6 * sqrt(2)"),
            ("(3 + sqrt(2)) ^ 3", "45 + 29 * sqrt(2)"),
            ("(3 + sqrt(2)) ^ -1", "(3 + sqrt(2)) ^ -1"),
            ("pi / 2 - pi / 3", "1/6 * pi"),
            ("exp(0)", "1"),
            ("exp(2) * exp(3)", "exp(5)"),
            ("exp(pi) * exp(3)", "exp(3) * exp(pi)"),
            ("log(1)", "0"),
            ("log(2)", "log(2)"),
            ("log(exp(2))", "2"),
            ("log(6)", "log(2) + log(3)"),
            ("log(8)", "3 * log(2)"),
            ("log(1/2)", "-log(2)"),
            ("log(9/10)", "-log(2) + 2 * log(3) + -log(5)"),
            ("sin(pi/4)", "1/2 * sqrt(2)"),
            ("sin(pi/4) * sqrt(2)", "1"),
            ("sin(5*pi/4)", "-1/2 * sqrt(2)"),
            ("sin(9*pi/4)", "1/2 * sqrt(2)"),
            ("sin(-5*pi/4)", "1/2 * sqrt(2)"),
            ("cos(5*pi/3)", "1/2"),
            ("cos(4*pi/3)", "-1/2"),
            ("atan(1)", "1/4 * pi"),
            ("abs(-2)", "2"),
            ("sqrt(1 - 1)", "0"),
            ("sqrt(2 + 1/4)", "3/2"),
            ("sin(2 * pi)", "0"),
            ("cos(2 * pi)", "1"),
            ("sin((2 + 3/4) * pi)", "1/2 * sqrt(2)"),
            ("(39 * (pi / 100)) / 2", "39/200 * pi"),
            ("cos((39 * (pi / 100)) / 2)", "cos(39/200 * pi)")
        ]

        context.set_context('interval_arith')
        for s, res in test_data:
            t = parse_expr(s)
            self.assertEqual(str(t.normalize_constant()), res)

    def testNormalizeConstantTrig(self):
        context.set_context('interval_arith')
        table = expr.trig_table()
        for func_name in ('sin', 'cos', 'tan', 'cot', 'csc', 'sec'):
            for k, v in table[func_name].items():
                self.assertEqual(Fun(func_name, k).normalize_constant(), v)

        inv_table = expr.inverse_trig_table()
        for func_name in ('asin', 'acos', 'atan', 'acot', 'acsc', 'asec'):
            for k, v in inv_table[func_name].items():
                self.assertEqual(Fun(func_name, k).normalize_constant(), v)

    def testNormalize(self):
        test_data = [
            ("2 + 3", "5"),
            ("x + 0", "x"),
            ("2 * 3", "6"),
            ("1 + 1/3", "4/3"),
            ("2 + 3 * x + 4", "6 + 3 * x"),
            ("0 / (x + y)", "0"),
            ("2 + x / y + 2 * (x / y) + 3", "5 + 3 * x * y ^ -1"),
            ("(x + y) ^ 2", "(x + y) ^ 2"),
            ("x^(1.5)","x ^ (3/2)"),
            ("(x + y) * (x - y)", "x ^ 2 + -(y ^ 2)"),
            ("[x]_x=a,b", "-a + b"),
            ("[x ^ 2 * y]_x=a,b", "-(a ^ 2 * y) + b ^ 2 * y"),
            ("[x ^ 2]_x=3,4", "7"),
            ("cos(x ^ 2)", "cos(x ^ 2)"),
            ("cos(pi/4)", "1/2 * sqrt(2)"),
            ("-(-x)", "x"),
            ("cos(0) - cos(pi/4)", "1 + -1/2 * sqrt(2)"),
            ("cos(0) - cos(pi/2)", "1"),
            ("([x]_x=a,b) + 2 * ([x ^ 2 / 2]_x=a,b) + [x ^ 3 / 3]_x=a,b",
             "-a + -(a ^ 2) + -1/3 * a ^ 3 + b + b ^ 2 + 1/3 * b ^ 3"),
            ("x ^ (1/2) * x ^ (1/2) ", "x"),
            ("2 * (1 + 3)", "8"),
            ("atan(1)", "1/4 * pi"),
            ("atan(sqrt(3)/3)", "1/6 * pi"),
            ("atan(sqrt(3))", "1/3 * pi"),
            ("sin(3/4 * pi)", "1/2 * sqrt(2)"),
            ("pi + pi / 3", "4/3 * pi"),
            ("1 - cos(x) ^ 2", "1 + -(cos(x) ^ 2)"),
            ("x^2 * 6", "6 * x ^ 2"),
            ("(x * y)^2", "x ^ 2 * y ^ 2"),
            ("(2*sin(x))^2", "4 * sin(x) ^ 2"),
            ("(2^(1/2)*sin(x))^(2)", "2 * sin(x) ^ 2"),
            ("2 * 8 ^ (1/2) * 1 * cos(t) ^ 2", "4 * sqrt(2) * cos(t) ^ 2"),
            ("8 ^ (1/2) * cos(t) ^ 2 * 1", "2 * sqrt(2) * cos(t) ^ 2"),
            ("1/3 * 3 ^ 3", "9"),
            ("(-1) * (1/3 * 2 ^ 3)", "-8/3"),
            ("5 + (1/3 * 3 ^ 3 + (-1) * (1/3 * 2 ^ 3))", "34/3"),
            ("2 * 8 ^ (1/2) * (1/2)", "2 * sqrt(2)"),
            ("x / sqrt(5 - 4 * x)", "x * (5 + -4 * x) ^ (-1/2)"),
            ("1/(1+sqrt(x))", "(1 + sqrt(x)) ^ -1"),
            ("log(2) - log(3)", "log(2) + -log(3)"),
            ("(3 * x + 1) ^ -2", "(1 + 3 * x) ^ -2"),
            ("-u/2","-1/2 * u"),
            ("exp(-u/2)", "exp(-1/2 * u)"),
            ("log(exp(2))", "2"),
            ("log(x^2)", "2 * log(x)"),
            ("sqrt(cos(x) - cos(x)^3)", "sqrt(cos(x) + -(cos(x) ^ 3))"),
            ("sqrt(cos(x) * (1 - cos(x)^2))", "sqrt(cos(x) + -(cos(x) ^ 3))"),
            ("1/2 * u ^ ((-1)) * 2 * u", "1"),
            ("1/2 * u ^ ((-1)) * (2 * u / (1 + u ^ (2)))", "(1 + u ^ 2) ^ -1"),
            ("[log(1 + u ^ 2)]_u=-1,1", "0"),
            # ("sqrt(x ^ 2)", "abs(x)"),
            ("[abs(x)]_x=-2,3", "1"),
            # ("abs(sqrt(3) / 2) / 2", "1/4 * 3 ^ (1/2)"),
            # ("abs(sqrt(3) / 2) / abs(sqrt(2) / 2)", "6 ^ (1/2) / 2"),
            # ("([log(abs(u))]_u=1/2 * 2 ^ (1/2),1/2 * 3 ^ (1/2))", "-log(2 ^ (1/2) * (1/2)) + log(3 ^ (1/2) * (1/2))"),
            ("exp(1)", "exp(1)"),
            ("[exp(u) * sin(u)]_u=0,1", "exp(1) * sin(1)"),
            ("exp(1) ^ 2", "exp(2)"),
            ("cos(acos(u)) ^ 2 ", "u ^ 2"),
            ("log(exp(t)) ^ (-2)", "t ^ -2"),
            ("log(6^(1/2))", "1/2 * log(2) + 1/2 * log(3)"),
            ("log(6*pi)", "log(2) + log(3) + log(pi)"),
            ("exp(-t) * exp(t)", "1"),
            ("(u ^ (-2) * exp(u)) * exp(-u)", "u ^ -2"),
            ("[u ^ 8 / 8]_u=-3,3", "0"),
            # ("(1 - exp(-x)) / (1 - exp(-x))", "1"),
            # ("sin(sqrt(x ^ 2))", "sin(abs(x))"),
            # ("sqrt((u/pi)^2)", "abs(u / pi)"),
            # ("sin(sqrt((u/pi)^2))", "sin(abs(u / pi))"),
            ("u*pi^(-1) * (u/pi)^(-1)", "1"),
            ("(2 * u) * pi ^ (-1) *(1/pi)^(-1)", "2 * u"),
            ("((2 * u) * pi ^ (-1)) * (u / pi) ^ (-1)", "2"),
            ("2 * (INT x:[1,exp(1)]. 1) - ([u * log(u)]_u=2,2 * exp(1))",
             "-2 * exp(1) + -2 * exp(1) * log(2) + 2 * log(2) + 2 * (INT x:[1,exp(1)]. 1)"),
            ("3 ^ (1/2) * 3 ^ (1/2)", "3"),
            ("2 * ((1/2) * 3 ^ (1/2))", "sqrt(3)"),
            ("exp(5 * x) * 3 / exp(3 * x)",  "3 * exp(2 * x)"),
            ("exp(5 * x) * exp(2 * x) / 7", "1/7 * exp(7 * x)"),
            ("(exp(4 * x) - 1) * exp(4 * x)  ", "-exp(4 * x) + exp(8 * x)"),
            ("(-u + 1) ^ 3 * (1 - u) ^ 2 ^ (-1)", "1 + -u"),
            ("2 * (-((1/2) * -(3 ^ (1/2))) + 1)", "2 + sqrt(3)"),
            ("1/2 * (-2 * (INT t:[0,(-1)/2]. exp(t)))", "-(INT t:[0,-1/2]. exp(t))"),
            ("(cos(x)^4 * sin(x) ^ 2) /  -(sin(x))", "-(cos(x) ^ 4 * sin(x))"),
            ("2 ^ (1/2) ^ 6 / 6", "4/3"),
            # ("sin(x) ^ 2 * csc(x) ^ 3", "csc(x)"),
            # ("sin(x) ^ 3 * csc(x) ^ 2", "sin(x)"),
            ("1 / (2 - sqrt(3))", "(2 + -sqrt(3)) ^ -1"),
            ("x ^ (1/2) * x ^ (1/3)", "x ^ (5/6)"),
            ("sqrt(x ^ 2)", "abs(x)"),
            ("sqrt(2 * x ^ 2)", "sqrt(2) * abs(x)"),
            ("sqrt(2 * cos(x) ^ 2)", "sqrt(2) * abs(cos(x))"),
            ("(2 * x^2) ^ (3/2)", "2 * sqrt(2) * abs(x) ^ 3"),
            ("-(11/21) + 2/3 * 0 ^ 6 + 1/7 * 0 ^ 7", "-11/21"),
            ("abs (2 + exp(2))", "2 + exp(2)"),
            ("abs (2 - exp(2))", "-2 + exp(2)"),
            ("exp (log(2))", "2"),
        ]

        context.set_context('interval_arith')
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
            ("INT u:[0,pi / 2]. sqrt(1 - sin(u) ^ 2) * cos(u)","0.1.0", "u")
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
            ("1/2 * x ^ ((-1)/2)", "x ^ (1/2)", "u", "1/2 * u ^ -1")
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
            ("1 / x", "-1 / x ^ 2"),
            ("3 * x + 1", "3"),
            ("x + pi / 3", "1"),
            ("2 * x + pi / 3", "2"),
            ("sin(x)", "cos(x)"),
            ("sin(x^2)", "2 * x * cos(x ^ 2)"),
            ("cos(x)", "-sin(x)"),
            ("log(x)", "x ^ -1"),
            ("x * log(x)", "1 + log(x)"),
            ("exp(x)", "exp(x)"),
            ("exp(x^2)", "2 * x * exp(x ^ 2)"),
            ("tan(2*x)", "2 * sec(2 * x) ^ 2"),
        ]

        for s, s2 in test_data:
            s = parse_expr(s)
            self.assertEqual(str(expr.deriv("x", s)), s2)

    def testSeparateIntegral(self):
        test_data = [
            ("((-1))*(INT x:[a, b].x+1) + (INT x:[a, b].1) + 3",
            {"INT x:[a,b]. x + 1", "INT x:[a,b]. 1"})
        ]

        for s, s2 in test_data:
            t = parse_expr(s).separate_integral()
            for i in range(len(t)):
                t[i] = str(t[i][0])
            self.assertEqual(set(t), s2)

    def testConstant(self):
        test_data = [
            ("1", True),
            ("x", False),
            ("sin(pi/5)", True),
            ("sqrt(2)", True),
            ("2^(1/2)", True),
            ("1 + sqrt(3)/2", True),
            ("2 - 2^(1/2) / 3", True),
            ("x ^ (1/2)", False),
            ("sin(x)", False),
            ("2 * 8 ^ (1/2) * (1/2)", True)
        ]

        for s, s2 in test_data:
            s = parse_expr(s)
            self.assertEqual(s.is_constant(), s2)

    def testGetAbs(self):
        test_data = [
            ("2 * u / (1 + abs(u))", ["abs(u)"]),
            ("t * (4 + abs(t)) ^ -1 * abs(t ^ -1)", ["abs(t)", "abs(t ^ -1)"])
        ]

        for s, s1 in test_data:
            s = parse_expr(s)
            for i in range(len(s1)):
                s1[i] = parse_expr(s1[i])
            self.assertEqual(s.get_abs(), s1)

    def testPriority(self):
        x = parse_expr("x")
        test_data = [
            ("1+(x^2)", "1 + x ^ 2"),
            ("1+(-2)","1 + -2"),
            ('-(x+3)','-(x + 3)'),
            ('------------x', '------------x'),
            ('x+-5', 'x + -5'),

        ]

        for s, s2 in test_data:
            e = expr.parser.parse_expr(s)
            self.assertEqual(str(e), s2)

    def testReplaceExpr(self):
        test_data = [
            ("x + y", "1", "x + y", "x + (x + y)"),
            ("x + y + z", "0.1", "sin(x)", "x + sin(x) + z"),
            ("x + 2", "", "x + 1 + 1", "x + 1 + 1"),
            ("sin(x) ^ 2 * sin(x) + sin(x) ^ 2", "0.0", "1 - cos(x) ^ 2", "(1 - cos(x) ^ 2) * sin(x) + sin(x) ^ 2"),
            ("INT u:[0,pi / 2]. sqrt(1 - sin(u) ^ 2) * cos(u)", "0.0.0", "cos(u) ^ 2", "INT u:[0,pi / 2]. sqrt(cos(u) ^ 2) * cos(u)")
        ]

        for s, s1, s2, s3 in test_data:
            s = parse_expr(s)
            s2 = parse_expr(s2)
            s3 = parse_expr(s3)
            self.assertEqual(s.replace_expr(s1, s2), s3)

    def testGetLocation(self):
        test_data = [
            ("$x$ + y", "0"),
            ("$x + y$", ''),
            ("$sin(x)^2$*sin(x)", "0"),
            ("INT x:[0, 1]. $sin(x)$ + x - 1", "0.0.0")
        ]

        for s, s1 in test_data:
            s = parse_expr(s)
            self.assertEqual(s.get_location(), s1)

    def testMatching(self):
        a = Symbol('a', [CONST])
        b = Symbol('b', [CONST])
        x = Symbol('x', [VAR])
        y = Symbol('y', [VAR, OP, FUN])

        test_data = [
            ('x - 1', x - a, {x: Var('x'), a: Const(1)}),
            ('x - 2', x - Const(2), {x: Var('x')}),
            ('x + 3', x - b, None),
            ('x', x + a, None),
            ('3*x', a * x, {a: Const(3), x: Var('x')}),
            ('3 * x + 5', a * x + b, {a: Const(3), x: Var('x'), b: Const(5)}),
            ('2 * x + 3', a * x + a, None),
            ('x ^ 2', x ^ Const(2), {x: Var('x')}),
            ('x ^ 3 - 2', x ^ Const(3), None),
            ('1 - x ^ 2', a - (x ^ Const(2)), {a: Const(1), x: Var('x')}),
            ('cos(x) ^ 2', cos(x) ^ Const(2), {x: Var('x')}),
            ('(1 - x ^ 2) ^ (1/2)', (Const(1) - (x ^ Const(2)))^(Const(Fraction(1/2))), {x: Var('x')}),
            ('(1 - x ^ 3) ^ (1/2)', (Const(1) - (x ^ Const(2)))^(Const(Fraction(1/2))), None),
            ('(1 - 2 * sin(x) ^ 2) ^ (1/2)', (b - a * (sin(x) ^ Const(2)))^Const(Fraction(1/2)), {b: Const(1), a: Const(2), x: Var('x')}),
            ('sin(x) ^ 2 + cos(y)^2', (sin(x)^Const(2))+(cos(x)^Const(2)), None),
            ('sin(2*x+1)^2 + cos(2*x+1) ^ 2', (sin(y)^Const(2))+(cos(y)^Const(2)), {y: Op("+",Op("*",Const(2),Var('x')),Const(1))}),
            ('2*pi', a * pi, {a: Const(2)}),
        ]

        for r1, r2, r3 in test_data:
            self.assertEqual(match(parse_expr(r1), r2), r3)

    def testExpandPower(self):
        test_data = [
            ("(x+y)^2", "2*x*y + x^2 + y^2"),
            ("(x-1)^2", "(1 - 2*x) + x^2"),
            ("1 + (exp(x) + 2*x)^2", "1 + (4 * x * exp(x) + 4 * x ^ 2 + exp(2 * x))"),
            ("2 * u + (u - 1) ^ 2 + 3", "4 + u^2"),
        ]

        for v, v_res in test_data:
            v = parse_expr(v)
            v_res = parse_expr(v_res)
            self.assertEqual(v.expand().normalize(), v_res.normalize())

    def testNormalize1(self):
        test_data = [
            ('x', 'x'),
            ("2 + 3", "5"),
            ("x + 0", "x"),
            ("2 * 3", "6"),
            ("1 + 1/3", "4/3"),
            ("2 + 3 * x + 4", "6 + 3 * x"),
            (" 0 / (x + y)", "0"),
            ("2 + x / y + 2 * (x / y) + 3", "5 + 3 * x * y ^ -1"),
            ("x+y","x + y"),
            ("(x + y) ^ 2", "(x + y) ^ 2"),
            ("x^(1.5)","x ^ (3/2)"),
            ("(x + y) * (x - y)", "x ^ 2 + -(y ^ 2)"),
            ("[x]_x=a,b", "-a + b"),
            ("[x ^ 2 * y]_x=a,b", "-(a ^ 2 * y) + b ^ 2 * y"),
            ("[x ^ 2]_x=3,4", "7"),
            ("-(-x)", "x"),
            ("(x*y)^2", "x ^ 2 * y ^ 2"),
            ("(x/y)^2", "x ^ 2 * y ^ -2"),
            ("exp(2*x)^2", "exp(4 * x)"),
            ("exp(3*x)*exp((1/2)*x)", "exp(7/2 * x)"),
            ("exp(2*x)^(-1)", "exp(-2 * x)"),
            ("pi/2-pi/3", "1/6 * pi"),
            ("(3/4)^(-1)", "4/3"),
            ("3 ^ (1/2) * 2 ^ -1","1/2 * sqrt(3)"),
            ("sin(pi/4)", "1/2 * sqrt(2)"),
            ("sin(4/pi)", "sin(4 * pi ^ -1)"),
            ("pi*pi", "pi ^ 2"),
            ("(1/4) * pi * (1/2)", "1/8 * pi"),
            ("pi/2 - pi/3", "1/6 * pi"),
            ("(-1)*(3^(-1))", "-1/3"),
            # ("1 / (2 * (u ^ 2 + 1))", "1/2 * (1 + u ^ 2) ^ -1"), 
            # ("(1 + x) * 1/(2*(1 + x))", "1/2"),
            # ("1/(1+x) * (1+x)", "1"),
            # ("(1+x) * (1+x)^(-1)", "1"),
            # ("(2+x)*(x+3)/(3+x)^2", "(2 + x) * (3 + x) ^ -1"),
            # ("(2+x)*(x+3)^3/(3+x)^2", "(2 + x) * (3 + x)")
            ("2 * exp(2) + -1 * exp(2)", "exp(2)"),
            ("2 * exp(2) + exp(-1) + -1 * ([exp(x)]_x=-1,2)", "2 * exp(-1) + exp(2)")
        ]

        for v, v_res in test_data:
            v = parse_expr(v)
            self.assertEqual(str(v.normalize()), v_res)


if __name__ == "__main__":
    unittest.main()

