import unittest

from integral.solve import solve_equation, solve_for_term
from integral.parser import parse_expr


class SolveTest(unittest.TestCase):
    def testSolveSimple(self):
        test_data = [
            ("x", "a", "a"),
            ("x + a", "b", "b - a"),
            ("a + x", "b", "b - a"),
            ("-x", "a", "-a"),
            ("a - x", "b", "a - b"),
            ("x - a", "b", "a + b"),
            ("x * a", "b", "b / a"),
            ("a * x", "b", "b / a"),
            ("a / x", "b", "a / b"),
            ("x / a", "b", "a * b"),
        ]

        for f, a, res in test_data:
            f = parse_expr(f)
            a = parse_expr(a)
            self.assertEqual(str(solve_equation(f, a, 'x')), res)

    def testSolveFunctions(self):
        test_data = [
            ("log(x)", "a", "exp(a)"),
            ("exp(x)", "a", "log(a)"),
            ("exp(x + a)", "b", "log(b) - a"),
        ]

        for f, a, res in test_data:
            f = parse_expr(f)
            a = parse_expr(a)
            self.assertEqual(str(solve_equation(f, a, 'x')), res)

    def testSolveLinear(self):
        test_data = [
            ("x + x", "a", "1/2 * a"),
            ("x - x", "a", None),
            ("x - 2 * x", "a", "-a"),
            ("x + b - 2 * x", "a", "-(a - b)"),
            ("x + b + 2 * x", "a", "1/3 * (a - b)"),
        ]
        
        for f, a, res in test_data:
            f = parse_expr(f)
            a = parse_expr(a)
            if res is None:
                self.assertIsNone(solve_equation(f, a, "x"))
            else:
                self.assertEqual(str(solve_equation(f, a, 'x')), res)

    def testSolveForTerm(self):
        test_data = [
            ("I(a) + a = b", "I(a)", "b - a"),
            ("I(a) + a = b - I(a)", "I(a)", "1/2 * (-a + b)"),
            ("log(I(a)) = b", "I(a)", "exp(b)"),
        ]

        for eq, t, res in test_data:
            eq = parse_expr(eq)
            t = parse_expr(t)
            if res is None:
                self.assertIsNone(solve_for_term(eq, t))
            else:
                self.assertEqual(str(solve_for_term(eq, t)), res)


if __name__ == "__main__":
    unittest.main()
