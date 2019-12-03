"""Unit test for rules."""

import unittest
from fractions import Fraction

from integral.expr import Const
from integral.parser import parse_expr
from integral import rules


class RulesTest(unittest.TestCase):
    def testSimplify(self):
        test_data = [
            ("INT x:[a,b]. x^(1/2) * x^(1/2)",
             "INT x:[a,b]. x"),
            ("INT x:[4, 9]. x^(1/2)*(1+x^(1/2))",
            "INT x:[4, 9]. x + x^(1/2)"),
            ("INT x:[0, pi/2]. (cos(x)^4 * sin(x) ^ 2) /  -(sin(x))",
            "INT x:[0, pi/2]. -1 * cos(x) ^ 4 * sin(x)"),
            ("INT x:[a, b]. (x ^ 2 + 2 * x  - x ^ 3 + sin(x)*x) /  (x * y * sin(z))",
            "INT x:[a, b]. (sin(x) + -1 * x ^ 2 + x + 2) / (y * sin(z))")
        ]
        rule = rules.Simplify()
        for s1, s2 in test_data:
            s1 = parse_expr(s1)
            s2 = parse_expr(s2)
            self.assertEqual(rule.eval(s1), s2)

    def testLinearity(self):
        test_data = [
            ("INT x:[a,b]. 1 + 2 * x + x ^ 2",
             "(INT x:[a,b]. x ^ 2) + 2 * (INT x:[a,b]. x) + (INT x:[a,b]. 1)"),
        ]

        rule = rules.Linearity()
        for s, s2 in test_data:
            s = parse_expr(s)
            s2 = parse_expr(s2)
            self.assertEqual(rule.eval(s), s2)

    def testCommonIntegral(self):
        test_data = [
            ("INT x:[a,b]. 1", "[x]_x=a,b"),
            ("INT x:[a,b]. 2", "[2 * x]_x=a,b"),
            ("INT x:[a,b]. x", "[x ^ 2 / 2]_x=a,b"),
            ("INT x:[a,b]. x ^ 2", "[x ^ 3 / 3]_x=a,b"),
            ("INT x:[a,b]. x ^ 3", "[x ^ 4 / 4]_x=a,b"),
            ("INT x:[a,b]. (x + 2) ^ 3", "[(x + 2) ^ 4 / 4]_x=a,b"),
            ("INT x:[a,b]. 3 / x ^ 3", "[3 * -1 / (2 * x ^ 2)]_x=a,b"),
            ("INT x:[a,b]. x ^ -1", "[log(x)]_x=a,b"),
            ("INT x:[a,b]. (x + 1) ^ -1", "[log(x+1)]_x=a,b"),
            ("INT x:[a,b]. (x + 2) ^ (-2)", "[(x + 2) ^ -1 / -1]_x=a,b"),
            ("INT x:[a,b]. 1 / x", "[log(x)]_x=a,b"),
            ("INT x:[a,b]. 1 / x ^ 2", "[(-1) / x]_x=a,b"),
            ("INT x:[a,b]. sin(x)", "[-cos(x)]_x=a,b"),
            ("INT x:[a,b]. cos(x)", "[sin(x)]_x=a,b"),
            ("INT x:[a,b]. 1 / (x ^ 2 + 1)", "[arctan(x)]_x=a,b")
        ]

        rule = rules.CommonIntegral()
        for s, s2 in test_data:
            s = parse_expr(s)
            s2 = parse_expr(s2)
            self.assertEqual(rule.eval(s), s2)

    def testOnSubterm(self):
        test_data = [
            ("(INT x:[a,b]. 1) + 2 * (INT x:[a,b]. x) + (INT x:[a,b]. x ^ 2)",
             "([x]_x=a,b) + 2 * ([x ^ 2 / 2]_x=a,b) + [x ^ 3 / 3]_x=a,b"),
        ]

        rule = rules.OnSubterm(rules.CommonIntegral())
        for s, s2 in test_data:
            s = parse_expr(s)
            s2 = parse_expr(s2)
            self.assertEqual(rule.eval(s), s2)

    def testIntegral1(self):
        e = parse_expr("INT x:[2,3]. 2 * x + x ^ 2")
        e = rules.Linearity().eval(e)
        e = rules.OnSubterm(rules.CommonIntegral()).eval(e)
        e = rules.Simplify().eval(e)
        self.assertEqual(e, Const(Fraction("34/3")))

    def testSubstitution(self):
        e = parse_expr("INT x:[0,1]. (3 * x + 1) ^ (-2)")
        e = rules.Substitution("u", parse_expr("3 * x + 1")).eval(e)
        e = rules.Linearity().eval(e)
        e = rules.OnSubterm(rules.CommonIntegral()).eval(e)
        e = rules.Simplify().eval(e)
        self.assertEqual(e, Const(Fraction("1/4")))

    def testSubstitution2(self):
        e = parse_expr("INT x:[0,1]. exp(6*x)")
        e = rules.Substitution("u", parse_expr("6 * x")).eval(e)
        e = rules.Linearity().eval(e)
        e = rules.OnSubterm(rules.CommonIntegral()).eval(e)
        e = rules.Simplify().eval(e)
        self.assertEqual(e, parse_expr("1/6 * exp(6) + -1/6"))

    def testEquation(self):
        test_data = [
            "sin(x) ^ 3", "sin(x)^2 * sin(x)"
        ]
        e = parse_expr("INT x:[0, pi]. sin(x) ^ 3")
        e = rules.Equation(parse_expr("sin(x) ^ 3"), parse_expr("sin(x) ^ 2 * sin(x)")).eval(e)
        self.assertEqual(e, parse_expr("INT x:[0, pi]. sin(x) ^ 2 * sin(x)"))

    def testTrigSubstitution(self):
        test_data = [
            ("INT x:[0, pi]. $sin(x) ^ 2$ * sin(x)",
                {"INT x:[0,pi]. (1 - cos(x) ^ 2) * sin(x)",
                "INT x:[0,pi]. sin(x) ^ 2 * sin(x)",
                "INT x:[0,pi]. (1/2 - cos(2 * x) / 2) * sin(x)"}
            ),
            ("INT x:[0, pi]. $sin(3*x)*cos(2*x)$",
                {"INT x:[0,pi]. sin(x) / 2 + sin(5 * x) / 2",
                "INT x:[0,pi]. sin(3 * x) * cos(2 * x)",
                "INT x:[0,pi]. (-(sin(x) ^ 2) + cos(x) ^ 2) * sin(3 * x)"}
            )
        ]
        for s, s2 in test_data:
            s = parse_expr(s)
            result = rules.TrigSubstitution().eval(s)
            for i in range(len(result)):
                result[i] = str(result[i])
            self.assertEqual(set(result), s2)
    
    def testIntegrationByParts(self):
        e = parse_expr("INT x:[-1,2]. x * exp(x)")
        e = rules.IntegrationByParts(parse_expr("x"), parse_expr("exp(x)")).eval(e)
        e = rules.Simplify().eval(e)
        e = rules.OnSubterm(rules.CommonIntegral()).eval(e)
        e = rules.Simplify().eval(e)
        self.assertEqual(e, parse_expr("exp(2) + 2 * exp(-1)"))

    def testPolynomialDivision(self):
        test_data = [
        ("INT x:[4, exp(1) + 3].(x^3 - 12 * x^2 - 42) / (x-3)", "INT x:[4, exp(1) + 3].x ^ 2 + -9 * x + -27 + -123 / (x + -3)"),
        ("INT x:[-1, 0].(3*x^4+3*x^2+1)/(x^2 + 1)", "INT x:[-1, 0].3 * x ^ 2 + 1 / (x ^ 2 + 1)")
        ]

        rule = rules.PolynomialDivision()
        for e1, e2 in test_data:
            s1 = parse_expr(e1)
            s2 = parse_expr(e2)
            self.assertEqual(rule.eval(s1), s2)


if __name__ == "__main__":
    unittest.main()
