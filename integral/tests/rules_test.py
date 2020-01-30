"""Unit test for rules."""

import unittest
from fractions import Fraction

from integral.expr import Const,deriv
from integral.parser import parse_expr
from integral import rules
from sympy.parsing import sympy_parser


class RulesTest(unittest.TestCase):
    def testSimplify(self):
        test_data = [
            ("INT x:[a,b]. x^(1/2) * x^(1/2)",
             "INT x:[a,b]. x"),
            ("INT x:[4, 9]. x^(1/2)*(1+x^(1/2))",
            "INT x:[4, 9]. x^(1/2) + x"),
            ("INT x:[0, pi/2]. (cos(x)^4 * sin(x) ^ 2) /  -(sin(x))",
            "INT x:[0, pi/2]. -cos(x) ^ 4 * csc(x) * sin(x) ^ 2"),
            ("INT x:[a, b]. (x ^ 2 + 2 * x  - x ^ 3 + sin(x)*x) /  (x * y * sin(z))",
            "INT x:[a,b]. x * y ^ -1 * csc(z) + -x ^ 2 * y ^ -1 * csc(z) + 2 * y ^ -1 * csc(z) + y ^ -1 * csc(z) * sin(x)")
        ]
        rule = rules.Simplify()
        for s1, s2 in test_data:
            s1 = parse_expr(s1)
            s2 = parse_expr(s2)
            self.assertEqual(rule.eval(s1), s2)

    def testLinearity(self):
        test_data = [
            ("INT x:[a,b]. 1 + 2 * x + x ^ 2",
             "2 * (INT x:[a,b]. x) + (INT x:[a,b]. 1) + (INT x:[a,b]. x ^ 2)"),
            ("(INT u:[1,-1]. -1 * u ^ 2 + 1) + pi", "(pi + (INT u:[1,-1]. 1)) - (INT u:[1,-1]. u ^ 2)"),
            ("INT t:[-pi / 4,pi / 4]. 8 ^ (1/2)", "2 ^ (3/2) * (INT t:[-pi / 4,pi / 4]. 1)"),
            ("1/2 * (INT t:[0,-1/2]. (-2)*exp(t))", "-(INT t:[0, -1/2]. exp(t))"),
            ("INT x:[-1, 1]. u / (u^2 + 1) + 1 / (u^2 + 1)", 
            "(INT x:[-1,1]. (1 + u ^ 2) ^ -1) + (INT x:[-1,1]. u * (1 + u ^ 2) ^ -1)"),
            ("INT x:[0,1]. (-1/2) * x ^ (2) / (1 + x ^ (2))",
            "-1/2 * (INT x:[0,1]. x ^ 2 * (1 + x ^ 2) ^ -1)")
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
            ("INT x:[a,b]. x ^ -1", "[log(abs(x))]_x=a,b"),
            ("INT x:[a,b]. 1 / x", "[log(abs(x))]_x=a,b"),
            ("INT x:[a,b]. 1 / x ^ 2", "[x ^ (-1) / (-1)]_x=a,b"),
            ("INT x:[a,b]. sin(x)", "[-cos(x)]_x=a,b"),
            ("INT x:[a,b]. cos(x)", "[sin(x)]_x=a,b"),
            ("INT x:[a,b]. 1 / (x ^ 2 + 1)", "[atan(x)]_x=a,b"),
            ("INT t:[a,b]. 8 ^ (1/2)", "[2 * 2 ^ (1/2) * t]_t=a,b"),
            ("INT x:[a,b]. (1 + x^2)^(-1)", "[atan(x)]_x=a,b"),
            ("INT x:[0, pi/4]. csc(x) ^ 2", "[-cot(x)]_x=0,pi / 4")
        ]

        rule = rules.CommonIntegral()
        for s, s2 in test_data:
            s = parse_expr(s)
            s2 = parse_expr(s2)
            self.assertEqual(rule.eval(s.normalize()), s2)

    def testOnSubterm(self):
        test_data = [
            ("(INT x:[a,b]. 1) + 2 * (INT x:[a,b]. x) + (INT x:[a,b]. x ^ 2)",
             "([x]_x=a,b) + 2 * ([x ^ 2 / 2]_x=a,b) + [x ^ 3 / 3]_x=a,b"),
             ("INT x:[0,pi]. cos(x) ^ 4", "INT x:[0,pi]. cos(x) ^ 4"),
            ("(INT x:[0,pi]. cos(x) ^ 2) - (INT x:[0,pi]. cos(x) ^ 4)", "(INT x:[0,pi]. cos(x) ^ 2) - (INT x:[0,pi]. cos(x) ^ 4)")
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
        self.assertEqual(e, Const(Fraction(34, 3)))

    def testSubstitution(self):
        e = parse_expr("INT x:[0,1]. (3 * x + 1) ^ (-2)")
        e, l = rules.Substitution1("u", parse_expr("3 * x + 1")).eval(e)
        e = rules.Linearity().eval(e)
        e = rules.OnSubterm(rules.CommonIntegral()).eval(e)
        e = rules.Simplify().eval(e)
        self.assertEqual(e, Const(Fraction("1/4")))

    def testSubstitution2(self):
        e = parse_expr("INT x:[0,1]. exp(6*x)")
        e, l = rules.Substitution1("u", parse_expr("6 * x")).eval(e)
        e = rules.Linearity().eval(e)
        e = rules.OnSubterm(rules.CommonIntegral()).eval(e)
        e = rules.Simplify().eval(e)
        self.assertEqual(e.normalize(), parse_expr("(-1/6) + 1/6 * exp(6)"))

    def testSubstitution3(self):
        e = parse_expr("INT x:[0, pi/2].sqrt(cos(x))*sin(x)")
        e, d = rules.Substitution1("u",parse_expr("cos(x)")).eval(e)
        self.assertEqual(e, parse_expr("INT u:[0,1]. u ^ (1/2)"))

    def testSubstitution4(self):
        e = parse_expr("INT x:[1, 4]. 1/(1+sqrt(x))")
        e, l = rules.Substitution1("u", parse_expr("sqrt(x)")).eval(e)
        self.assertEqual(e, parse_expr("INT u:[1,2]. 2 * u * (1 + u) ^ -1"))

    def testSubstitution5(self):
        e = parse_expr("INT t:[0, 1]. t * e^(-(t^2/2))")
        e, l = rules.Substitution1("u", parse_expr("t^2")).eval(e)
        self.assertEqual(e, parse_expr("INT u:[0,1]. 1/4 * e ^ -u"))

    def testSubstitution6(self):
        e = parse_expr("INT x:[-2, 0]. (x + 2)/(x^2 + 2*x + 2)")
        e = rules.Equation(e.body, parse_expr("((x+1) + 1)/((x+1)*(x+1) + 1)")).eval(e)
        e, l = rules.Substitution1("u", parse_expr("x+1")).eval(e)
        self.assertEqual(e, parse_expr("INT u:[-1,1]. (u + 1) / (u ^ 2 + 1)"))

    def testSubstitution7(self):
        e = parse_expr("INT x:[3/4, 1]. 1/(sqrt(1-x) - 1)")
        e, l = rules.Substitution1("u", parse_expr("sqrt(1 - x)")).eval(e)
        self.assertEqual(e, parse_expr("INT u:[0,1/2]. 2 * u * (-1 + u) ^ -1"))

    def testSubstitution8(self):
        e = parse_expr("INT x:[1, exp(1)]. sin(log(x))")
        e, l = rules.Substitution1("u", parse_expr("log(x)")).eval(e)
        self.assertEqual(e.normalize(), parse_expr("INT u:[0,1]. sin(u) * exp(u)"))

    def testSubstitution9(self):
        e = parse_expr("INT x:[1, exp(2)]. 1/(x * sqrt(1 + log(x)))")
        e, l = rules.Substitution1("u", parse_expr("1 + log(x)")).eval(e)
        self.assertEqual(e, parse_expr("INT u:[1,3]. u ^ (-1/2)"))

    def testSubstitution10(self):
        e = parse_expr("INT x:[0, 441]. (pi * sin(pi*sqrt(x))) / sqrt(x)")
        e, l = rules.Substitution1("u", parse_expr("pi * sqrt(x)")).eval(e)
        self.assertEqual(e, parse_expr("INT u:[0,21 * pi]. (2 * u * sin(sqrt(u ^ 2))) / sqrt(u ^ 2)"))

    def testUnfoldPower(self):
        test_data = [
            ("INT x:[1, 2].(x + y) ^ 3", "INT x:[1,2]. x ^ 3 + 3 * x ^ 2 * y + 3 * x * y ^ 2 + y ^ 3"),
            ("INT x:[1, 2].(x + y) ^ (1/2)", "INT x:[1,2]. (x + y) ^ (1/2)"),
            ("INT x:[1, 2].(1 + cos(2*x)) ^ 2", "INT x:[1,2]. cos(2 * x) ^ 2 + 2 * cos(2 * x) + 1")
        ]

        for s, s1 in test_data:
            s = parse_expr(s)
            s1 = parse_expr(s1)
            rule = rules.unfoldPower()
            self.assertEqual(rule.eval(s), s1)


    def testEquation(self):
        test_data = [
            "sin(x) ^ 3", "sin(x)^2 * sin(x)"
        ]
        e = parse_expr("INT x:[0, pi]. sin(x) ^ 3")
        e = rules.Equation(parse_expr("sin(x) ^ 3"), parse_expr("sin(x) ^ 2 * sin(x)")).eval(e)
        self.assertEqual(e, parse_expr("INT x:[0, pi]. sin(x) ^ 2 * sin(x)"))

    def testSubstitutionInverse(self):
        e = parse_expr("INT x:[0, sqrt(2)]. sqrt(2 - x^2)")
        e = rules.Substitution2("u", parse_expr("sqrt(2) * sin(u)")).eval(e)

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
                "INT x:[0,pi]. (-sin(x) ^ 2 + cos(x) ^ 2) * sin(3 * x)"}
            )
        ]
        for s, s2 in test_data:
            s = parse_expr(s)
            result = rules.TrigSubstitution().eval(s)
            for i in range(len(result)):
                result[i] = str(result[i][0])
            self.assertEqual(set(result), s2)
    
    def testIntegrationByParts(self):
        e = parse_expr("INT x:[-1,2]. x * exp(x)")
        e = rules.IntegrationByParts(parse_expr("x"), parse_expr("exp(x)")).eval(e)
        e = rules.Simplify().eval(e)
        e = rules.Linearity().eval(e)
        e = rules.OnSubterm(rules.CommonIntegral()).eval(e)
        e = rules.Simplify().eval(e)
        self.assertEqual(e, parse_expr("2 * exp(-1) + exp(2)"))

    def testPolynomialDivision(self):
        test_data = [
            ("INT x:[4, exp(1) + 3].(x^3 - 12 * x^2 - 42) / (x-3)", "INT x:[4, exp(1) + 3].x ^ 2 - 9 * x - 27 - 123 / (x -3)"),
            ("INT x:[-1, 0].(3*x^4+3*x^2+1)/(x^2 + 1)", "INT x:[-1, 0].3 * x ^ 2 + 1 / (x ^ 2 + 1)")
        ]

        rule = rules.PolynomialDivision()
        for e1, e2 in test_data:
            s1 = parse_expr(e1)
            s2 = parse_expr(e2)
            self.assertEqual(rule.eval(s1), s2)

    def testElimAbsByMonomial(self):
        test_data = [
            ("INT x:[-pi/2, pi/2]. sqrt(cos(x))*abs(sin(x))",
            "(INT x:[0,pi / 2]. cos(x) ^ (1/2) * sin(x)) + (INT x:[-pi / 2,0]. -cos(x) ^ (1/2) * sin(x))"),
            ("INT x:[0, pi]. sqrt(2) * abs(cos(x))", "(INT x:[0,pi / 2]. 2 ^ (1/2) * cos(x)) + (INT x:[pi / 2,pi]. -2 ^ (1/2) * cos(x))"),
            ("INT u:[1,3]. u * abs(u) ^ -1", "INT u:[1,3]. u * u ^ -1")
        ]

        for s, s1 in test_data:
            s = parse_expr(s)
            s1 = parse_expr(s1)
            rule = rules.ElimAbs()
            self.assertEqual(rules.OnSubterm(rules.ElimAbs()).eval(s).normalize(), s1.normalize())
    
    def testElimAbs(self):
        test_data = [
            ("INT u:[1, 4]. 2*u/(1 + abs(u))", "INT u:[1, 4]. 2*u/(1 + u)"),
            ("INT u:[-2, 3]. 2*u/(abs(u) + abs(u + 1))", "(INT u:[-2,-1]. 2 * u / (-u + -(u + 1))) + (INT u:[-1,0]. 2 * u / (-u + u + 1)) + (INT u:[0,3]. 2 * u / (u + u + 1))")
        ]

        for s, s1 in test_data:
            s = parse_expr(s)
            s1 = parse_expr(s1)
            self.assertEqual(rules.ElimAbs().eval(s).normalize(), s1.normalize())

    def testIntegrateByEquation(self):
        test_data = [
            ("INT x:[0,pi / 2]. exp(2 * x) * cos(x)", 
            "(-2) + exp(pi) + (-4) * (INT x:[0,pi / 2]. cos(x) * exp(2 * x))", 
            "-2/5 + exp(pi)/5"),
            ("INT u:[0,1]. exp(u) * sin(u)",
            "1 + (-1) * cos(1) * exp(1) + sin(1) * exp(1) + (-1) * (INT u:[0,1]. exp(u) * sin(u))",
            "(1/2 + (-(1/2) * cos(1)) * exp(1)) + ((1/2) * sin(1)) * exp(1)"),
            ("INT x:[0,pi / 2]. exp(2 * x) * cos(x)",
            "(-2 + exp(pi)) - 4 * (INT x:[0,pi / 2]. cos(x) * exp(2 * x))",
            "-2/5 + 1/5 * exp(pi)")
        ]

        for s, s1, s2 in test_data:
            s = parse_expr(s)
            s1 = parse_expr(s1)
            s2 = parse_expr(s2)
            rule = rules.IntegrateByEquation(s, s1)
            self.assertEqual(rule.eval().normalize(), s2.normalize())

    

    def testTrigSubstitution1(self):
        test_data = [
            ("INT x:[0, 1]. sqrt(2 - x^2)", "u", "sqrt(2) * sin(u)", "INT u:[0,pi / 4]. sqrt(2 - (sqrt(2) * sin(u)) ^ 2) * 2 ^ (1/2) * cos(u)"),
            
        ]

        for s, s1, s2, s3 in test_data:
            s = parse_expr(s)
            s2 = parse_expr(s2)
            s3 = parse_expr(s3)
            rule = rules.Substitution2(s1, s2)
            self.assertEqual(rule.eval(s).normalize(), s3.normalize())
            


if __name__ == "__main__":
    unittest.main()
 