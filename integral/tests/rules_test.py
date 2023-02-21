"""Unit test for rules."""

import unittest
from fractions import Fraction

from integral import parser, context
from integral.expr import Const
from integral.parser import parse_expr
from integral import rules
from integral.context import Context


class RulesTest(unittest.TestCase):
    def testIndefiniteIntegralIdentity(self):
        test_data = [
            ("INT x. x ^ -1", 'log(abs(x)) + SKOLEM_CONST(C)'),
            ("INT x [a, y]. a / (1 + y^2)", "a / (1 + y ^ 2) * x + SKOLEM_FUNC(C(a, y))"),
        ]

        ctx = Context()
        ctx.load_book('base')
        for s, res in test_data:
            e = parse_expr(s)
            e = rules.IndefiniteIntegralIdentity().eval(e, ctx=ctx)
            self.assertEqual(str(e), res)

    def testSimplify(self):
        # Note simplification does not expand products and powers.
        test_data = [
            ("INT x:[a,b]. x^(1/2) * x^(1/2)",
             "INT x:[a,b]. x"),
            ("INT x:[4,9]. x^(1/2)*(1+x^(1/2))",
             "INT x:[4,9]. sqrt(x) * (sqrt(x) + 1)"),
            ("INT x:[0,pi/2]. (cos(x)^4 * sin(x) ^ 2) /  -(sin(x))",
             "INT x:[0,1/2 * pi]. -(cos(x) ^ 4 * sin(x))"),
            ('(sqrt(x) - 2) * (sqrt(x) + 2)','(sqrt(x) + 2) * (sqrt(x) - 2)'),
            ('(-1)^n*x^(2*n+1)/(2*n+1)/x', "x ^ (2 * n) * (-1) ^ n * (2 * n + 1) ^ (-1)"),
        ]
        rule = rules.Simplify()
        for s1, s2 in test_data:
            s1 = parse_expr(s1)
            self.assertEqual(str(rule.eval(s1)), s2)

    def testLinearity(self):
        test_data = [
            ("INT x:[a,b]. 1 + 2 * x + x ^ 2",
             "(INT x:[a,b]. 1) + 2 * (INT x:[a,b]. x) + (INT x:[a,b]. x ^ 2)"),
            ("(INT u:[1,-1]. -1 * u ^ 2 + 1)",
             "-1 * (INT u:[1,-1]. u ^ 2) + (INT u:[1,-1]. 1)"),
            ("INT t:[-pi / 4,pi / 4]. 8 ^ (1/2)",
             "8 ^ (1/2) * (INT t:[-pi / 4,pi / 4]. 1)"),
            ("(INT t:[0,-1/2]. (-2)*exp(t))",
             "-2 * (INT t:[0,-1/2]. exp(t))"),
            ("INT x:[-1, 1]. u / (u^2 + 1) + 1 / (u^2 + 1)",
             "(INT x:[-1,1]. u / (u ^ 2 + 1)) + (INT x:[-1,1]. 1 / (u ^ 2 + 1))"),
            ("INT x:[0,1]. 1/2 * x ^ 2 * (1 + x ^ 2) ^ -1",
             "1/2 * (INT x:[0,1]. x ^ 2 * (x ^ 2 + 1) ^ (-1))"),
            ('SUM(k,0,oo,(-1) ^ k * x ^ (k + 1) / (k + 1)) / x',
             'SUM(k, 0, oo, (-1) ^ k * x ^ (k + 1) / (k + 1)) / x'),
            ("SUM(k,0,oo,(-1) ^ k * x ^ (k + 1) / (k + 1) * (1/x))",
             'x ^ (-1) * SUM(k, 0, oo, x ^ (k + 1) * (-1) ^ k * (k + 1) ^ (-1))'),
        ]

        rule = rules.Linearity()
        for s, s2 in test_data:
            s = parse_expr(s)
            self.assertEqual(str(rule.eval(s)), s2)

    def testCommonIntegral(self):
        test_data = [
            ("INT x:[a,b]. 1", "[x]_x=a,b"),
            ("INT x:[a,b]. 2", "[2 * x]_x=a,b"),
            ("INT x:[a,b]. x", "[x ^ 2 / 2]_x=a,b"),
            ("INT x:[a,b]. x ^ 2", "[x ^ 3 / 3]_x=a,b"),
            ("INT x:[a,b]. x ^ 3", "[x ^ 4 / 4]_x=a,b"),
            ("INT x:[a,b]. x ^ -1", "[log(abs(x))]_x=a,b"),
            ("INT x:[a,b]. 1 / x", "[log(abs(x))]_x=a,b"),
            ("INT x:[a,b]. 1 / x ^ 2", "[x ^ (-1) / -1]_x=a,b"),
            ("INT x:[a,b]. sin(x)", "[-cos(x)]_x=a,b"),
            ("INT x:[a,b]. cos(x)", "[sin(x)]_x=a,b"),
            ("INT x:[a,b]. 1 / (x ^ 2 + 1)", "[atan(x)]_x=a,b"),
            ("INT t:[a,b]. 8 ^ (1/2)", "[2 * sqrt(2) * t]_t=a,b"),
            ("INT x:[a,b]. (1 + x^2)^(-1)", "[atan(x)]_x=a,b"),
            ("INT x:[0, pi/4]. csc(x) ^ 2", "[-cot(x)]_x=0,1/4 * pi")
        ]

        rule = rules.CommonIntegral()
        for s, s2 in test_data:
            s = parse_expr(s)
            self.assertEqual(str(rule.eval(s.normalize())), s2)

    def testTrigSimplify(self):
        test_data = [
            ("sin(1/2 * pi - x)", "cos(x)"),
            ("cos(1/2 * pi - x)", "sin(x)"),
        ]

        rule = rules.TrigSimplify()
        for s, s2 in test_data:
            s = parse_expr(s)
            self.assertEqual(str(rule.eval(s)), s2)

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
        self.assertEqual(str(e.normalize()), "1/6 * exp(6) - 1/6")

    def testSubstitution3(self):
        e = parse_expr("INT x:[0, pi/2].sqrt(cos(x))*sin(x)")
        e = rules.Substitution("u",parse_expr("cos(x)")).eval(e)
        self.assertEqual(e, parse_expr("INT u:[0,1]. sqrt(u)"))

    def testSubstitution4(self):
        e = parse_expr("INT x:[1, 4]. 1/(1+sqrt(x))")
        e = rules.Substitution("u", parse_expr("sqrt(x)")).eval(e)
        self.assertEqual(str(e), "INT u:[1,2]. 2 * u * (u + 1) ^ (-1)")

    def testSubstitution5(self):
        e = parse_expr("INT t:[0, 1]. t * exp(-(t^2/2))")
        e = rules.Substitution("u", parse_expr("-t^2/2")).eval(e)
        self.assertEqual(str(e), "INT u:[-1/2,0]. exp(u)")

    def testSubstitution6(self):
        e = parse_expr("INT x:[-2, 0]. (x + 2)/(x^2 + 2*x + 2)")
        e.body = rules.Equation(e.body, parse_expr("((x+1) + 1)/((x+1)*(x+1) + 1)")).eval(e.body)
        e = rules.Substitution("u", parse_expr("x+1")).eval(e)
        self.assertEqual(str(e), "INT u:[-1,1]. (u + 1) * ((u - 1) ^ 2 + 2 * u) ^ (-1)")

    def testSubstitution7(self):
        e = parse_expr("INT x:[3/4, 1]. 1/(sqrt(1-x) - 1)")
        e = rules.Substitution("u", parse_expr("sqrt(1 - x)")).eval(e)
        self.assertEqual(str(e), "INT u:[0,1/2]. 2 * u * (u - 1) ^ (-1)")

    def testSubstitution8(self):
        e = parse_expr("INT x:[1, exp(1)]. sin(log(x))")
        e = rules.Substitution("u", parse_expr("log(x)")).eval(e)
        self.assertEqual(e.normalize(), parse_expr("INT u:[0,1]. exp(u) * sin(u)"))

    def testSubstitution9(self):
        e = parse_expr("INT x:[1, exp(2)]. 1/(x * sqrt(1 + log(x)))")
        e = rules.Substitution("u", parse_expr("1 + log(x)")).eval(e)
        self.assertEqual(e, parse_expr("INT u:[1,3]. u ^ (-1/2)"))

    def testSubstitution10(self):
        e = parse_expr("INT x:[0, 441]. (pi * sin(pi*sqrt(x))) / sqrt(x)")
        e = rules.Substitution("u", parse_expr("pi * sqrt(x)")).eval(e)
        self.assertEqual(e, parse_expr("INT u:[0,21 * pi]. 2 * sin(u)"))

    def testSustitution11(self):
        e = parser.parse_expr("INT x:[0,1]. sqrt(-log(x))")
        r = rules.Substitution("y", "-log(x)")
        ctx = context.Context()
        res = r.eval(e, ctx)
        self.assertEqual(res, parser.parse_expr("INT y:[0,oo]. sqrt(y) * exp(-y)"))
        
    # Caused by there is no default simplification for fraction in rules.py, Line 291
    # def testSubstitution11(self):
    #     e = parse_expr("INT x:[0, 1]. (2 * x + 1)/(2 * x ^ 2 + 2 * x + 1)")
    #     res = rules.Substitution("u", parse_expr("2 * x ^ 2 + 2 * x + 1")).eval(e)
    #     self.assertEqual(str(res), "INT u:[1,5]. 1/2 * u ^ -1")

    # def testSubstitution12(self):
    #     e = parse_expr("INT x:[0, 1]. x ^ 3 / (1 + x ^ 4) ^ (1/4)")
    #     res = rules.Substitution("u", parse_expr("1 + x ^ 4")).eval(e)
    #     self.assertEqual(str(res), "INT u:[1,2]. 1/4 * u ^ (-1/4)")

    def testSubstitution13(self):
        e = parse_expr('INT t:[pi / 2,pi]. 1/2 * log(a * sin(t))')
        res = rules.SubstitutionInverse('x', parse_expr('pi-x')).eval(e)
        self.assertEqual(str(res), "-(INT x:[0,pi / 2]. 1/2 * log(a * sin(pi - x)) * -1)")

    def testEquation(self):
        test_data = [
            ("sin(x) ^ 3", "sin(x)^2 * sin(x)","sin(x) ^ 2 * sin(x)"),
            ("5 * x ^ 2 + 4 * x ^ 4 + x ^ 6 + 2", "(1+x^2)^2 * (2+x^2)","(1 + x ^ 2) ^ 2 * (2 + x ^ 2)")
        ]
        for a, b, c in test_data:
            e = parse_expr(a)
            ee = parse_expr(b)
            res = rules.Equation(old_expr=e, new_expr=ee).eval(e)
            self.assertEqual(str(res), c)

    def testSubstitutionInverse(self):
        e = parse_expr("INT x:[0, sqrt(2)]. sqrt(2 - x^2)")
        e = rules.SubstitutionInverse("u", parse_expr("sqrt(2) * sin(u)")).eval(e)

    # def testTrigSubstitution(self):
    #     test_data = [
    #         ("INT x:[0, pi]. $sin(x) ^ 2$ * sin(x)",
    #             {"INT x:[0,pi]. (1 - cos(x) ^ 2) * sin(x)",
    #             "INT x:[0,pi]. sin(x) ^ 2 * sin(x)",
    #             "INT x:[0,pi]. (1/2 - cos(2 * x) / 2) * sin(x)"}
    #         ),
    #         ("INT x:[0, pi]. $sin(3*x)*cos(2*x)$",
    #             {"INT x:[0,pi]. sin(x) / 2 + sin(5 * x) / 2",
    #             "INT x:[0,pi]. sin(3 * x) * cos(2 * x)",
    #             "INT x:[0,pi]. (-sin(x) ^ 2 + cos(x) ^ 2) * sin(3 * x)"}
    #         )
    #     ]
    #     for s, s2 in test_data:
    #         s = parse_expr(s)
    #         result = rules.TrigSubstitution().eval(s)
    #         for i in range(len(result)):
    #             result[i] = str(result[i][0])
    #         self.assertEqual(set(result), s2)
    
    def testIntegrationByParts(self):
        e = parse_expr("INT x:[-1,2]. x * exp(x)")
        e = rules.IntegrationByParts(parse_expr("x"), parse_expr("exp(x)")).eval(e)
        e = rules.Simplify().eval(e)
        e = rules.Linearity().eval(e)
        e = rules.OnSubterm(rules.CommonIntegral()).eval(e)
        e = rules.Simplify().eval(e)
        self.assertEqual(str(e.normalize()), "2 * exp(-1) + exp(2)")

    def testApplyEquation(self):
        test_data = [("U = (INT x:[0, h/a]. (f(a*x) - f(0)) / x)", "U", "INT x:[0,h / a]. (f(a * x) - f(0)) / x"),
                     ("f(a,b) = a + b + 3", "f(a,2)", "a + 2 + 3"),
                     ("a = 3", "a", "3"),]
        for eq, e, res in test_data:
            r = rules.ApplyEquation(parser.parse_expr(eq))
            self.assertEqual(res, str(r.eval(parser.parse_expr(e))))

    def testIntegrateByEquation(self):
        test_data = [
            ("INT x:[0,pi / 2]. exp(2 * x) * cos(x)", 
             "(-2) + exp(pi) + (-4) * (INT x:[0,pi / 2]. cos(x) * exp(2 * x))", 
             "-2/5 + exp(pi)/5"),
            ("INT u:[0,1]. exp(u) * sin(u)",
             "1 + (-1) * cos(1) * exp(1) + sin(1) * exp(1) + (-1) * (INT u:[0,1]. exp(u) * sin(u))",
             "(1 + -1 * cos(1) * exp(1) + sin(1) * exp(1)) * (1/2)"),
            ("INT x:[0,pi / 2]. exp(2 * x) * cos(x)",
             "(-2 + exp(pi)) - 4 * (INT x:[0,pi / 2]. cos(x) * exp(2 * x))",
             "-2/5 + 1/5 * exp(pi)")
        ]

        for s, s1, s2 in test_data:
            s = parse_expr(s)
            s1 = parse_expr(s1)
            s2 = parse_expr(s2)
            rule = rules.IntegrateByEquation(s)
            res = rule.eval(s1)
            self.assertEqual(res.normalize(), s2.normalize())

    def testTrigSubstitution1(self):
        test_data = [
            ("INT x:[0, 1]. sqrt(2 - x^2)", "u", "sqrt(2) * sin(u)",
             "INT u:[0,pi / 4]. sqrt(2 - (sqrt(2) * sin(u)) ^ 2) * 2 ^ (1/2) * cos(u)"),   
        ]

        for s, s1, s2, s3 in test_data:
            s = parse_expr(s)
            s2 = parse_expr(s2)
            s3 = parse_expr(s3)
            rule = rules.SubstitutionInverse(s1, s2)
            self.assertEqual(rule.eval(s).normalize(), s3.normalize())
            
    def testElimInfInterval(self):
        test_data = [
            ("INT x:[-inf, inf]. 1/x",Const(2),"(LIM {t -> -oo}. INT x:[t,2]. 1 / x) + (LIM {t -> oo}. INT x:[2,t]. 1 / x)"),
            ("INT x:[inf, -inf]. 1/x",Const(3),"(LIM {t -> oo}. INT x:[t,3]. 1 / x) + (LIM {t -> -oo}. INT x:[3,t]. 1 / x)")
        ]
        for s1,a,s2 in test_data:
            e = parse_expr(s1)
            e = rules.ElimInfInterval(a).eval(e)
            self.assertEqual(str(e), s2)

    def testElimInfInterval2(self):
        test_data = [
            ("INT x:[1, inf]. 1/x", "LIM {t -> oo}. INT x:[1,t]. 1 / x"),
            ('INT x:[-inf,inf]. 1/x', "(LIM {t -> -oo}. INT x:[t,0]. (1) / (x)) + (LIM {t -> oo}. INT x:[0,t]. (1) / (x))"),
            ('INT x:[-inf,3]. log(x) + sin(x) + x^2',"LIM {t -> -oo}. INT x:[t,3]. ((log(x)) + (sin(x))) + ((x) ^ (2))"),

        ]
        for s1, s2 in test_data:
            e1 = parse_expr(s1)
            e1 = rules.ElimInfInterval().eval(e1)
            e2 = parse_expr(s2)
            self.assertEqual(e1, e2)

    def testDerivativeSimplify(self):
        test_data = [
            ("D x. x", '1'),
            ("D x. log(x)", 'x ^ (-1)'),
            ("D x. sin(x^2)", '2 * x * cos(x ^ 2)'),
            ("D x. sin(x+y) * y + 3", 'y * cos(x + y)'),
            ("D y. tan(log(x)+y) * y^2 + cos(y) - y + 3",
             'y ^ 2 * sec(log(x) + y) ^ 2 + 2 * y * tan(log(x) + y) - sin(y) - 1'),
            ('D z. exp(2*z) + 1/cos(z) + 1/z * z', 'cos(z) ^ (-2) * sin(z) + 2 * exp(2 * z)'),
            ('D x. (2*x +x^2 + cos(x)) / (sin(x) + tan(x))',
             '(sin(x) + tan(x)) ^ -2 * (-((sec(x) ^ 2 + cos(x)) * (x ^ 2 + cos(x) + 2 * x)) + (sin(x) + tan(x)) * (-sin(x) + 2 * x + 2))'),
        ]
        for a, b in test_data:
            a, b = parser.parse_expr(a), parser.parse_expr(b)
            self.assertEqual(str(rules.DerivativeSimplify().eval(a)), str(b))

    # def testLimitCompute1(self):
    #     t = 'LIM {x -> oo}. (x+3) / sqrt(9*x*x - 5 * x)'
    #     res = "1/3"
    #
    #
    # def testLimitCompute2(self):
    #     t = 'LIM {x -> -oo}. (x+3) / sqrt(9*x*x - 5 * x)'
    #     res = "-1/3"

    def testComputeLimit1(self):
        s = 'LIM {t -> oo}. exp(1/2 * t ^ 2 * (-(y ^ 2) - 1)) * (y ^ 2 + 1) ^ -1'
        e = parser.parse_expr(s)
        # TODO: fix answer
        # print(rules.LimitSimplify().eval(e))

    def testFullSimplify(self):
        test_data = [
            ('LIM {x -> 1 }. (x ^ 2 - 1) / (x ^ 2 + 3 * x - 4)', "LIM {x -> 1 }. (x ^ 2 - 1) * (x ^ 2 + 3 * x - 4) ^ (-1)"),
            ('LIM {x -> 1 }. (x-1) * tan(pi/2 * x)', "LIM {x -> 1 }. (x - 1) * tan(1/2 * pi * x)"),
            ('LIM {x -> 0 }. sin(x) / x', "LIM {x -> 0 }. x ^ (-1) * sin(x)"),
            ('SUM(k,0,oo,(-1) ^ k * x ^ (k + 1) / (k + 1) * (1/x))',
             'x ^ (-1) * SUM(k, 0, oo, x ^ (k + 1) * (-1) ^ k * (k + 1) ^ (-1))'),
            ('SUM(k,0,oo,(-1) ^ k * x ^ (k + 1) / (k + 1)) / x',
             "x ^ (-1) * SUM(k, 0, oo, x ^ (k + 1) * (-1) ^ k * (k + 1) ^ (-1))"),
            ("SUM(k, 0, oo, (-1) ^ (2*k+1) * x ^ (k + 1) / (k+1))",
             "-SUM(k, 0, oo, x ^ (k + 1) * (k + 1) ^ (-1))"),
            ("(c * x ^ a) ^ k * log(x) ^ k", "log(x) ^ k * (c * x ^ a) ^ k"),
        ]

        for s, res in test_data:
            e = parse_expr(s)
            e = rules.FullSimplify().eval(e)
            self.assertEqual(str(e), res)

    def testFullSimplify2(self):
        test_data = [
            ("INT x:[0,oo]. D b. (x ^ 2 + b) ^ (-m - 1)", "INT x:[0,oo]. D b. (x ^ 2 + b) ^ (-m - 1)"),
        ]
        for s,res in test_data:
            s = parse_expr(s)
            rules.FullSimplify().eval(s)
            self.assertEqual(str(s), res)


    def testExpandSeries(self):
        test_data = [
            ('exp(x)', 'SUM(n, 0, oo, x ^ n / factorial(n))'),
            ('sin(x)', 'SUM(n, 0, oo, (-1) ^ n * x ^ (2 * n + 1) / factorial(2 * n + 1))'),
            ('atan(x)', 'SUM(n, 0, oo, (-1) ^ n * x ^ (2 * n + 1) / (2 * n + 1))')
        ]

        ctx = Context()
        ctx.load_book('base')
        for a, b in test_data:
            e = parser.parse_expr(a)
            res = rules.SeriesExpansionIdentity().eval(e, ctx=ctx)
            self.assertEqual(str(res), b)

    def testExpandPolynomial(self):
        test_data = [
            ('x ^ 3 * (x ^ (-2) + 1)', 'x ^ 3 + x'),
        ]

        for a, b in test_data:
            e = parser.parse_expr(a)
            res = rules.ExpandPolynomial().eval(e)
            self.assertEqual(str(res), b)

    def testSolveEquation(self):
        test_data = [
            ("a + I(1) = b - I(1)", "I(1)", "I(1) = -1/2 * a + 1/2 * b"),
            ("factorial(2 * z + 1) = 2/sqrt(pi) * (1/2)^(-2*z)*(factorial(z) * factorial(z+1/2))", "factorial(z) * factorial(z + 1/2)","factorial(z) * factorial(z + 1/2) = sqrt(pi) / 2 * (1/2) ^ (2 * z) * factorial(2 * z + 1)")
        ]
        ctx = context.Context()
        for a, b, c in test_data:
            e = parse_expr(a)
            res = rules.SolveEquation(parse_expr(b)).eval(e, ctx)
            self.assertEqual(str(res), c)

    def testDefiniteIntegralIdentity(self):
        test_data = [("(INT x:[1,oo]. log(x) / (x^2+1))", "G"),]
        ctx = context.Context()
        ctx.load_book("interesting", upto="xxx")
        r = rules.DefiniteIntegralIdentity()
        for e, res in test_data:
            e = parse_expr(e)
            self.assertEqual(str(r.eval(e, ctx)), str(res))


if __name__ == "__main__":
    unittest.main()
