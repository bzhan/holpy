"""Unit test for rules."""

import unittest
import json
from fractions import Fraction

import backcall

from integral import expr, parser
from integral.expr import Const, deriv, neg_inf, Inf
from integral.parser import parse_expr
from integral import rules
from integral import compstate
from integral import conditions


class RulesTest(unittest.TestCase):

    def testCommonIndefiniteIntegral(self):
        test_data = [("INT x.1/x",'D','log(abs(x)) + SKOLEM_CONST(D)'),
                     ("INT x.a / (1+y^2)","C","a / (1 + y ^ 2) * x + SKOLEM_FUNC(C(a, y))"),
                    ]
        for s, c_name, res in test_data:
            e = parse_expr(s)
            e = rules.CommonIndefiniteIntegral(c_name).eval(e)
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

    def testUnfoldPower(self):
        test_data = [
            ("INT x:[1, 2].(x + y) ^ 3", "INT x:[1,2]. 3 * x * y ^ 2 + 3 * x ^ 2 * y + x ^ 3 + y ^ 3"),
            ("INT x:[1, 2].(x + y) ^ (1/2)", "INT x:[1,2]. (x + y) ^ (1/2)"),
            ("INT x:[1, 2].(1 + cos(2*x)) ^ 2", "INT x:[1,2]. cos(2 * x) ^ 2 + 2 * cos(2 * x) + 1")
        ]

        for s, res in test_data:
            s = parse_expr(s)
            rule = rules.UnfoldPower()
            self.assertEqual(str(rule.eval(s)), res)


    def testEquation(self):
        test_data = [
            "sin(x) ^ 3", "sin(x)^2 * sin(x)"
        ]
        e = parse_expr("INT x:[0, pi]. sin(x) ^ 3")
        e.body = rules.Equation(parse_expr("sin(x) ^ 2 * sin(x)")).eval(e.body)
        self.assertEqual(e, parse_expr("INT x:[0, pi]. sin(x) ^ 2 * sin(x)"))

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
    # def testLinearity(self):
    #     test_data = [("INT a:[1,2]. pi / a", "")]
    #     for a, b in test_data:
    #         a = parser.parse_expr(a)
    #         a = rules.Linearity().eval(a)
    #         a = rules.Simplify().eval(a)
    #         self.assertEqual(str(a), b)
    def testPolynomialDivision(self):
        test_data = [
            ("INT x:[4,exp(1) + 3]. (x^3 - 12 * x^2 - 42) / (x - 3)",
             "INT x:[4,exp(1) + 3]. x ^ 2 - 9 * x - 27 - 123 / (x - 3)"),
            ("INT x:[-1,0]. (3*x^4 + 3*x^2 + 1) / (x^2 + 1)",
             "INT x:[-1,0]. 3 * x ^ 2 + 1 / (x ^ 2 + 1)")
        ]

        rule = rules.PolynomialDivision()
        for s1, s2 in test_data:
            e1 = parse_expr(s1)
            self.assertEqual(str(rule.eval(e1)), s2)

    def testElimAbs(self):
        test_data = [
            ("INT x:[-pi/2, pi/2]. sqrt(cos(x))*abs(sin(x))",
             "(INT x:[-1/2 * pi,0]. -(sqrt(cos(x)) * sin(x))) + (INT x:[0,1/2 * pi]. sqrt(cos(x)) * sin(x))"),
            ("INT x:[0, pi]. sqrt(2) * abs(cos(x))",
             "(INT x:[1/2 * pi,pi]. -sqrt(2) * cos(x)) + (INT x:[0,1/2 * pi]. sqrt(2) * cos(x))"),
            ("INT u:[1,3]. u * abs(u) ^ -1",
             "INT u:[1,3]. 1"),
            ("INT u:[1,4]. 2 * u / (1 + abs(u))",
             "INT u:[1,4]. 2 * u * (u + 1) ^ -1"),
            ("INT x:[1/exp(1), 1]. abs(log(x))", "INT x:[exp(-1),1]. -log(x)"),
            ("INT x:[1,exp(1)]. abs(log(x))", "INT x:[1,exp(1)]. log(x)")
        ]

        for s, res in test_data:
            s = parse_expr(s)
            e = rules.ElimAbs().eval(s).normalize()
            self.assertEqual(str(e), res)

    def testElimAbs2(self):
        test_data = [
            ("INT u:[-2, 3]. 2 * u / (abs(u) + abs(u + 1))",
             "(INT u:[0,3]. 2 * u * (2 * u + 1) ^ (-1)) + (INT u:[-2,-1]. 2 * u * (-2 * u - 1) ^ (-1)) + (INT u:[-1,0]. 2 * u)")
        ]

        for s, res in test_data:
            e = parse_expr(s)
            e = rules.ElimAbs().eval(e).normalize()
            e = rules.OnSubterm(rules.ElimAbs()).eval(e).normalize()
            self.assertEqual(str(e), res)

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
            ("INT x:[0, 1]. sqrt(2 - x^2)", "u", "sqrt(2) * sin(u)", "INT u:[0,pi / 4]. sqrt(2 - (sqrt(2) * sin(u)) ^ 2) * 2 ^ (1/2) * cos(u)"),
            
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

    def testLimSep(self):
        test_data = [("LIM {x -> inf}. 3*x + 4*sin(x)", "(LIM {x -> oo}. (3) * (x)) + (LIM {x -> oo}. (4) * (sin(x)))"),
                     ("LIM {x -> 3 +}. x / (x-3)", "(LIM {x -> 3 +}. x) / (LIM {x -> 3 +}. x - 3)"),
                     ("LIM {x -> oo}. x", "LIM {x -> oo}.x"),
                     ("LIM {x -> oo}. (-x) - x", "(LIM {x -> oo}. (-x)) - (LIM {x -> oo}. x)"),
                     ("LIM {x -> -oo}. (1/x) + (2/x)", "(LIM {x -> -oo}. (1) / (x)) + (LIM {x -> -oo}. (2) / (x))"),
                     ("LIM {x -> -oo}. x / (x+sin(x))", "(LIM {x -> -oo}. x) / (LIM {x -> -oo}. (x) + (sin(x)))"),
                     ("LIM {x -> -oo}. (x^2) * x", "(LIM {x -> -oo}. (x) ^ (2)) * (LIM {x -> -oo}. x)"),
                     ("LIM {x -> 3 -}. x / sin(x+2)", "(LIM {x -> 3 -}. x) / (LIM {x -> 3 -}. sin((x) + (2)))"),
                     ("LIM {x -> 4 +}. cos(x) + x", "(LIM {x -> 4 +}. cos(x)) + (LIM {x -> 4 +}. x)"),
                     ("LIM {x -> 5}. x / tan(x)", "(LIM {x -> 5 }. x) / (LIM {x -> 5 }. tan(x))"),
                     ("LIM {x -> -oo}. log(x) * x", "(LIM {x -> -oo}. log(x)) * (LIM {x -> -oo}. x)"), ]
        for s1,s2 in test_data:
            e1,e2 = rules.LimSep().eval(parse_expr(s1)),parse_expr(s2)
            self.assertEqual(str(e1),str(e2))
    def testLHopital2(self):
        pass

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

    # def testExtractFromRoot(self):
    #     test_data = [
    #         ('sqrt(9*x*x - 5 * x)', '3*x', -1, "-(3 * x) * sqrt((9 * x * x - 5 * x) / (3 * x) ^ 2)")
    #     ]
    #     for a, b, c, d in test_data:
    #         a = parser.parse_expr(a)
    #         b = parser.parse_expr(b)
    #         e = rules.ExtractFromRoot(b, c).eval(a)
    #         self.assertEqual(str(e), d)

    def testIntegralSimplify(self):
        s = 'INT x:[-pi/4,pi/4].cos(x)*abs(cos(x))'
        res = '2 * (INT x:[0,pi / 4]. cos(x) * abs(cos(x)))'
        e = parser.parse_expr(s)
        r = rules.IntegralSimplify()
        e = r.eval(e)
        self.assertEqual(str(e), res)

    def testComputeLimit1(self):
        s = 'LIM {t -> oo}. exp(1/2 * t ^ 2 * (-(y ^ 2) - 1)) * (y ^ 2 + 1) ^ -1'
        e = parser.parse_expr(s)
        # TODO: fix answer
        # print(rules.LimitSimplify().eval(e))

    def testCosTransformationOfGaussion(self):
        # Overall goal
        goal = parser.parse_expr("INT x:[0, oo]. cos(tx)*exp(-(x^2)/2) = sqrt(pi/2)*exp(-(t^2)/2)")

        # Initial state
        st = compstate.CompFile('Integral1')

        # Make definition
        e = parser.parse_expr("I(t) = INT x:[0, oo]. cos(t*x)*exp(-(x^2)/2)")
        Idef = compstate.FuncDef(e)
        st.add_definition(Idef)
        conds = conditions.Conditions()

        e = parse_expr('I(0) = sqrt(pi/2)')
        lemma1 = compstate.Lemma(e)
        st.add_lemma(lemma1)

        # Prove the following equality
        e = parser.parse_expr('(D t. I(t)) = -t*I(t)')
        Eq1 = compstate.Goal(e, conds=conds)
        st.add_goal(Eq1)
        Eq1_proof = Eq1.proof_by_calculation()
        calc = Eq1_proof.lhs_calc
        calc.perform_rule(rules.OnLocation(rules.ExpandDefinition(Idef.eq), '0'))
        calc.perform_rule(rules.OnLocation(rules.ElimInfInterval(new_var='u'), '0'))
        calc.perform_rule(rules.FullSimplify())
        u = parse_expr('sin(t*x)')
        v = parse_expr('-exp(-x^2/2)')
        calc.perform_rule(rules.OnLocation(rules.IntegrationByParts(u, v), '0.0'))
        calc.perform_rule(rules.FullSimplify())

        calc = Eq1_proof.rhs_calc
        calc.perform_rule(rules.OnLocation(rules.ExpandDefinition(Idef.eq), '1'))
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.OnLocation(rules.ElimInfInterval(new_var='u'), '0.1'))

        Eq2 = compstate.Goal(parse_expr('(D t. log(I(t)) + t^2/2) = 0'), conds=conds)
        st.add_goal(Eq2)
        Eq2_proof = Eq2.proof_by_calculation()
        calc = Eq2_proof.lhs_calc
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.OnLocation(rules.ApplyEquation(Eq1.goal), '0.1'))
        calc.perform_rule(rules.FullSimplify())

        e = parse_expr('1/2 * t ^ 2 + log(I(t)) = SKOLEM_CONST(C)')
        Eq3 = compstate.Goal(e, conds=conds)
        st.add_goal(Eq3)
        Eq3_proof = Eq3.proof_by_rewrite_goal(begin=Eq2)
        calc = Eq3_proof.begin
        calc.perform_rule(rules.IntegralEquation(var='t', left_skolem_name='E', right_skolem_name=None))
        calc.perform_rule(rules.OnLocation(rules.CommonIndefiniteIntegral(const_name='C'), '1'))
        new_expr = parser.parse_expr("SKOLEM_CONST(C)")
        calc.perform_rule(rules.RewriteSkolemConst(new_expr=new_expr))

        e = parse_expr('log(sqrt(pi / 2)) = SKOLEM_CONST(C)')
        Eq4 = compstate.Goal(e, conds=conds)
        st.add_goal(Eq4)
        Eq4_proof = Eq4.proof_by_rewrite_goal(begin=Eq3)
        calc = Eq4_proof.begin
        calc.perform_rule(rules.LimitEquation('t', Const(0)))
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.OnLocation(rules.ApplyLemma(lemma=lemma1.lemma, conds=None), '0.0'))

        e = parse_expr('log(I(t)) = -t ^ 2 / 2 + log(sqrt(pi / 2))')
        Eq5 = compstate.Goal(e, conds=conds)
        st.add_goal(Eq5)
        Eq5_proof = Eq5.proof_by_calculation()
        calc = Eq5_proof.lhs_calc
        calc.perform_rule(rules.ApplyEquation(Eq3.goal))
        calc.perform_rule(rules.OnLocation(rules.ApplyEquation(Eq4.goal), '0'))
        calc.perform_rule(rules.FullSimplify())
        calc = Eq5_proof.rhs_calc
        calc.perform_rule(rules.FullSimplify())

        e = parse_expr('I(t) = sqrt(pi/2) * exp(-t^2/2)')
        Eq6 = compstate.Goal(e, conds=conds)
        st.add_goal(Eq6)
        Eq6_proof = Eq6.proof_by_rewrite_goal(begin=Eq5)
        calc = Eq6_proof.begin
        calc.perform_rule(rules.ExpEquation())
        calc.perform_rule(rules.OnLocation(rules.RewriteExp(), '1'))
        calc.perform_rule(rules.FullSimplify())
        # print(st)
        for i in range(2, 8):
            self.assertTrue(st.content[i].is_finished())
        with open('integral/examples/cosIntegral.json', 'w', encoding='utf-8') as f:
            json.dump(st.export(), f, indent=4, ensure_ascii=False, sort_keys=True)

    def testProbabilityIntegral(self):
        file = compstate.CompFile('probability integral')

        # Overall goal
        goal = parser.parse_expr("(INT x:[-oo,oo]. exp(-(x^2)/2)) = sqrt(2*pi)")

        # Make definition
        e = parser.parse_expr("g(t) = (INT x:[0,t].exp(-(x^2)/2))^2")
        Idef = compstate.FuncDef(e)
        file.add_definition(Idef)

        e = parser.parse_expr("(INT x:[-oo,oo]. exp(-x^2/2)) = 2 * LIM {t->oo}. sqrt(g(t))")
        Eq1 = compstate.Goal(e)
        file.add_goal(Eq1)
        Eq1_proof = Eq1.proof_by_calculation()
        calc = Eq1_proof.lhs_calc
        calc.perform_rule(rules.SplitRegion(Const(0)))
        e = parser.parse_expr('-x')
        calc.perform_rule(rules.OnLocation(rules.Substitution('y', e), '0'))
        e = parser.parse_expr('y')
        calc.perform_rule(rules.OnLocation(rules.Substitution('x', e), '0'))
        calc.perform_rule(rules.FullSimplify())
        calc = Eq1_proof.rhs_calc
        calc.perform_rule(rules.OnLocation(rules.ExpandDefinition(Idef.eq), '1.0.0'))
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.OnLocation(rules.RewriteLimit(), '1'))
        calc.perform_rule(rules.OnLocation(rules.ElimAbs(), '1'))

        e = '(D t. g(t) + 2 * INT y:[0, 1].exp(-(1+y^2)*t^2/2)/(1+y^2)) = 0'
        e = parser.parse_expr(e)
        Eq2 = compstate.Goal(e)
        file.add_goal(Eq2)
        Eq2_proof = Eq2.proof_by_calculation()
        calc = Eq2_proof.lhs_calc
        calc.perform_rule(rules.OnLocation(rules.ExpandDefinition(Idef.eq), '0.0'))
        calc.perform_rule(rules.FullSimplify())
        e = parser.parse_expr('x/t')
        calc.perform_rule(rules.OnLocation(rules.Substitution('y', e), '1.1'))
        e = parser.parse_expr('-exp(1/2 * t ^ 2 * (-(y ^ 2) - 1)) ')
        calc.perform_rule(rules.OnLocation(rules.Equation(e), '0.1.0'))
        e = parser.parse_expr('-1/2 * t ^ 2 * y ^ 2+1/2 * t ^ 2 *  (- 1) ')
        calc.perform_rule(rules.OnLocation(rules.Equation(e), '0.1.0.0.0'))
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.OnLocation(rules.RewriteExp(), '1.1.0'))
        calc.perform_rule(rules.FullSimplify())

        e = parser.parse_expr('2 * (INT y:[0,1]. exp(1/2 * t ^ 2 * (-(y ^ 2) - 1)) * (y ^ 2 + 1) ^ -1) + g(t) = SKOLEM_FUNC(C(y))')
        Eq3 = compstate.Goal(e)
        file.add_goal(Eq3)
        Eq3_proof = Eq3.proof_by_rewrite_goal(begin=Eq2)
        calc = Eq3_proof.begin
        calc.perform_rule(rules.IntegralEquation(var = 't',left_skolem_name='E',right_skolem_name=None))
        calc.perform_rule(rules.OnLocation(rules.CommonIndefiniteIntegral(const_name='C'), '1'))
        calc.perform_rule(rules.FullSimplify())
        new_expr = parser.parse_expr("SKOLEM_FUNC(C(y))")
        calc.perform_rule(rules.RewriteSkolemConst(new_expr=new_expr))


        e = parser.parse_expr("g(0) = 0")
        Eq4 = compstate.Goal(e)
        file.add_goal(Eq4)
        proof_of_Eq4 = Eq4.proof_by_calculation()
        calc = proof_of_Eq4.lhs_calc
        calc.perform_rule(rules.ExpandDefinition(Idef.eq))
        calc.perform_rule(rules.FullSimplify())

        e = parser.parse_expr("pi/2 = SKOLEM_FUNC(C(y))")
        Eq5 = compstate.Goal(e)
        file.add_goal(Eq5)
        proof_of_Eq5 = Eq5.proof_by_rewrite_goal(begin = Eq3)
        calc = proof_of_Eq5.begin
        calc.perform_rule(rules.LimitEquation('t', Const(0)))
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.OnLocation(rules.ApplyEquation(Eq4.goal), "0.0"))
        calc.perform_rule(rules.FullSimplify())

        e = parser.parse_expr("g(t) = -2 * (INT y:[0,1]. exp(1/2 * t ^ 2 * (-(y ^ 2) - 1)) * (y ^ 2 + 1) ^ -1) + 1/2 * pi")
        Eq6 = compstate.Goal(e)
        file.add_goal(Eq6)
        proof_of_Eq6 = Eq6.proof_by_calculation()
        calc = proof_of_Eq6.lhs_calc
        calc.perform_rule(rules.ApplyEquation(Eq3.goal))
        calc.perform_rule(rules.OnLocation(rules.ApplyEquation(Eq5.goal), '0'))
        calc.perform_rule(rules.FullSimplify())

        e = parser.parse_expr("(INT x:[-oo,oo]. exp(-x^2/2)) = sqrt(2*pi)")
        conds_of_Eq7 = compstate.Conditions()
        e2 = parser.parse_expr("y^2 + 1 > 0")
        conds_of_Eq7.add_condition(str(e2), e2)
        Eq7 = compstate.Goal(e, conds_of_Eq7)
        file.add_goal(Eq7)
        proof_of_Eq6 = Eq7.proof_by_calculation()
        calc = proof_of_Eq6.lhs_calc
        calc.perform_rule(rules.ApplyEquation(Eq1.goal))
        calc.perform_rule(rules.OnSubterm(rules.ApplyEquation(Eq6.goal)))
        calc.perform_rule(rules.OnLocation(rules.LimFunExchange(), '1'))
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.OnLocation(rules.LimIntExchange(), '1.0.0.1'))
        old_expr = parser.parse_expr("1/2 * t ^ 2 * (-(y ^ 2) - 1)")
        new_expr = parser.parse_expr("-1/2 * t^2 * (y^2+1)")
        calc.perform_rule(rules.Equation(old_expr=old_expr,new_expr=new_expr))
        calc.perform_rule(rules.FullSimplify())
        calc = proof_of_Eq6.rhs_calc
        calc.perform_rule(rules.FullSimplify())

        for i in range(1, 8):
            self.assertTrue(file.content[i].is_finished())
        with open('integral/examples/probabilityIntegral.json', 'w', encoding='utf-8') as f:
            json.dump(file.export(), f, indent=4, ensure_ascii=False, sort_keys=True)

    def testFullSimplify(self):
        test_data = [('LIM {x -> 1 }. (x ^ 2 - 1) / (x ^ 2 + 3 * x - 4)', "LIM {x -> 1 }. (x ^ 2 - 1) * (x ^ 2 + 3 * x - 4) ^ (-1)"),
                     ('LIM {x -> 1 }. (x-1) * tan(pi/2 * x)', "LIM {x -> 1 }. (x - 1) * tan(1/2 * pi * x)"),
                     ('LIM {x -> 0 }. sin(x) / x', "LIM {x -> 0 }. x ^ (-1) * sin(x)"),
                     ('SUM(k,0,oo,(-1) ^ k * x ^ (k + 1) / (k + 1) * (1/x))',
                      'x ^ (-1) * SUM(k, 0, oo, x ^ (k + 1) * (-1) ^ k * (k + 1) ^ (-1))'),
                     ('SUM(k,0,oo,(-1) ^ k * x ^ (k + 1) / (k + 1)) / x',
                      "x ^ (-1) * SUM(k, 0, oo, x ^ (k + 1) * (-1) ^ k * (k + 1) ^ (-1))"),
                     ("SUM(k, 0, oo, (-1) ^ (2*k+1) * x ^ (k + 1) / (k+1))",
                      "-SUM(k, 0, oo, x ^ (k + 1) * (k + 1) ^ (-1))"),]
        r = rules.FullSimplify()
        for s, res in test_data:
            e = parse_expr(s)
            e = r.eval(e)
            self.assertEqual(str(e), res)
    def testLimFunExchange(self):
        test_data = [
            ("LIM {x->3}. f(x,log(x))", "f(LIM {x -> 3 }. x,LIM {x -> 3 }. log(x))"),
            ("LIM {x->oo}. sqrt(x-sqrt(x))", "sqrt(LIM {x -> oo}. x - sqrt(x))"),
        ]

        for s, res in test_data:
            s = parser.parse_expr(s)
            e = rules.LimFunExchange().eval(s)
            self.assertEqual(str(e), res)

    def testRootFractionReWrite(self):
        test_data = [
            ("(x+3) / sqrt(9*x*x - 5 * x)", "((x + 3) ^ 2 / (9 * x * x - 5 * x) ^ 1) ^ (1/2)"),
            ("x^(1/2) / y^(1/6)", "(x ^ 3 / y ^ 1) ^ (1/6)")
        ]

        for s, s2 in test_data:
            s = parser.parse_expr(s)
            e = rules.RootFractionReWrite().eval(s)
            self.assertEqual(str(e), s2)

    def testFullSimplify2(self):
        test_data = [("INT x:[0, oo].D b.(x ^ 2 + b) ^ (-m - 1)","INT x:[0,oo]. D b. (x ^ 2 + b) ^ (-m - 1)"),
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
        for a, b in test_data:
            e = parser.parse_expr(a)
            res = rules.ExpandSeries().eval(e)
            self.assertEqual(str(res), b)

if __name__ == "__main__":
    unittest.main()
