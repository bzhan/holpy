"""Unit test for rules."""

import unittest
from fractions import Fraction

from integral import expr, parser
from integral.expr import Const, deriv, neg_inf, Inf
from integral.parser import parse_expr
from integral import rules
from integral import compstate
from integral import conditions


class RulesTest(unittest.TestCase):
    def testSimplify(self):
        test_data = [
            ("INT x:[a,b]. x^(1/2) * x^(1/2)",
             "INT x:[a,b]. x"),
            ("INT x:[4,9]. x^(1/2)*(1+x^(1/2))",
             "INT x:[4,9]. sqrt(x) + x"),
            ("INT x:[0,pi/2]. (cos(x)^4 * sin(x) ^ 2) /  -(sin(x))",
             "INT x:[0,1/2 * pi]. -(cos(x) ^ 4 * sin(x))"),
            ('(sqrt(x)-2)*(sqrt(x)+2)','-4 + x')
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
            ("INT x:[0,1]. 1/2 * x ^ 2 * (1 + x ^ 2) ^ -1", "1/2 * (INT x:[0,1]. x ^ 2 * (1 + x ^ 2) ^ -1)")
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
            ("INT x:[a,b]. 1 / x ^ 2", "[x ^ -1 / -1]_x=a,b"),
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
        e = rules.Substitution1("u", parse_expr("3 * x + 1")).eval(e)
        e = rules.Linearity().eval(e)
        e = rules.OnSubterm(rules.CommonIntegral()).eval(e)
        e = rules.Simplify().eval(e)
        self.assertEqual(e, Const(Fraction("1/4")))

    def testSubstitution2(self):
        e = parse_expr("INT x:[0,1]. exp(6*x)")
        e = rules.Substitution1("u", parse_expr("6 * x")).eval(e)
        e = rules.Linearity().eval(e)
        e = rules.OnSubterm(rules.CommonIntegral()).eval(e)
        e = rules.Simplify().eval(e)
        self.assertEqual(str(e.normalize()), "-1/6 + 1/6 * exp(6)")

    def testSubstitution3(self):
        e = parse_expr("INT x:[0, pi/2].sqrt(cos(x))*sin(x)")
        e = rules.Substitution1("u",parse_expr("cos(x)")).eval(e)
        self.assertEqual(e, parse_expr("INT u:[0,1]. sqrt(u)"))

    def testSubstitution4(self):
        e = parse_expr("INT x:[1, 4]. 1/(1+sqrt(x))")
        e = rules.Substitution1("u", parse_expr("sqrt(x)")).eval(e)
        self.assertEqual(str(e), "INT u:[1,2]. 2 * u * (1 + u) ^ -1")

    def testSubstitution5(self):
        e = parse_expr("INT t:[0, 1]. t * exp(-(t^2/2))")
        e = rules.Substitution1("u", parse_expr("-t^2/2")).eval(e)
        self.assertEqual(e, parse_expr("INT u:[-1/2,0]. exp(u)"),"%s"%e)

    def testSubstitution6(self):
        e = parse_expr("INT x:[-2, 0]. (x + 2)/(x^2 + 2*x + 2)")
        e.body = rules.Equation(e.body, parse_expr("((x+1) + 1)/((x+1)*(x+1) + 1)")).eval(e.body)
        e = rules.Substitution1("u", parse_expr("x+1")).eval(e)
        self.assertEqual(e, parse_expr("INT u:[-1,1]. u * (2 * u + (-1 + u) ^ 2) ^ -1 + (2 * u + (-1 + u) ^ 2) ^ -1"))

    def testSubstitution7(self):
        e = parse_expr("INT x:[3/4, 1]. 1/(sqrt(1-x) - 1)")
        e = rules.Substitution1("u", parse_expr("sqrt(1 - x)")).eval(e)
        self.assertEqual(str(e), "INT u:[0,1/2]. 2 * u * (-1 + u) ^ -1")

    def testSubstitution8(self):
        e = parse_expr("INT x:[1, exp(1)]. sin(log(x))")
        e = rules.Substitution1("u", parse_expr("log(x)")).eval(e)
        self.assertEqual(e.normalize(), parse_expr("INT u:[0,1]. exp(u) * sin(u)"))

    def testSubstitution9(self):
        e = parse_expr("INT x:[1, exp(2)]. 1/(x * sqrt(1 + log(x)))")
        e = rules.Substitution1("u", parse_expr("1 + log(x)")).eval(e)
        self.assertEqual(e, parse_expr("INT u:[1,3]. u ^ (-1/2)"))

    def testSubstitution10(self):
        e = parse_expr("INT x:[0, 441]. (pi * sin(pi*sqrt(x))) / sqrt(x)")
        e = rules.Substitution1("u", parse_expr("pi * sqrt(x)")).eval(e)
        self.assertEqual(e, parse_expr("INT u:[0,21 * pi]. 2 * sin(u)"))

    # Caused by there is no default simplification for fraction in rules.py, Line 291
    # def testSubstitution11(self):
    #     e = parse_expr("INT x:[0, 1]. (2 * x + 1)/(2 * x ^ 2 + 2 * x + 1)")
    #     res = rules.Substitution1("u", parse_expr("2 * x ^ 2 + 2 * x + 1")).eval(e)
    #     self.assertEqual(str(res), "INT u:[1,5]. 1/2 * u ^ -1")

    # def testSubstitution12(self):
    #     e = parse_expr("INT x:[0, 1]. x ^ 3 / (1 + x ^ 4) ^ (1/4)")
    #     res = rules.Substitution1("u", parse_expr("1 + x ^ 4")).eval(e)
    #     self.assertEqual(str(res), "INT u:[1,2]. 1/4 * u ^ (-1/4)")

    def testUnfoldPower(self):
        test_data = [
            ("INT x:[1, 2].(x + y) ^ 3", "INT x:[1,2]. 3 * x * y ^ 2 + 3 * x ^ 2 * y + x ^ 3 + y ^ 3"),
            ("INT x:[1, 2].(x + y) ^ (1/2)", "INT x:[1,2]. (x + y) ^ (1/2)"),
            ("INT x:[1, 2].(1 + cos(2*x)) ^ 2", "INT x:[1,2]. 1 + 2 * cos(2 * x) + cos(2 * x) ^ 2")
        ]

        for s, s1 in test_data:
            s = parse_expr(s)
            s1 = parse_expr(s1)
            rule = rules.UnfoldPower()
            self.assertEqual(rule.eval(s), s1)


    def testEquation(self):
        test_data = [
            "sin(x) ^ 3", "sin(x)^2 * sin(x)"
        ]
        e = parse_expr("INT x:[0, pi]. sin(x) ^ 3")
        e.body = rules.Equation(parse_expr("sin(x) ^ 2 * sin(x)")).eval(e.body)
        self.assertEqual(e, parse_expr("INT x:[0, pi]. sin(x) ^ 2 * sin(x)"))

    def testSubstitutionInverse(self):
        e = parse_expr("INT x:[0, sqrt(2)]. sqrt(2 - x^2)")
        e = rules.Substitution2("u", parse_expr("sqrt(2) * sin(u)")).eval(e)

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

    def testPolynomialDivision(self):
        test_data = [
            ("INT x:[4, exp(1) + 3].(x^3 - 12 * x^2 - 42) / (x-3)", "INT x:[4, exp(1) + 3].x ^ 2 - 9 * x - 27 - 123 / (x -3)"),
            ("INT x:[-1, 0].(3*x^4+3*x^2+1)/(x^2 + 1)", "INT x:[-1, 0].3 * x ^ 2 + 1 / (x ^ 2 + 1)"),
            ("INT x:[0,1]. (2*x+5)*(x^2+5*x)^7", "INT x:[0,1]. (2*x+5)*(x^2+5*x)^7")
        ]

        rule = rules.PolynomialDivision()
        for e1, e2 in test_data:
            s1 = parse_expr(e1)
            s2 = parse_expr(e2)
            self.assertEqual(rule.eval(s1.body), s2.body)

    def testElimAbs(self):
        test_data = [
            ("INT x:[-pi/2, pi/2]. sqrt(cos(x))*abs(sin(x))",
             "(INT x:[0,1/2 * pi]. sqrt(cos(x)) * sin(x)) + (INT x:[-1/2 * pi,0]. -(sqrt(cos(x)) * sin(x)))"),
            ("INT x:[0, pi]. sqrt(2) * abs(cos(x))",
             "(INT x:[0,1/2 * pi]. sqrt(2) * cos(x)) + (INT x:[1/2 * pi,pi]. -sqrt(2) * cos(x))"),
            ("INT u:[1,3]. u * abs(u) ^ -1",
             "INT u:[1,3]. 1"),
            ("INT u:[1,4]. 2 * u / (1 + abs(u))",
             "INT u:[1,4]. 2 * u * (1 + u) ^ -1"),
            ("INT x:[1/exp(1), 1]. abs(log(x))", "INT x:[exp(-1),1]. -log(x)"),
            ("INT x:[1,exp(1)]. abs(log(x))", "INT x:[1,exp(1)]. log(x)")
        ]

        for s, s1 in test_data:
            s, s1 = parse_expr(s), parse_expr(s1)
            e = rules.ElimAbs().eval(s).normalize()
            self.assertEqual(e, s1)

    def testElimAbs2(self):
        test_data = [
            ("INT u:[-2, 3]. 2 * u / (abs(u) + abs(u + 1))",
             "(INT u:[-1,0]. 2 * u) + (INT u:[-2,-1]. 2 * u * (-1 + -2 * u) ^ -1) + (INT u:[0,3]. 2 * u * (1 + 2 * u) ^ -1)")
        ]

        for s, s1 in test_data:
            e = parse_expr(s)
            e = rules.ElimAbs().eval(e).normalize()
            e = rules.OnSubterm(rules.ElimAbs()).eval(e).normalize()
            self.assertEqual(str(e), s1)

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
            rule = rules.Substitution2(s1, s2)
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
            ("D x. x",'1'),
            ( "D x. log(x)",'x ^ (-1)'),
            ("D x. sin(x^2)",'2 * x * cos(x ^ 2)'),
            ("D x. sin(x+y) * y + 3",'y * cos(x + y)'),
            ("D y. tan(log(x)+y) * y^2 + cos(y) - y + 3", '-1 + 2 * y * tan(y + log(x)) + y ^ 2 * sec(y + log(x)) ^ 2 + -sin(y)'),
            ('D z. exp(2*z) + 1/cos(z) + 1/z * z','cos(z) ^ (-2) * sin(z) + 2 * exp(2 * z)'),
            ( 'D x. (2*x +x^2 + cos(x)) / (sin(x) + tan(x))','(-2 * x * cos(x) + -2 * x * sec(x) ^ 2 + 2 * x * sin(x) + 2 * x * tan(x) + -(x ^ 2 * cos(x)) + -(x ^ 2 * sec(x) ^ 2) + -(cos(x) * sec(x) ^ 2) + -(cos(x) ^ 2) + 2 * sin(x) + -(sin(x) * tan(x)) + -(sin(x) ^ 2) + 2 * tan(x)) / (sin(x) + tan(x)) ^ 2'),
        ]
        for a, b in test_data:
            a, b = parser.parse_expr(a), parser.parse_expr(b)
            self.assertEqual(str(rules.DerivativeSimplify().eval(a)), str(b))

    def testLimitCompute1(self):
        t = 'LIM {x -> oo}. (x+3) / sqrt(9*x*x - 5 * x)'
        res = "1/3"
        t0 = expr.parser.parse_expr(t)
        # print("t0 =",t0)
        t1 = rules.OnLocation(rules.RootFractionReWrite(), '0').eval(t0);
        # print("t1 =", t1)
        t2 = rules.LimFunExchange().eval(t1)
        # print("t2 =", t2)
        t3 = rules.OnLocation(rules.LHopital(), '0').eval(t2);
        # print("t3 =", t3)
        t4 = rules.OnLocation(rules.LHopital(), '0').eval(t3);
        # print("t4 =", t4)
        t5 = rules.OnLocation(rules.LimitSimplify(), '0').eval(t4);
        # print("t5 =", t5)
        t6 = rules.FullSimplify().eval(t5)
        # print("t6 =", t6)

    def testLimitCompute2(self):
        t = 'LIM {x -> -oo}. (x+3) / sqrt(9*x*x - 5 * x)'
        res = "-1/3"
        t0 = expr.parser.parse_expr(t)
        sub = expr.parser.parse_expr("x/sqrt(9*x*x-5*x) + 3/sqrt(9*x*x - 5*x)")
        t1 = rules.OnLocation(rules.Equation(sub), '0').eval(t0)
        # print("t1 =",t1)
        t2 = rules.LimSep().eval(t1)
        t3 = rules.OnLocation(rules.LimitSimplify(), '1').eval(t2)
        #print(t3)
        t4 = rules.OnLocation(rules.ExtractFromRoot('3*x', -1), '0.0.1').eval(t3);
        sub = '(x/(-(3*x))) * (1/sqrt((9 * x * x - 5 * x) / (3 * x) ^ 2))'
        sub = expr.parser.parse_expr(sub)
        t5 = rules.OnLocation(rules.Equation(sub), '0.0').eval(t4)
        t6 = rules.OnLocation(rules.LimSep(), '0').eval(t5)
        t7 = rules.OnLocation(rules.Simplify(), '0.1.0').eval(t6)
        print("t7 =", t7)
        t8 = rules.OnLocation(rules.LimitSimplify(), '0.0').eval(t7)
        # print("t8 =", t8)
        t9 = rules.OnLocation(rules.LimitSimplify(), '0.1').eval(t8)
        # print("t9 =", t9)
        t10 = rules.OnLocation(rules.LHopital(), '0.0').eval(t9)
        # print("t10 =", t10)
        t11 = rules.OnLocation(rules.LimitSimplify(), '0.0').eval(t10)
        # print("t11 =", t11)
        t12 = rules.Simplify().eval(t11)
        self.assertEqual(str(t12),res)

    def testExtractFromRoot(self):
        test_data = [
            ('sqrt(9*x*x - 5 * x)', '3*x', -1, "-(3 * x) * sqrt((9 * x * x - 5 * x) / (3 * x) ^ 2)")
        ]
        for a, b, c, d in test_data:
            a = parser.parse_expr(a)
            e = rules.ExtractFromRoot(b, c).eval(a)
            self.assertEqual(str(e), d)

    def testLimitSimplify(self):
        test_data = [
            ("LIM {x -> 3}. (5*x*x-8*x-13)/(x*x-5)", "2"),
            # ("LIM {x -> 2}. (3*x*x-x-10)/(x*x-4)", "11/4"), #LHopital
            # ("LIM {x -> 3}. (x^4-81)/(2*x*x-5*x-3)", "108/7"), #LHopital
            #("LIM {x -> -2}. ((1/x)+(1/2))/(x^3+8)", "-1/48"), #LHopital
            #("LIM {x -> 4}. (3-sqrt(x+5))/(x-4)", "-1/6"), # rewrite
            # ("LIM {x->27}. (x-27) / (x^(1/3)-3)", "27"),
            # ("LIM {x->1}. (x^(1/3) - 1) / (x^(1/4)-1)", "4/3"),
            # ("LIM {x->0}. sin(5*x) / (3*x)", "5/3"),
            # ("LIM {x->0}. (cos(2*x) - 1) / (cos(x) - 1)", "4"),
            # ("LIM {x->1}. (x^(1/3) - 1) / (x^(1/4)-1)", "4/3"),
            # ("LIM {x->0}. sin(5*x) / (3*x)", "5/3"),
            # ("LIM {x->0}. (cos(2*x) - 1) / (cos(x) - 1)", "4"),
            # ("LIM {t -> oo}. (-1/t) + 1","1"),
            # ('LIM {x -> oo}. 100 / (x^2+5)',"0"),
            # ('LIM {x -> -oo}. 7 / (x^3 - 20)',"0"),
            # ('LIM {x -> oo}. 3*x^3 - 1000*x^2',"oo"),
            # ('LIM {x -> -oo}. x^4 + 5*x^2 + 1',"oo"),
            # ('LIM {x -> oo}. x^5 - x^2 + x - 10',"oo"),
            # ('LIM {x -> -oo}. (x+7) / (3*x+5)',"1/3"),
            # ('LIM {x -> oo}. (7*x*x + x - 100) / (2*x^2 - 5 *x)',"7/2"),
            # ("LIM {x -> oo}. (x^2 - 3*x + 7)/(x^3 + 10*x - 4)","0"),
            # ('LIM {x -> -oo}. (7 * x * x - x + 11) / (4 - x)',"oo"),
            # ('LIM {x -> oo}. sqrt(x^3 + 7*x)',"oo"),
            # ('LIM {x -> oo}. log((x^6-500)/(x^6+500))',"0"),
            # ('LIM {x -> -oo}. cos(x/(x^2+10) + pi/3)',"1/2"),
            # ('LIM {x -> -oo}. (x+3) / sqrt(9*x*x - 5 * x)',"-1/3"),  # 分子变成 sqrt((x+3)^2)
            # ('LIM {x -> oo}. (x+3) / sqrt(9*x*x - 5 * x)',"1/3"),
            # ("LIM {x -> oo}. sin(x)","sin(oo)"),
            # ('LIM {x -> oo}. x - sqrt(x*x + 7)',"0"),  # 待解决 分子分母同乘 x + sqrt(x*x + 7)
            # ('LIM {x -> -oo}. x - sqrt(x*x + 7)',"-oo"),  # 待解决 分子分母同乘 x + sqrt(x*x + 7)
            # ('LIM {x -> -oo}. exp(x) / (4+5*exp(3*x))',"0"),
            # # ("LIM {x->0}. (x^3 - 7*x) / (x^3)"),  #极限不存在
            # # ("LIM {x->1}. (x^3 - 7*x) / (x-1)^2"), #极限不存在
            # # ("LIM {x-> (pi/2) }. tan(2*x) / (x - pi / 2)"),
            # # ('LIM {x -> oo}. 5^x / (3^x + 2^x)'),
            # ("LIM {x -> oo}. (5/3)^x / (1 + (2/3)^x)","oo"),
            # # ('LIM {x -> oo}. (3^x + 3^(2*x))^(1/x)'),
            # ('LIM {x -> oo}. 9*((1/3)^x + 1)^(1/x)',"9"),
            # ('LIM {x -> 0}. sin(x) / x',"1"),  # 特殊极限
            # ('LIM {x -> 0}. x / sin(x)',"1"),
            # ('LIM {x -> oo}. (1+(1/x))^x',"exp(1)"),
            # ('LIM {x -> oo}. ((1/x)+1)^x',"exp(1)"),
            # ('LIM {x -> oo}. (1+x^(-1))^x',"exp(1)"),
            # ('LIM {x -> oo}. (x^(-1)+1)^x', "exp(1)"),
            # ("LIM {x -> 5}. 7","7"),
            # ("LIM {x -> 10}. (3*x+5)", '35'),
            # ("LIM {x -> (-3/2)}. (1-4*x)", '7'),
            # ("LIM {x -> 1}. (x^2 + 3)", '4'),
            # ("LIM {x -> (-1)}. (x^2+3)", '4'),
            # ("LIM {x -> 2}. (3*x*x-x)", '10'),
            # ("LIM {x -> 3}. 2/(x+3)", '1/3'),
            # ("LIM {x -> -6}. (x+4)/(2-x)", '-1/4'),
            # ("LIM {x -> 3}. x/(4*x-9)", '1'),
            # ("LIM {x -> -6}. (x+4) / (2-x)", '-1/4'),
            # ("LIM {x -> 3}. x / (4*x-9)", '1'),
            # ("LIM {x -> 9}. (2+sqrt(x))", '5'),
            # ("LIM {x->1}. (x*x-1)/(x*x+3*x-4)", "2/5"),
            # ("LIM {x->4}. (x-4)/(sqrt(x)-2)", "4"),
            # ("LIM {x->0}. sin(x) / x", "1"),
            # ("LIM {x->0}. (3^x-2^x)/(x^2-x)", "log(2) + -log(3)"),
            # # ('LIM {x -> oo}. 5^x / (3^x + 2^x)'),
            # ('LIM {x->0}. (x*tan(x))/sin(3*x)', "0"),
            # ('LIM {x->0}. (x^2*exp(x))/(tan(x))^2', "1"),
            # ('LIM {x->0}. atan(4*x)/atan(5*x)', "4/5"),
            # ('LIM {x->0}. sin(x*x)/(x*tan(x))', "1"),
            # ('LIM {x->0}. (x*x*e^x)/tan(x)^2', "1"),
            # # ('LIM {x->0}. exp(-1/x^2)/x^2'), #错误
            ('LIM {x->oo}. exp(3*x) / 5', "oo"),
            ('LIM {x->oo}. 1/(x^2+7)', "0"),
            # ('LIM {x->oo}. (x^2+3*x-10)/(7*x^2-5*x+4)', "1/7"),
            ('LIM {x->oo}. 1/(x*exp(2*x))', "0"),
            # ('LIM {x->oo}. exp(x*(log(2)-log(3)))',"0"),
            # # ('LIM {x->oo}. (exp(x)+2/x) / (exp(x)+5/x)')# 洛必达死循环
            # # ("LIM {x->oo}. sqrt(x^2+1)-sqrt(x-1)"),
            ("LIM {x->oo}. exp(-x)*sin(x)", "0"),
            # ("LIM {x-> (pi/2) }. tan(2*x) / (x - pi / 2)", "2"),
            ("LIM {x->oo}. atan(x) + exp(-x)", "1/2 * pi"),
            ("LIM {x->-oo}. atan(x) + exp(x)", "-1/2 * pi"),
            ("LIM {x->oo}. asin(x)", "asin(oo)"),
            ("LIM {x->oo}. exp(-3*x+2)*atan(3*x^2)", "0"),
            # ("LIM {t->-oo}. -1+(-t*exp(t))+exp(t)","-1"),
            ("LIM {t->oo}. atan(t) - atan(sqrt(2)/2)","1/2 * pi + -atan(sqrt(2) / 2)"),
            ("LIM {x -> -oo}. (1 + -5/9 * x ^ -1) ^ (-1/2)","1")
        ]

        for a, b in test_data:
            a = parser.parse_expr(a)
            e = rules.LimitSimplify().eval(a)
            # print(e)
            if e.ty != expr.LIMIT:
                self.assertEqual(str(e.normalize()), b, a)
            else:
                print(e)

    def testComputeLimitConds(self):
        test_data = [
            ("b * oo", "b > 0", "oo"),
            ("b * oo", "b < 0", "-oo"),
            ("b ^ (-1/2) * oo", "b > 0", "oo"),
            ("atan(b ^ (-1/2) * oo)", "b > 0", "1/2 * pi"),
        ]

        for e, cond, res in test_data:
            e = parser.parse_expr(e)
            res = parser.parse_expr(res)
            conds = conditions.Conditions()
            conds.add_condition("1", parser.parse_expr(cond))
            self.assertEqual(rules.compute_limit(e, conds)[0], res)

    def testWallis(self):
        # Overall goal
        goal = parser.parse_expr("(INT x:[0,oo]. 1/(x^2+1)^(m+1)) = pi/(2^(2*m+1))*binom(2*m,m)")

        # Initial state
        st = compstate.State(goal)

        # Make definition
        Idef = compstate.FuncDef(parser.parse_expr("I(m,b) = (INT x:[0,oo]. 1/(x^2+b)^(m+1))"))
        st.add_item(Idef)

        # Condition b > 0
        conds = conditions.Conditions()
        conds.add_condition("b", parser.parse_expr("b > 0"))

        # Prove the following equality
        Eq1 = compstate.Identity(parser.parse_expr("(D b. I(m,b)) = -(m+1) * I(m+1, b)"))
        st.add_item(Eq1)

        Eq1_proof = compstate.CalculationProof(Eq1.eq, conds=conds)
        st.add_item(Eq1_proof)

        calc = Eq1_proof.lhs_calc
        calc.perform_rule(rules.OnLocation(rules.ExpandDefinition(Idef.eq), "0"))
        calc.perform_rule(rules.DerivIntExchange())
        calc.perform_rule(rules.OnLocation(rules.DerivativeSimplify(), "0"))
        calc.perform_rule(rules.FullSimplify())

        calc = Eq1_proof.rhs_calc
        calc.perform_rule(rules.OnLocation(rules.ExpandDefinition(Idef.eq), "1"))
        calc.perform_rule(rules.FullSimplify())

        # Prove the following by induction
        Eq2 = compstate.Identity(parser.parse_expr("I(m,b) = pi / 2^(2*m+1) * binom(2*m, m) * (1/(b^((2*m+1)/2)))"))
        st.add_item(Eq2)

        Eq2_proof = compstate.InductionProof(Eq2.eq, "m", conds=conds)
        st.add_item(Eq2_proof)

        # Base case
        calc = Eq2_proof.base_case.lhs_calc
        calc.perform_rule(rules.ExpandDefinition(Idef.eq))
        calc.perform_rule(rules.ElimInfInterval())
        calc.perform_rule(rules.OnLocation(rules.Substitution2("u", parser.parse_expr("sqrt(b) * u")), "0"))
        calc.perform_rule(rules.OnLocation(rules.FullSimplify(), "0"))
        calc.perform_rule(rules.OnLocation(rules.Equation(parser.parse_expr("b^-1 * (1 + u^2)^-1")), "0.1.0"))
        calc.perform_rule(rules.OnLocation(rules.FullSimplify(), "0"))
        calc.perform_rule(rules.LimitSimplify())
        calc.perform_rule(rules.FullSimplify())

        # Induction case, LHS
        calc = Eq2_proof.induct_case.lhs_calc
        calc.perform_rule(rules.ApplyEquation(Eq1.eq))
        calc.perform_rule(rules.OnLocation(rules.ApplyEquation(Eq2.eq), "0.0"))
        calc.perform_rule(rules.OnLocation(rules.DerivativeSimplify(), "0"))
        calc.perform_rule(rules.FullSimplify())

        # Induction step, RHS
        calc = Eq2_proof.induct_case.rhs_calc
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.OnLocation(rules.RewriteBinom(), "1"))
        calc.perform_rule(rules.FullSimplify())
        print(st)

    def testMul2Div(self):
        test_data = [("x*(e^-x)", "", 1, "x / (1 / e ^ -x)"),
                     ('1 + (x*y + t*log(t))/5', "1.0.1", 1, "1 + (x * y + t / (1 / log(t))) / 5"),
                     ('1 + (x*y + t*log(t))/5', "1.0.0", 0, "1 + (y / (1 / x) + t * log(t)) / 5"), ]
        for s, mulExprLoc, multiplierLoc, res in test_data:
            loc = expr.Location(mulExprLoc)
            r = rules.Mul2Div(multiplierLoc)
            res2 = rules.OnLocation(r, loc).eval(expr.parser.parse_expr(s))
            self.assertEqual(str(res2), res)

    def testNumeratorDeominatorMulExpr(self):
        test_data = [("sqrt(a) + sqrt(b)", "", "sqrt(a)-sqrt(b)", \
                      "((sqrt(a) + sqrt(b)) * (sqrt(a) - sqrt(b))) / (sqrt(a) - sqrt(b))"),
                     ('3/2 + 1/(sqrt(x^2-2) + sqrt(x^2-1))', '1', 'sqrt(x^2-2) - sqrt(x^2-1)',
                      '3/2 + ((1 / (sqrt(x ^ 2 - 2) + sqrt(x ^ 2 - 1))) * (sqrt(x ^ 2 - 2) - sqrt(x ^ 2 - 1))) / (sqrt(x ^ 2 - 2) - sqrt(x ^ 2 - 1))'),
                     ('x - sqrt(x*x + 7)', '', 'x + sqrt(x*x + 7)',\
                      '((x - sqrt(x * x + 7)) * (x + sqrt(x * x + 7))) / (x + sqrt(x * x + 7))'),
                     ('sqrt(a) / b', '', 'sqrt(a)', '((sqrt(a) / b) * sqrt(a)) / sqrt(a)'),
                     ]
        for s, loc, u, res2 in test_data:
            s = expr.parser.parse_expr(s)
            u = expr.parser.parse_expr(u)
            loc = expr.Location(loc)
            res1 = rules.OnLocation(rules.NumeratorDeominatorMulExpr(u), loc).eval(s)
            self.assertEqual(str(res1), res2)

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


if __name__ == "__main__":
    unittest.main()
