"""Overall test for integrals."""

import unittest
import json

from integral import expr
from logic import basic
from integral import compstate
from integral import rules
from integral import parser
from integral import conditions


class IntegralTest(unittest.TestCase):
    def testInteresting(self):
        file = compstate.CompFile("Interesting")

        # Problem (2.2.a)
        calc = file.add_calculation("INT x:[0,pi/2]. sqrt(sin(x)) / (sqrt(sin(x)) + sqrt(cos(x)))")
        calc.perform_rule(rules.Substitution("y", parser.parse_expr("pi / 2 - x")))
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.Equation(parser.parse_expr("1 - sqrt(sin(y)) / (sqrt(cos(y)) + sqrt(sin(y)))"),
                                         old_expr=parser.parse_expr("sqrt(cos(y)) * (sqrt(cos(y)) + sqrt(sin(y)))^-1")))
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.IntegrateByEquation(parser.parse_expr("INT x:[0,pi/2]. sqrt(sin(x)) / (sqrt(sin(x)) + sqrt(cos(x)))")))
        self.assertEqual(str(calc.last_expr), "1/4 * pi")

        # Problem (2.2.b)
        calc = file.add_calculation("INT x:[0,pi]. x * sin(x) / (1 + cos(x)^2)")
        calc.perform_rule(rules.Substitution("y", parser.parse_expr("pi - x")))
        calc.perform_rule(rules.ExpandPolynomial())
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.IntegrateByEquation(parser.parse_expr("INT x:[0,pi]. x * sin(x) / (1 + cos(x)^2)")))
        calc.perform_rule(rules.Substitution("u", parser.parse_expr("cos(y)")))
        calc.perform_rule(rules.FullSimplify())
        self.assertEqual(str(calc.last_expr), "1/4 * pi ^ 2")

        # Test parsing of json file
        json_file = file.export()
        for i, item in enumerate(json_file['content']):
            self.assertEqual(compstate.parse_item(item).export(), file.content[i].export())

        with open('integral/examples/interesting.json', 'w', encoding='utf-8') as f:
            json.dump(file.export(), f, indent=4, ensure_ascii=False, sort_keys=True)

    def testTongji(self):
        basic.load_theory('interval_arith')

        file = compstate.CompFile("Tongji")

        calc = file.add_calculation("INT x:[2,3]. 2 * x + x ^ 2")
        calc.perform_rule(rules.FullSimplify())
        self.assertEqual(str(calc.last_expr), "34/3")

        calc = file.add_calculation("INT x:[0,1]. (3 * x + 1) ^ (-2)")
        calc.perform_rule(rules.Substitution("u", parser.parse_expr("3 * x + 1")))
        calc.perform_rule(rules.FullSimplify())
        self.assertEqual(str(calc.last_expr), "1/4")

        calc = file.add_calculation("INT x:[0,1]. exp(6 * x)")
        calc.perform_rule(rules.Substitution("u", parser.parse_expr("6 * x")))
        calc.perform_rule(rules.FullSimplify())
        self.assertEqual(str(calc.last_expr), "1/6 * exp(6) - 1/6")

        calc = file.add_calculation("INT x:[-1,2]. x * exp(x)")
        calc.perform_rule(rules.IntegrationByParts(parser.parse_expr("x"), parser.parse_expr("exp(x)")))
        calc.perform_rule(rules.FullSimplify())
        self.assertEqual(str(calc.last_expr), "2 * exp(-1) + exp(2)")

        calc = file.add_calculation("INT x:[0,pi/4]. sin(x)")
        calc.perform_rule(rules.FullSimplify())
        self.assertEqual(str(calc.last_expr), "-1/2 * sqrt(2) + 1")

        calc = file.add_calculation("INT x:[0,1]. 3*x^2 - x + 1")
        calc.perform_rule(rules.FullSimplify())
        self.assertEqual(str(calc.last_expr), "3/2")

        calc = file.add_calculation("INT x:[1,2]. x^2 + 1/x^4")
        calc.perform_rule(rules.FullSimplify())
        self.assertEqual(str(calc.last_expr), "21/8")

        calc = file.add_calculation("INT x:[pi/3, pi]. sin(2*x + pi/3)")
        calc.perform_rule(rules.Substitution("u", parser.parse_expr("2*x + pi/3")))
        calc.perform_rule(rules.FullSimplify())
        self.assertEqual(str(calc.last_expr), "-3/4")

        calc = file.add_calculation("INT x:[4, 9]. x ^ (1 / 3) * (x ^ (1 / 2) + 1)")
        calc.perform_rule(rules.ExpandPolynomial())
        calc.perform_rule(rules.FullSimplify())
        self.assertEqual(str(calc.last_expr), "-81/11 * 2 ^ (2/3) + 945/44 * 3 ^ (2/3)")

        calc = file.add_calculation("INT x:[-1, 0]. (3 * x ^ 4 + 3 * x ^ 2 + 1) / (x ^ 2 + 1)")
        calc.perform_rule(rules.PolynomialDivision())
        calc.perform_rule(rules.FullSimplify())
        self.assertEqual(str(calc.last_expr), "1/4 * pi + 1")

        calc = file.add_calculation("INT x:[4, exp(1) + 3]. (x ^ 3 - 12 * x ^ 2 - 42) / (x - 3)")
        calc.perform_rule(rules.PolynomialDivision())
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.Substitution("u", parser.parse_expr("x - 3")))
        calc.perform_rule(rules.FullSimplify())
        self.assertEqual(str(calc.last_expr), "-45 * exp(1) - 3/2 * exp(2) + 1/3 * exp(3) - 461/6")

        calc = file.add_calculation("INT x:[0, pi / 2]. sin(x) * cos(x) ^ 3")
        calc.perform_rule(rules.Substitution("u", parser.parse_expr("cos(x)")))
        calc.perform_rule(rules.FullSimplify())
        self.assertEqual(str(calc.last_expr), "1/4")

        calc = file.add_calculation("INT x:[0, pi]. (1 - sin(x)^3)")
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.Equation(parser.parse_expr("sin(x) * sin(x)^2"),
                                         old_expr=parser.parse_expr("sin(x)^3")))
        calc.perform_rule(rules.RewriteTrigonometric("TR5", rewrite_term=parser.parse_expr("sin(x)^2")))
        calc.perform_rule(rules.Substitution("u", parser.parse_expr("cos(x)")))
        calc.perform_rule(rules.FullSimplify())
        self.assertEqual(str(calc.last_expr), "pi - 4/3")

        calc = file.add_calculation("INT x:[pi/6, pi/2]. cos(x) ^ 2")
        calc.perform_rule(rules.RewriteTrigonometric("TR7", rewrite_term=parser.parse_expr("cos(x)^2")))
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.Substitution("u", parser.parse_expr("2 * x")))
        calc.perform_rule(rules.FullSimplify())
        self.assertEqual(str(calc.last_expr), "-1/8 * sqrt(3) + 1/6 * pi")

        calc = file.add_calculation("INT x:[0, 1]. (1 - x^2) ^ (1/2)")
        calc.perform_rule(rules.SubstitutionInverse("u", parser.parse_expr("sin(u)")))
        calc.perform_rule(rules.RewriteTrigonometric("TR5", rewrite_term=parser.parse_expr("1-sin(u)^2")))
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.ElimAbs())
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.RewriteTrigonometric("TR7", rewrite_term=parser.parse_expr("cos(u)^2")))
        calc.perform_rule(rules.Substitution("v", parser.parse_expr("2 * u")))
        calc.perform_rule(rules.FullSimplify())
        self.assertEqual(str(calc.last_expr), "1/4 * pi")

        calc = file.add_calculation("INT x:[0, sqrt(2)]. sqrt(2 - x^2)")
        calc.perform_rule(rules.SubstitutionInverse("u", parser.parse_expr("sqrt(2) * sin(u)")))
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.RewriteTrigonometric("TR5", rewrite_term=parser.parse_expr("-2*sin(u)^2+2")))
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.ElimAbs())
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.RewriteTrigonometric("TR7", rewrite_term=parser.parse_expr("cos(u)^2")))
        calc.perform_rule(rules.Substitution("v", parser.parse_expr("2 * u")))
        calc.perform_rule(rules.FullSimplify())
        self.assertEqual(str(calc.last_expr), "1/2 * pi")

        calc = file.add_calculation("INT y:[-sqrt(2), sqrt(2)]. sqrt(8 - 2*y^2)")
        calc.perform_rule(rules.SubstitutionInverse("u", parser.parse_expr("2 * sin(u)")))
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.RewriteTrigonometric("TR5", rewrite_term=parser.parse_expr("-8*sin(u)^2+8")))
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.ElimAbs())
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.RewriteTrigonometric("TR7", rewrite_term=parser.parse_expr("cos(u)^2")))
        calc.perform_rule(rules.Substitution("v", parser.parse_expr("2 * u")))
        calc.perform_rule(rules.FullSimplify())
        self.assertEqual(str(calc.last_expr), "sqrt(2) * pi + 2 * sqrt(2)")

        calc = file.add_calculation("INT x:[1/sqrt(2), 1]. sqrt(1 - x^2) / x ^ 2")
        calc.perform_rule(rules.SubstitutionInverse("u", parser.parse_expr("sin(u)")))
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.RewriteTrigonometric("TR5", parser.parse_expr("-sin(u)^2+1")))
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.ElimAbs())
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.RewriteTrigonometric("TR6", parser.parse_expr("cos(u)^2")))
        calc.perform_rule(rules.ExpandPolynomial())
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.RewriteTrigonometric("TR111", parser.parse_expr("sin(u)^(-2)")))
        calc.perform_rule(rules.FullSimplify())
        self.assertEqual(str(calc.last_expr), "-1/4 * pi + 1")

        calc = file.add_calculation("INT x:[-1, 1]. x / sqrt(5 - 4 * x)")
        calc.perform_rule(rules.Substitution("u", parser.parse_expr("5 - 4 * x")))
        calc.perform_rule(rules.ExpandPolynomial())
        calc.perform_rule(rules.FullSimplify())
        self.assertEqual(str(calc.last_expr), "1/6")

        calc = file.add_calculation("INT x:[1,4]. 1 / (1 + sqrt(x))")
        calc.perform_rule(rules.Substitution("u", parser.parse_expr("sqrt(x)")))
        calc.perform_rule(rules.Substitution("v", parser.parse_expr("u + 1")))
        calc.perform_rule(rules.ExpandPolynomial())
        calc.perform_rule(rules.FullSimplify())
        self.assertEqual(str(calc.last_expr), "2 * log(2) - 2 * log(3) + 2")

        calc = file.add_calculation("INT x:[3/4, 1]. 1 / (sqrt(1-x) - 1)")
        calc.perform_rule(rules.Substitution("u", parser.parse_expr("sqrt(1 - x)")))
        calc.perform_rule(rules.Substitution("v", parser.parse_expr("u - 1")))
        calc.perform_rule(rules.ExpandPolynomial())
        calc.perform_rule(rules.FullSimplify())
        self.assertEqual(str(calc.last_expr), "-2 * log(2) + 1")

        calc = file.add_calculation("INT t:[0, 1]. t * exp(-t ^ 2 / 2)")
        calc.perform_rule(rules.Substitution("u", parser.parse_expr("-t ^ 2 / 2")))
        calc.perform_rule(rules.FullSimplify())
        self.assertEqual(str(calc.last_expr), "-exp(-1/2) + 1")

        calc = file.add_calculation("INT x:[1, exp(2)]. 1 / (x*sqrt(1+log(x)))")
        calc.perform_rule(rules.Substitution("u", parser.parse_expr("1 + log(x)")))
        calc.perform_rule(rules.FullSimplify())
        self.assertEqual(str(calc.last_expr), "2 * sqrt(3) - 2")

        calc = file.add_calculation("INT x:[-2, 0]. (x + 2)/(x^2 + 2*x + 2)")
        calc.perform_rule(rules.Equation(parser.parse_expr("(x + 1) ^ 2 + 1"),
                                         old_expr=parser.parse_expr("x^2 + 2*x + 2")))
        calc.perform_rule(rules.Substitution("u", parser.parse_expr("x + 1")))
        calc.perform_rule(rules.ExpandPolynomial())
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.SplitRegion(parser.parse_expr("0")))
        calc.perform_rule(rules.Substitution("v", parser.parse_expr("u ^ 2 + 1")))
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.Substitution("v", parser.parse_expr("u ^ 2 + 1")))
        calc.perform_rule(rules.FullSimplify())
        self.assertEqual(str(calc.last_expr), "1/2 * pi")

        calc = file.add_calculation("INT x:[-pi/2,pi/2]. cos(x)^4")
        calc.perform_rule(rules.Equation(parser.parse_expr("(cos(x)^2)^2"), old_expr=parser.parse_expr("cos(x)^4")))
        calc.perform_rule(rules.RewriteTrigonometric("TR7", rewrite_term=parser.parse_expr("cos(x)^2")))
        calc.perform_rule(rules.ExpandPolynomial())
        calc.perform_rule(rules.Substitution("u", parser.parse_expr("2 * x")))
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.RewriteTrigonometric("TR7", rewrite_term=parser.parse_expr("cos(u)^2")))
        calc.perform_rule(rules.Substitution("v", parser.parse_expr("2 * u")))
        calc.perform_rule(rules.FullSimplify())
        self.assertEqual(str(calc.last_expr), "3/8 * pi")

        calc = file.add_calculation("INT x:[-pi/2, pi/2]. sqrt(cos(x) - cos(x)^3)")
        calc.perform_rule(rules.Equation(parser.parse_expr("cos(x) * (1 - cos(x)^2)"),
                                         old_expr=parser.parse_expr("cos(x) - cos(x)^3")))
        calc.perform_rule(rules.RewriteTrigonometric("TR6", rewrite_term=parser.parse_expr("1 - cos(x)^2")))
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.ElimAbs())
        calc.perform_rule(rules.Substitution("u", parser.parse_expr("cos(x)")))
        calc.perform_rule(rules.FullSimplify())
        self.assertEqual(str(calc.last_expr), "4/3")

        calc = file.add_calculation("INT x:[0, pi]. sqrt(1 + cos(2*x))")
        calc.perform_rule(rules.RewriteTrigonometric("TR11", parser.parse_expr("cos(2*x)")))
        calc.perform_rule(rules.RewriteTrigonometric("TR5", parser.parse_expr("-(sin(x) ^ 2)")))
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.ElimAbs())
        calc.perform_rule(rules.FullSimplify())
        self.assertEqual(str(calc.last_expr), "2 * sqrt(2)")

        calc = file.add_calculation("INT x:[0, 1].x * exp(-x)")
        calc.perform_rule(rules.IntegrationByParts(parser.parse_expr("x"), parser.parse_expr("-exp(-x)")))
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.Substitution("u", parser.parse_expr("-x")))
        calc.perform_rule(rules.FullSimplify())
        self.assertEqual(str(calc.last_expr), "-2 * exp(-1) + 1")

        calc = file.add_calculation("INT x:[1, exp(1)]. x * log(x)")
        calc.perform_rule(rules.IntegrationByParts(parser.parse_expr("log(x)/2"), parser.parse_expr("x^2")))
        calc.perform_rule(rules.FullSimplify())
        self.assertEqual(str(calc.last_expr), "1/4 * exp(2) + 1/4")

        calc = file.add_calculation("INT x:[pi/4, pi/3]. x / sin(x)^2")
        calc.perform_rule(rules.RewriteTrigonometric("TR111", rewrite_term=parser.parse_expr("x / sin(x)^2")))
        calc.perform_rule(rules.IntegrationByParts(parser.parse_expr("x"), parser.parse_expr("-cot(x)")))
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.RewriteTrigonometric("TR2", rewrite_term=parser.parse_expr("cot(x)")))
        calc.perform_rule(rules.Substitution("u", parser.parse_expr("sin(x)")))
        calc.perform_rule(rules.FullSimplify())
        self.assertEqual(str(calc.last_expr), "-1/9 * sqrt(3) * pi - 1/2 * log(2) + 1/2 * log(3) + 1/4 * pi")

        calc = file.add_calculation("INT x:[1, 4]. log(x) / sqrt(x)")
        calc.perform_rule(rules.IntegrationByParts(parser.parse_expr("2*log(x)"), parser.parse_expr("sqrt(x)")))
        calc.perform_rule(rules.FullSimplify())
        self.assertEqual(str(calc.last_expr), "8 * log(2) - 4")

        calc = file.add_calculation("INT x:[0, 1]. x * atan(x)")
        calc.perform_rule(rules.IntegrationByParts(parser.parse_expr("atan(x)/2"), parser.parse_expr("x^2")))
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.PolynomialDivision())
        calc.perform_rule(rules.FullSimplify())
        self.assertEqual(str(calc.last_expr), "1/4 * pi - 1/2")

        calc = file.add_calculation(parser.parse_expr("INT x:[0, pi/2]. exp(2*x)*cos(x)"))
        calc.perform_rule(rules.IntegrationByParts(parser.parse_expr("exp(2*x)"), parser.parse_expr("sin(x)")))
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.IntegrationByParts(parser.parse_expr("exp(2*x)"), parser.parse_expr("-cos(x)")))
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.IntegrateByEquation(parser.parse_expr("INT x:[0, pi/2]. exp(2*x)*cos(x)")))
        self.assertEqual(str(calc.last_expr), "1/5 * exp(pi) - 2/5")

        calc = file.add_calculation(parser.parse_expr("INT x:[0,pi]. (x * sin(x))^2"))
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.RewriteTrigonometric("TR8", rewrite_term=parser.parse_expr("sin(x)^2")))
        calc.perform_rule(rules.ExpandPolynomial())
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.IntegrationByParts(parser.parse_expr("x^2/2"), parser.parse_expr("sin(2*x)")))
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.IntegrationByParts(parser.parse_expr("x/2"), parser.parse_expr("-cos(2*x)")))
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.Substitution("u", parser.parse_expr("2 * x")))
        calc.perform_rule(rules.FullSimplify())
        self.assertEqual(str(calc.last_expr), "1/6 * pi ^ 3 - 1/4 * pi")

        calc = file.add_calculation(parser.parse_expr("INT x:[1, exp(1)]. sin(log(x))"))
        calc.perform_rule(rules.Substitution("u", parser.parse_expr("log(x)")))
        calc.perform_rule(rules.IntegrationByParts(parser.parse_expr("-exp(u)"), parser.parse_expr("cos(u)")))
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.IntegrationByParts(parser.parse_expr("exp(u)"), parser.parse_expr("sin(u)")))
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.IntegrateByEquation(parser.parse_expr("INT u:[0,1]. exp(u) * sin(u)")))
        self.assertEqual(str(calc.last_expr), "-1/2 * cos(1) * exp(1) + 1/2 * exp(1) * sin(1) + 1/2")

        calc = file.add_calculation("INT x:[1/exp(1), exp(1)]. abs(log(x))")
        calc.perform_rule(rules.ElimAbs())
        calc.perform_rule(rules.IntegrationByParts(parser.parse_expr("log(x)"), parser.parse_expr("x")))
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.IntegrationByParts(parser.parse_expr("log(x)"), parser.parse_expr("x")))
        calc.perform_rule(rules.FullSimplify())
        self.assertEqual(str(calc.last_expr), "-2 * exp(-1) + 2")

        # Test parsing of json file
        json_file = file.export()
        for i, item in enumerate(json_file['content']):
            self.assertEqual(compstate.parse_item(item).export(), file.content[i].export())

        with open('integral/examples/tongji7.json', 'w', encoding='utf-8') as f:
            json.dump(file.export(), f, indent=4, ensure_ascii=False, sort_keys=True)

    def testLHopital(self):
        file = compstate.CompFile("LHopital")

        calc = file.add_calculation("LIM {x -> 1}. (x^2 - 1) / (x^2 + 3*x - 4)")
        calc.perform_rule(rules.LHopital())
        calc.perform_rule(rules.FullSimplify())
        self.assertEqual(str(calc.last_expr), "2/5")

        calc = file.add_calculation("LIM {x -> 4}. (x - 4) / (sqrt(x) - 2)")
        calc.perform_rule(rules.LHopital())
        calc.perform_rule(rules.FullSimplify())
        self.assertEqual(str(calc.last_expr), "4")

        calc = file.add_calculation("LIM {x -> 0}. sin(x) / x")
        calc.perform_rule(rules.LHopital())
        calc.perform_rule(rules.FullSimplify())
        self.assertEqual(str(calc.last_expr), "1")

        calc = file.add_calculation("LIM {x -> 0}. (3^x - 2^x) / (x^2 - x)")
        calc.perform_rule(rules.LHopital())
        calc.perform_rule(rules.FullSimplify())
        self.assertEqual(str(calc.last_expr), "log(2) - log(3)")

        calc = file.add_calculation("LIM {x -> 3}. (1/x - 1/3) / (x^2 - 9)")
        calc.perform_rule(rules.LHopital())
        calc.perform_rule(rules.FullSimplify())
        self.assertEqual(str(calc.last_expr), "-1/54")

        calc = file.add_calculation("LIM {x -> 0}. x * tan(x) / sin(3*x)")
        calc.perform_rule(rules.LHopital())
        calc.perform_rule(rules.FullSimplify())
        self.assertEqual(str(calc.last_expr), "0")

        # Test parsing of json file
        json_file = file.export()
        for i, item in enumerate(json_file['content']):
            self.assertEqual(compstate.parse_item(item).export(), file.content[i].export())

        with open('integral/examples/UCDAVIS/LHopital.json', 'w', encoding='utf-8') as f:
            json.dump(file.export(), f, indent=4, ensure_ascii=False, sort_keys=True)

    def testWallis(self):
        file = compstate.CompFile('Wallis')

        # Condition b > 0
        conds = conditions.Conditions()
        conds.add_condition("b", parser.parse_expr("b > 0"))

        # Make definition
        Idef = compstate.FuncDef(parser.parse_expr("I(m,b) = (INT x:[0,oo]. 1/(x^2+b)^(m+1))"), conds=conds)
        file.add_definition(Idef)

        # Prove the following equality
        Eq1 = compstate.Goal(parser.parse_expr("(D b. I(m,b)) = -(m+1) * I(m+1, b)"), conds=conds)
        file.add_compstate(Eq1)
        proof = Eq1.proof_by_calculation()

        calc = proof.lhs_calc
        calc.perform_rule(rules.OnSubterm(rules.ExpandDefinition(Idef.eq)))
        calc.perform_rule(rules.DerivIntExchange())

        calc.perform_rule(rules.FullSimplify())

        calc = proof.rhs_calc
        calc.perform_rule(rules.OnSubterm(rules.ExpandDefinition(Idef.eq)))
        calc.perform_rule(rules.FullSimplify())

        # Prove the following by induction
        Eq2 = compstate.Goal(parser.parse_expr("I(m,b) = pi / 2^(2*m+1) * binom(2*m, m) * (1/(b^((2*m+1)/2)))"), conds=conds)
        file.add_compstate(Eq2)
        proof = Eq2.proof_by_induction("m")
        proof_base = proof.base_case.proof_by_calculation()
        proof_induct = proof.induct_case.proof_by_calculation()

        # Base case
        calc = proof_base.lhs_calc
        calc.perform_rule(rules.ExpandDefinition(Idef.eq))
        calc.perform_rule(rules.ElimInfInterval())
        calc.perform_rule(rules.SubstitutionInverse("u", parser.parse_expr("sqrt(b) * u")))
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.Equation(parser.parse_expr("b^-1 * (1 + u^2)^-1"),
                                         old_expr=parser.parse_expr("(b * u^2 + b)^-1")))
        calc.perform_rule(rules.FullSimplify())

        # Induction case, LHS
        calc = proof_induct.lhs_calc
        calc.perform_rule(rules.ApplyEquation(Eq1.goal))
        calc.perform_rule(rules.OnSubterm(rules.ApplyEquation("IH")))
        calc.perform_rule(rules.FullSimplify())

        # Induction step, RHS
        calc = proof_induct.rhs_calc
        calc.perform_rule(rules.OnSubterm(rules.RewriteBinom()))
        calc.perform_rule(rules.FullSimplify())

        # Test parsing of json file
        json_file = file.export()
        for i, item in enumerate(json_file['content']):
            self.assertEqual(compstate.parse_item(item).export(), file.content[i].export())

        # Test goals are finished
        self.assertTrue(file.content[1].is_finished())
        self.assertTrue(file.content[2].is_finished())
        with open('integral/examples/wallis.json', 'w', encoding='utf-8') as f:
            json.dump(file.export(), f, indent=4, ensure_ascii=False, sort_keys=True)

    def testGammaBeta(self):
        file = compstate.CompFile("GammaBeta")

        # Condition n > 0
        conds = conditions.Conditions()
        conds.add_condition("n", parser.parse_expr("n > 0"))

        # Definition of Gamma function
        gamma_def = compstate.FuncDef(parser.parse_expr("Gamma(n) = (INT x:[0,oo]. exp(-x) * x^(n-1))"), conds=conds)
        file.add_definition(gamma_def)

        # Recursive equation for gamma function
        goal1 = compstate.Goal(parser.parse_expr("Gamma(n+1) = n * Gamma(n)"), conds=conds)
        file.add_compstate(goal1)

        proof = goal1.proof_by_calculation()
        calc = proof.lhs_calc
        calc.perform_rule(rules.ExpandDefinition(gamma_def.eq))
        calc.perform_rule(rules.ElimInfInterval())
        calc.perform_rule(rules.IntegrationByParts(parser.parse_expr("x^n"), parser.parse_expr("-exp(-x)")))
        calc.perform_rule(rules.FullSimplify())

        calc = proof.rhs_calc
        calc.perform_rule(rules.OnSubterm(rules.ExpandDefinition(gamma_def.eq)))
        calc.perform_rule(rules.ElimInfInterval())

        # Gamma function and factorial
        goal2 = compstate.Goal(parser.parse_expr("Gamma(n+1) = factorial(n)"))
        file.add_compstate(goal2)

        proof = goal2.proof_by_induction("n")
        proof_base = proof.base_case.proof_by_calculation()
        proof_induct = proof.induct_case.proof_by_calculation()

        calc = proof_base.lhs_calc
        calc.perform_rule(rules.ExpandDefinition(gamma_def.eq))
        calc.perform_rule(rules.ElimInfInterval())
        calc.perform_rule(rules.Substitution("u", parser.parse_expr("-x")))
        calc.perform_rule(rules.FullSimplify())

        calc = proof_induct.lhs_calc
        calc.perform_rule(rules.ApplyEquation(goal1.goal, subMap={"n": parser.parse_expr("n + 1")}))
        calc.perform_rule(rules.OnSubterm(rules.ApplyInductHyp(goal2.goal)))
        calc.perform_rule(rules.RewriteFactorial())

        # Application
        goal3 = compstate.Calculation(parser.parse_expr("INT x:[0,oo]. exp(-x^3)"))
        file.add_calculation(goal3)
        goal3.perform_rule(rules.Substitution('y', parser.parse_expr('x^3')))
        goal3.perform_rule(rules.FullSimplify())
        goal3.perform_rule(rules.OnSubterm(rules.ApplyEquation(gamma_def.eq, subMap={"n": parser.parse_expr('1/3')})))
        goal3.perform_rule(rules.ApplyEquation(goal1.goal))
        goal3.perform_rule(rules.FullSimplify())

        # Test parsing of json file
        json_file = file.export()
        for i, item in enumerate(json_file['content']):
            self.assertEqual(compstate.parse_item(item).export(), file.content[i].export())

        # Test goals are finished
        self.assertTrue(file.content[1].is_finished())
        self.assertTrue(file.content[2].is_finished())
        self.assertEqual(str(file.content[3].last_expr), "Gamma(4/3)")

        with open('integral/examples/GammaBeta.json', 'w', encoding='utf-8') as f:
            json.dump(file.export(), f, indent=4, ensure_ascii=False, sort_keys=True)

    def testEulerLogSineIntegral(self):
        # Reference:
        # Inside interesting integrals, Section 2.4
        file = compstate.CompFile("EulerLogSine")

        # Define I(a)
        e = parser.parse_expr('I(a) = INT x:[0,pi/2]. log(a * sin(x))')
        Idef1 = compstate.FuncDef(e)
        file.add_definition(Idef1)

        # Define J(a)
        e = parser.parse_expr('J(a) = INT x:[0,pi/2]. log(a * sin(2*x))')
        Idef2 = compstate.FuncDef(e)
        file.add_definition(Idef2)

        # Prove J(a) = I(a)
        e = parser.parse_expr("J(a) = I(a)")
        goal1 = compstate.Goal(e)
        file.add_compstate(goal1)

        proof = goal1.proof_by_calculation()
        calc = proof.lhs_calc
        calc.perform_rule(rules.ExpandDefinition(Idef2.eq))
        calc.perform_rule(rules.Substitution("t", parser.parse_expr("2*x")))
        calc.perform_rule(rules.SplitRegion(parser.parse_expr('pi/2')))
        calc.perform_rule(rules.OnLocation(rules.Substitution('x', parser.parse_expr('pi - t')), '1'))
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.OnLocation(rules.Substitution('x', parser.parse_expr('t')), '1'))
        calc.perform_rule(rules.FullSimplify())

        calc = proof.rhs_calc
        calc.perform_rule(rules.ExpandDefinition(Idef1.eq))

        # Prove J(a) = pi/2 * log(2/a) + 2 * I(a)
        e = parser.parse_expr("J(a) = pi/2 * log(2/a) + 2 * I(a)")
        goal2 = compstate.Goal(e)
        file.add_compstate(goal2)

        proof = goal2.proof_by_calculation()
        calc = proof.lhs_calc
        calc.perform_rule(rules.ExpandDefinition(Idef2.eq))
        calc.perform_rule(rules.RewriteTrigonometric("TR11", parser.parse_expr("sin(2*x)")))
        calc.perform_rule(rules.Equation(new_expr = parser.parse_expr("(2/a) * (a*sin(x)) * (a*cos(x))"),\
                                         old_expr = parser.parse_expr("a * (2 * sin(x) * cos(x))")))
        calc.perform_rule(rules.RewriteLog())
        calc.perform_rule(rules.RewriteLog())
        calc.perform_rule(rules.FullSimplify())

        calc.perform_rule(rules.OnLocation(rules.Substitution('t', parser.parse_expr("pi/2 - x")), '0.1'))
        calc.perform_rule(rules.OnLocation(rules.Substitution('x', parser.parse_expr("t")), '0.1'))
        calc.perform_rule(rules.FullSimplify())

        calc = proof.rhs_calc
        calc.perform_rule(rules.OnSubterm(rules.ExpandDefinition(Idef1.eq)))
        calc.perform_rule(rules.FullSimplify())

        # Finally show I(a) = pi/2 * log(a/2)
        e = parser.parse_expr("I(a) = pi/2 * log(a/2)")
        goal3 = compstate.Goal(e)
        file.add_compstate(goal3)

        proof = goal3.proof_by_calculation()
        calc = proof.lhs_calc
        calc.perform_rule(rules.ApplyEquation(goal1.goal))
        calc.perform_rule(rules.ApplyEquation(goal2.goal))
        calc.perform_rule(rules.IntegrateByEquation(parser.parse_expr("I(a)")))
        calc.perform_rule(rules.RewriteLog())
        calc.perform_rule(rules.ExpandPolynomial())
        calc = proof.rhs_calc
        calc.perform_rule(rules.RewriteLog())
        calc.perform_rule(rules.ExpandPolynomial())

        # Test parsing of json file
        json_file = file.export()
        for i, item in enumerate(json_file['content']):
            self.assertEqual(compstate.parse_item(item).export(), file.content[i].export())

        # Test goals are finished
        for content in file.content:
            self.assertTrue(content.is_finished())

        # Output to file
        with open('integral/examples/euler_log_sin.json', 'w', encoding='utf-8') as f:
            json.dump(file.export(), f, indent=4, ensure_ascii=False, sort_keys=True)

    def testDiricheletIntegral(self):
        file = compstate.CompFile("DiricheletIntegral")

        # Condition
        conds = conditions.Conditions()

        # Definition
        e = parser.parse_expr('I(b) = INT x:[0,oo]. sin(x) / x * exp(-b * x)')
        # add condition b>=0
        conds.add_condition("b>=0", parser.parse_expr("b>=0"))
        Idef = compstate.FuncDef(e, conds=conds)
        file.add_definition(Idef)

        e = parser.parse_expr("I(0) = SKOLEM_CONST(C)")
        lemma1 = compstate.Lemma(e)
        file.add_lemma(lemma1)


        e = parser.parse_expr("(INT x:[0,oo]. exp(-(b * x)) * sin(x)) = 1/(b^2+1)")  # for b > 0
        conds_of_lemma2 = compstate.Conditions()
        e2 = parser.parse_expr("b>0")
        conds_of_lemma2.add_condition(str(e2), e2)
        lemma2 = compstate.Lemma(e, conds_of_lemma2)
        file.add_lemma(lemma2)

        e = parser.parse_expr("(LIM {b -> oo}. INT x:[0,oo]. x ^ -1 * exp(-(b * x)) * sin(x)) = 0")
        lemma3 = compstate.Lemma(e)
        file.add_lemma(lemma3)

        # goal: D b. I(b) = -1/(b^2+1)
        e = parser.parse_expr("(D b. I(b)) = -1/(b^2+1)")
        conds_of_goal1 = conditions.Conditions()
        e2 = parser.parse_expr("b>0")
        conds_of_goal1.add_condition(str(e2), e2)
        goal1 = compstate.Goal(e, conds_of_goal1)
        file.add_goal(goal1)
        proof = goal1.proof_by_calculation()
        calc = proof.lhs_calc
        calc.perform_rule(rules.OnSubterm(rules.ExpandDefinition(Idef.eq)))
        calc.perform_rule(rules.DerivIntExchange())
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.OnLocation(rules.ApplyLemma(lemma2.lemma, lemma2.conds), '0'))
        calc.perform_rule(rules.FullSimplify())
        calc = proof.rhs_calc
        calc.perform_rule(rules.FullSimplify())
        #
        #
        # goal: I(0) = INT x:[0, oo]. sin(x) / x
        e = parser.parse_expr("I(0) = INT x:[0, oo]. sin(x) / x")
        goal2 = compstate.Goal(e)
        file.add_compstate(goal2)
        proof = goal2.proof_by_calculation()
        calc = proof.lhs_calc
        # need to check whether 0 is satisfied the condition of b
        calc.perform_rule(rules.ExpandDefinition(Idef.eq))
        calc = proof.rhs_calc
        calc.perform_rule(rules.FullSimplify())

        # goal: I(b) = -atan(b) + C for C is some constant
        e = parser.parse_expr("I(b) = -atan(b) + SKOLEM_CONST(C)")
        conds_of_goal3 = conditions.Conditions()
        e2 = parser.parse_expr("b>=0")
        conds_of_goal3.add_condition(str(e2), e2)
        goal3 = compstate.Goal(e, conds=conds_of_goal3)
        file.add_goal(goal3)
        cond_str = "b=0"
        proof = goal3.proof_by_case(cond_str)
        case_1_proof = proof.case_1.proof_by_calculation()
        calc = case_1_proof.lhs_calc
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.ApplyLemma(lemma1.lemma,lemma1.conds))
        calc = case_1_proof.rhs_calc
        calc.perform_rule(rules.FullSimplify())
        case_2_proof = proof.case_2.proof_by_rewrite_goal(begin=goal1)
        calc = case_2_proof.begin
        calc.perform_rule(rules.FullSimplify())
        left_skolem_name = 'E'
        calc.perform_rule(rules.IntegralEquation(var='b', left_skolem_name=left_skolem_name, right_skolem_name=None))
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.OnLocation(rules.CommonIndefiniteIntegral('C'), '1.0'))
        new_expr = parser.parse_expr("SKOLEM_CONST(C)")
        calc.perform_rule(rules.RewriteSkolemConst(new_expr=new_expr))

        e = parser.parse_expr("0 = (INT x:[0,oo]. x ^ -1 * sin(x)) - 1/2 * pi")
        goal4 = compstate.Goal(e)
        file.add_goal(goal4)
        proof_of_goal4 = goal4.proof_by_rewrite_goal(begin=goal3)
        calc = proof_of_goal4.begin
        calc.perform_rule(rules.OnLocation(rules.ApplyLemma(lemma1.lemma, lemma1.conds), '1.1'))
        calc.perform_rule(rules.LimitEquation(var='b', lim=expr.POS_INF))
        calc.perform_rule(rules.OnSubterm(rules.ExpandDefinition(Idef.eq)))
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.OnLocation(rules.ApplyEquation(lemma3.lemma), '0'))

        e = parser.parse_expr("(INT x:[0,oo]. x ^ -1 * sin(x)) = 1/2 * pi")
        goal5 = compstate.Goal(e)
        file.add_goal(goal5)
        proof_of_goal5 = goal5.proof_by_calculation()
        calc = proof_of_goal5.lhs_calc
        calc.perform_rule(rules.ApplyEquation(goal4.goal))
        calc.perform_rule(rules.FullSimplify())

        # print(file)
        # Test goals are finished
        for i in range(4, 9):
            self.assertTrue(file.content[i].is_finished())
        path = 'integral/examples/diricheletIntegral.json'
        with open(path, 'w', encoding='utf-8') as f:
            json.dump(file.export(), f, indent=4, ensure_ascii=False, sort_keys=True)

    def testIntegral01(self):
        # goal: INT x:[0, 1]. (x ^ a - 1) / log(x) = log(a + 1)
        file = compstate.CompFile("Integral01")

        # introduce definition
        e = parser.parse_expr("I(a) = INT x:[0, 1]. (x ^ a - 1) / log(x)")
        conds = compstate.Conditions()
        conds.add_condition(str("a>=0"), parser.parse_expr("a>=0"))
        Idef = compstate.FuncDef(e, conds)
        file.add_definition(Idef)

        # verify the following equation: D a. I(a) = 1/(a+1)
        e = parser.parse_expr("(D a. I(a)) = 1/(a+1)")
        goal1 = compstate.Goal(e, conds)
        file.add_goal(goal1)
        proof_of_goal1 = goal1.proof_by_calculation()
        calc = proof_of_goal1.lhs_calc
        calc.perform_rule(rules.OnSubterm(rules.ExpandDefinition(Idef.eq)))
        calc.perform_rule(rules.DerivIntExchange())
        calc.perform_rule(rules.FullSimplify())
        calc = proof_of_goal1.rhs_calc
        calc.perform_rule(rules.FullSimplify())

        # verify the following equation: I(a) = log(a+1)
        e = parser.parse_expr("I(0) = 0")
        goal2 = compstate.Goal(e)
        file.add_goal(goal2)
        proof_of_goal2 = goal2.proof_by_calculation()
        calc = proof_of_goal2.lhs_calc
        calc.perform_rule(rules.OnSubterm(rules.ExpandDefinition(Idef.eq)))
        calc.perform_rule(rules.FullSimplify())

        e = parser.parse_expr("I(a) = log(a+1) + SKOLEM_CONST(C)")
        conds2 = compstate.Conditions()
        e2 = parser.parse_expr("a>=0")
        conds2.add_condition(str(e2),e2)
        goal3 = compstate.Goal(e, conds2)
        file.add_goal(goal3)
        proof_of_goal3 = goal3.proof_by_rewrite_goal(begin=goal1)
        calc = proof_of_goal3.begin
        left_skolem_name = 'E'
        calc.perform_rule(rules.IntegralEquation(var='a', left_skolem_name='E', right_skolem_name=None))
        calc.perform_rule(rules.OnLocation(rules.CommonIndefiniteIntegral('C'), '1'))
        calc.perform_rule(rules.OnSubterm(rules.ElimAbs()))
        new_expr = parser.parse_expr("SKOLEM_CONST(C)")
        calc.perform_rule(rules.RewriteSkolemConst(new_expr=new_expr))

        e = parser.parse_expr("0 = SKOLEM_CONST(C)")
        goal4 = compstate.Goal(e)
        file.add_goal(goal4)
        proof_of_goal4 = goal4.proof_by_rewrite_goal(begin=goal3)
        calc = proof_of_goal4.begin
        calc.perform_rule(rules.VarSubsOfEquation('a', expr.Const(0)))
        calc.perform_rule(rules.OnLocation(rules.ApplyEquation(goal2.goal), '0'))
        calc.perform_rule(rules.FullSimplify())

        e = parser.parse_expr("I(a) = log(a+1)")
        conds4 = compstate.Conditions()
        conds4.add_condition("a>=0", parser.parse_expr("a>=0"))
        goal5 = compstate.Goal(e, conds4)
        file.add_goal(goal5)
        proof_of_goal5 = goal5.proof_by_calculation()
        calc = proof_of_goal5.lhs_calc
        calc.perform_rule(rules.ApplyEquation(goal3.goal))
        # didn't check condition about goal4
        calc.perform_rule(rules.OnLocation(rules.ApplyEquation(goal4.goal), '1'))
        calc.perform_rule(rules.FullSimplify())

        for i in range(1, 6):
            self.assertTrue(file.content[i].is_finished())
        path = 'integral/examples/integral01.json'
        with open(path, 'w', encoding='utf-8') as f:
            json.dump(file.export(), f, indent=4, ensure_ascii=False, sort_keys=True)

    def testFrullaniIntegral(self):
        # Reference:
        # Inside interesting integrals, Section 3.3

        file = compstate.CompFile("Frullani Integral")

        # Define I(a, b)
        e = parser.parse_expr("I(a, b) = INT x:[0,oo]. (atan(a*x) - atan(b*x))/x")
        conds_of_Idef = compstate.Conditions()
        e2 = parser.parse_expr("a > 0")
        conds_of_Idef.add_condition("a", e2)
        e2 = parser.parse_expr("b > 0")
        conds_of_Idef.add_condition("b", e2)
        Idef = compstate.FuncDef(e, conds_of_Idef)
        file.add_definition(Idef)

        # Show I(a, a) = 0
        e = parser.parse_expr("I(a, a) = 0")
        goal1 = compstate.Goal(e)
        file.add_goal(goal1)
        proof_of_goal1 = goal1.proof_by_calculation()
        calc = proof_of_goal1.lhs_calc
        calc.perform_rule(rules.ExpandDefinition(Idef.eq))
        calc.perform_rule(rules.FullSimplify())

        # Evalute D a. I(a, b) for a > 0
        e = parser.parse_expr("(D a. I(a,b)) = pi / (2*a)")
        conds_of_goal2 = compstate.Conditions()
        e2 = parser.parse_expr("a > 0")
        conds_of_goal2.add_condition("a", e2)
        goal2 = compstate.Goal(e, conds_of_goal2)
        file.add_goal(goal2)
        proof_of_goal2 = goal2.proof_by_calculation()
        calc = proof_of_goal2.lhs_calc
        calc.perform_rule(rules.OnSubterm(rules.ExpandDefinition(Idef.eq)))
        calc.perform_rule(rules.DerivIntExchange())
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.ElimInfInterval())
        new_expr = parser.parse_expr('(a*x) ^ 2')
        old_expr = parser.parse_expr("a^2 * x^2")
        calc.perform_rule(rules.Equation(new_expr=new_expr, old_expr=old_expr))
        calc.perform_rule(rules.OnLocation(rules.Substitution('u' , parser.parse_expr("a*x")) ,'0'))
        calc.perform_rule(rules.FullSimplify())
        calc = proof_of_goal2.rhs_calc
        calc.perform_rule(rules.FullSimplify())

        # Integrate the previous result to get formula for I(a,b)
        # TODO: can simplify
        e = parser.parse_expr("I(a,b) = 1/2 * pi * log(a) - SKOLEM_FUNC(C(b))")
        conds_of_goal3 = compstate.Conditions()
        e2 = parser.parse_expr("a > 0")
        conds_of_goal3.add_condition("a", e2)
        goal3 = compstate.Goal(e, conds_of_goal3)
        file.add_goal(goal3)
        proof_of_goal3 = goal3.proof_by_rewrite_goal(begin=goal2)
        calc = proof_of_goal3.begin
        left_skolem_name = 'E'
        calc.perform_rule(rules.IntegralEquation(var='a', left_skolem_name=left_skolem_name, right_skolem_name=None))
        calc.perform_rule(rules.OnLocation(rules.FullSimplify(), '1'))
        calc.perform_rule(rules.OnSubterm(rules.CommonIndefiniteIntegral(const_name='C')))
        calc.perform_rule(rules.OnLocation(rules.ExpandPolynomial(), '1'))
        new_expr = parser.parse_expr("-SKOLEM_FUNC(C(b))")
        calc.perform_rule(rules.RewriteSkolemConst(new_expr = new_expr))
        calc.perform_rule(rules.OnSubterm(rules.ElimAbs()))
        calc.perform_rule(rules.FullSimplify())

        # Special case I(a,a)
        e = parser.parse_expr("I(a,a) = 1/2 * pi * log(a) - SKOLEM_FUNC(C(a))")
        conds_of_goal4 = compstate.Conditions()
        e2 = parser.parse_expr("a>0")
        conds_of_goal4.add_condition(str(e2), e2)
        goal4 = compstate.Goal(e, conds_of_goal4)
        file.add_goal(goal4)
        proof_of_goal4 = goal4.proof_by_calculation()
        calc = proof_of_goal4.lhs_calc
        calc.perform_rule(rules.ExpandDefinition(goal3.goal))

        # Obtain value of Skolem function
        e = parser.parse_expr("SKOLEM_FUNC(C(a)) = 1/2 * pi * log(a)")
        conds_of_goal5 = compstate.Conditions()
        e2 = parser.parse_expr("a>0")
        conds_of_goal5.add_condition(str(e2), e2)
        goal5 = compstate.Goal(e, conds_of_goal5)
        file.add_goal(goal5)
        proof_of_goal5 = goal5.proof_by_calculation()
        calc = proof_of_goal5.lhs_calc
        calc.perform_rule(rules.ApplyEquation(goal4.goal))
        calc.perform_rule(rules.OnSubterm(rules.ApplyEquation(goal1.goal)))
        calc.perform_rule(rules.FullSimplify())

        # Final result
        e = parser.parse_expr("I(a, b) = 1/2 * pi * log(a) - 1/2 * pi * log(b)")
        conds_of_goal6 = compstate.Conditions()
        e2 = parser.parse_expr("a>0")
        conds_of_goal6.add_condition(str(e2), e2)
        e2 = parser.parse_expr("b>0")
        conds_of_goal6.add_condition(str(e2), e2)
        goal6 = compstate.Goal(e, conds_of_goal6)
        file.add_goal(goal6)
        proof_of_goal6 = goal6.proof_by_calculation()
        calc = proof_of_goal6.lhs_calc
        calc.perform_rule(rules.ApplyEquation(goal3.goal))
        calc.perform_rule(rules.OnSubterm(rules.ExpandDefinition(goal5.goal)))

        # Test parsing of json file
        json_file = file.export()
        for i, item in enumerate(json_file['content']):
            self.assertEqual(compstate.parse_item(item).export(), file.content[i].export())

        # Test goals are finished
        for content in file.content:
            self.assertTrue(content.is_finished())

        # Output to file
        path = 'integral/examples/FrullaniIntegral.json'
        with open(path, 'w', encoding='utf-8') as f:
            json.dump(file.export(), f, indent=4, ensure_ascii=False, sort_keys=True)

    def testCatalanConstant01(self):
        # Reference:
        # Inside interesting integrals, Section 5.1, example #1

        file = compstate.CompFile('CatalanConstant01')

        # Define Catalan's constant
        e = parser.parse_expr('G = SUM(n, 0, oo, (-1)^n / (2*n+1)^2)')
        Gdef = compstate.FuncDef(e)
        file.add_definition(Gdef)

        # Evaluate integral of atan(x) / x
        e = parser.parse_expr("(INT x:[0, 1]. atan(x) / x) = G")
        goal01 = compstate.Goal(goal=e, conds=None)
        file.add_goal(goal01)
        proof_of_goal01 = goal01.proof_by_calculation()
        calc = proof_of_goal01.lhs_calc
        calc.perform_rule(rules.OnLocation(rules.ExpandSeries(), '0.0'))
        old_expr = parser.parse_expr("x ^ (2 * n + 1)")
        new_expr = parser.parse_expr("x^ (2*n) * x")
        calc.perform_rule(rules.Equation(old_expr=old_expr,new_expr=new_expr))
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.IntSumExchange())
        calc.perform_rule(rules.FullSimplify())
        calc = proof_of_goal01.rhs_calc
        calc.perform_rule(rules.ApplyEquation(Gdef.eq))
        calc.perform_rule(rules.FullSimplify())

        # Test parsing of json file
        json_file = file.export()
        for i, item in enumerate(json_file['content']):
            self.assertEqual(compstate.parse_item(item).export(), file.content[i].export())

        # Test goals are finished
        for content in file.content:
            self.assertTrue(content.is_finished())

        # Output to file
        path = 'integral/examples/CatalanConstant01.json'
        with open(path, 'w', encoding='utf-8') as f:
            json.dump(file.export(), f, indent=4, ensure_ascii=False, sort_keys=True)

    def testCatalanConstant02(self):
        # Reference:
        # Inside interesting integrals, Section 5.1, example #2

        file = compstate.CompFile('CatalanConstant02')

        # Define Catalan's constant
        e = parser.parse_expr('G = SUM(n, 0, oo, (-1)^n / (2*n+1)^2)')
        Gdef = compstate.FuncDef(e)
        file.add_definition(Gdef)

        # Define I(k)
        e = parser.parse_expr("I(k) = INT x:[1,oo]. log(x) / (x^k)")
        conds_of_Idef = compstate.Conditions()
        e2 = parser.parse_expr("k > 1")
        conds_of_Idef.add_condition("k", e2)
        Idef = compstate.FuncDef(e,conds=conds_of_Idef)
        file.add_definition(Idef)

        # Evaluate I(k)
        e = parser.parse_expr("I(k) = 1/(k-1)^2")
        conds_of_goal1 = compstate.Conditions()
        e2 = parser.parse_expr("k > 1")
        conds_of_goal1.add_condition("k", e2)
        goal1 = compstate.Goal(e, conds=conds_of_goal1)
        file.add_goal(goal1)

        proof_of_goal1 = goal1.proof_by_calculation()
        calc = proof_of_goal1.lhs_calc
        calc.perform_rule(rules.ExpandDefinition(Idef.eq))
        u = parser.parse_expr("log(x)")
        v = parser.parse_expr("(x^(1-k)) / (1-k)")
        calc.perform_rule(rules.ElimInfInterval())
        calc.perform_rule(rules.OnLocation(rules.IntegrationByParts(u=u,v=v), '0'))
        calc.perform_rule(rules.FullSimplify())
        old_expr = parser.parse_expr("t ^ (-k + 1) * log(t)")
        new_expr = parser.parse_expr("log(t) / t^(k-1)")
        calc.perform_rule(rules.Equation(old_expr=old_expr, new_expr=new_expr))
        calc.perform_rule(rules.OnLocation(rules.LHopital(), '0.1'))
        calc.perform_rule(rules.FullSimplify())
        calc = proof_of_goal1.rhs_calc
        calc.perform_rule(rules.FullSimplify())
        old_expr=parser.parse_expr("(k-1)^-2")
        new_expr=parser.parse_expr("(-k+1)^-2")
        calc.perform_rule(rules.Equation(old_expr=old_expr,new_expr=new_expr))

        # Special case of I(2*n+2)
        e = parser.parse_expr("I(2 * n + 2) = 1/(2*n+1)^2")
        goal2 = compstate.Goal(e)
        file.add_goal(goal2)
        proof_of_goal2 = goal2.proof_by_calculation()
        calc = proof_of_goal2.lhs_calc
        calc.perform_rule(rules.ExpandDefinition(goal1.goal))
        calc = proof_of_goal2.rhs_calc
        calc.perform_rule(rules.FullSimplify())

        # Definition of I(2*n+2)
        e = parser.parse_expr("I(2*n+2) = INT x:[1,oo]. log(x) / (x^(2*n+2))")
        goal3 = compstate.Goal(e)
        file.add_goal(goal3)
        proof_of_goal3 = goal3.proof_by_calculation()
        calc = proof_of_goal3.lhs_calc
        calc.perform_rule(rules.ExpandDefinition(Idef.eq))
        calc = proof_of_goal3.rhs_calc
        calc.perform_rule(rules.FullSimplify())

        # Combine previous two results
        # TODO: can simplify these three parts
        e = parser.parse_expr("(INT x:[1,oo]. log(x) / x^(2*n+2)) = 1/(2*n+1)^2")
        goal4 = compstate.Goal(e)
        file.add_goal(goal4)
        proof_of_goal4 = goal4.proof_by_calculation()
        calc = proof_of_goal4.lhs_calc
        calc.perform_rule(rules.FullSimplify())
        calc = proof_of_goal4.rhs_calc
        calc.perform_rule(rules.ApplyEquation(goal2.goal))
        calc.perform_rule(rules.ApplyEquation(goal3.goal))
        calc.perform_rule(rules.FullSimplify())

        e = parser.parse_expr("(INT x:[1,oo]. log(x) / (x^2+1)) = G")
        goal5 = compstate.Goal(e)
        file.add_goal(goal5)
        proof_of_goal5 = goal5.proof_by_calculation()
        calc = proof_of_goal5.lhs_calc
        old_expr = parser.parse_expr("log(x)/(x^2+1)")
        new_expr = parser.parse_expr("log(x) * (x^-2) * (1 + (1/x^2))^-1")
        calc.perform_rule(rules.Equation(old_expr=old_expr, new_expr=new_expr))
        calc.perform_rule(rules.OnLocation(rules.ExpandSeries(), '0.1'))
        old_expr = parser.parse_expr("log(x) * x ^ (-2) * SUM(n, 0, oo, (-1) ^ n * (1 / x ^ 2) ^ n)")
        new_expr = parser.parse_expr("SUM(n, 0, oo, (-1) ^ n * ((1 / x ^ 2) ^ n) * log(x) * x ^ -2)")
        calc.perform_rule(rules.Equation(old_expr=old_expr, new_expr=new_expr))
        calc.perform_rule(rules.IntSumExchange())
        calc.perform_rule(rules.FullSimplify())
        old_expr = parser.parse_expr("x ^ (-2 * n - 2) * log(x)")
        new_expr = parser.parse_expr("log(x) / x^(2*n+2)")
        calc.perform_rule(rules.Equation(old_expr=old_expr, new_expr=new_expr))
        calc.perform_rule(rules.OnLocation(rules.ApplyEquation(goal4.goal), '0.1'))
        calc.perform_rule(rules.FullSimplify())
        calc = proof_of_goal5.rhs_calc
        calc.perform_rule(rules.ApplyEquation(eq=Gdef.eq))
        calc.perform_rule(rules.FullSimplify())

        # Test parsing of json file
        json_file = file.export()
        for i, item in enumerate(json_file['content']):
            self.assertEqual(compstate.parse_item(item).export(), file.content[i].export())

        # Test goals are finished
        for content in file.content:
            self.assertTrue(content.is_finished())

        # Output to file
        path = 'integral/examples/CatalanConstant02.json'
        with open(path, 'w', encoding='utf-8') as f:
            json.dump(file.export(), f, indent=4, ensure_ascii=False, sort_keys=True)

    def testLogFunction01(self):
        file = compstate.CompFile("LogFunction01")
        conds_of_lemma01 = compstate.Conditions()
        e = parser.parse_expr("abs(x) < 1")
        conds_of_lemma01.add_condition(str(e), e)
        e = parser.parse_expr("log(1+x) = SUM(k,0,oo,(-1)^k * (x^(k+1))/(k+1))")
        lemma01 = compstate.Lemma(lemma = e,conds = conds_of_lemma01)
        file.add_lemma(lemma01)

        e = parser.parse_expr("SUM(k,0,oo,(-1)^k * (k+1)^(-2))  = (pi^2) / 12")
        lemma02 = compstate.Lemma(lemma = e, conds = None)
        file.add_lemma(lemma02)

        e = parser.parse_expr("(INT x:[0,1]. log(x+1) / x) = (pi^2) / 12")
        goal01 = compstate.Goal(goal = e, conds = None)
        file.add_goal(goal01)
        proof_of_goal01 = goal01.proof_by_calculation()
        calc = proof_of_goal01.lhs_calc

        # TODO: condition check
        calc.perform_rule(rules.OnSubterm(rules.ApplyLemma(lemma=lemma01.lemma, conds=None)))
        old_expr = parser.parse_expr("SUM(k,0,oo,(-1) ^ k * x ^ (k + 1) / (k + 1)) / x")
        new_expr = parser.parse_expr("SUM(k,0,oo,(-1) ^ k * x ^ (k + 1) / (k + 1) * (1/x))")
        calc.perform_rule(rules.Equation(old_expr = old_expr, new_expr = new_expr))
        calc.perform_rule(rules.IntSumExchange())
        calc.perform_rule(rules.FullSimplify())

        calc.perform_rule(rules.ApplyLemma(lemma = lemma02.lemma, conds = None))
        calc.perform_rule(rules.FullSimplify())
        calc = proof_of_goal01.rhs_calc
        calc.perform_rule(rules.FullSimplify())

        self.assertTrue(file.content[2].is_finished())
        path = 'integral/examples/LogFunction01.json'
        with open(path, 'w', encoding='utf-8') as f:
            json.dump(file.export(), f, indent=4, ensure_ascii=False, sort_keys=True)

    def testLogFunction02(self):
        file = compstate.CompFile('LogFunction02')

        conds_of_lemma01 = compstate.Conditions()
        e = parser.parse_expr("abs(x) < 1")
        conds_of_lemma01.add_condition(str(e), e)
        e = parser.parse_expr("log(1+x) = SUM(k,0,oo,(-1)^k * (x^(k+1))/(k+1))")
        lemma01 = compstate.Lemma(lemma=e, conds=conds_of_lemma01)
        file.add_lemma(lemma01)

        e = parser.parse_expr("SUM(k,0,oo,(k+1)^(-2))  = (pi^2) / 6")
        lemma02 = compstate.Lemma(lemma=e, conds=None)
        file.add_lemma(lemma02)

        e = parser.parse_expr("sin(acos(x)) = sqrt(1-x^2)")
        lemma03 = compstate.Lemma(lemma=e, conds=None)
        file.add_lemma(lemma03)

        e = parser.parse_expr("(INT x:[0,1]. x ^ k * log(x)) = -1/(k+1)^2")
        lemma04 = compstate.Lemma(lemma=e, conds=None)
        file.add_lemma(lemma04)

        e = parser.parse_expr("(INT x:[0,1]. (-x) ^ k * log(x)) = -(-1)^ k /(k+1)^2")
        lemma05 = compstate.Lemma(lemma=e, conds=None)
        file.add_lemma(lemma05)

        e = parser.parse_expr("SUM(k,0,oo,(-1)^k * (k+1)^(-2))  = (pi^2) /12")
        lemma06 = compstate.Lemma(lemma=e, conds=None)
        file.add_lemma(lemma06)

        conds_of_goal01 = compstate.Conditions()
        e = parser.parse_expr("abs(x) < 1")
        conds_of_goal01.add_condition(str(e), e)
        s = "-log(1-x) - log(1+x) = \
                -SUM(k,0,oo,(-1)^k*(-x)^(k+1) / (k+1))-SUM(k,0,oo,(-1)^k*x^(k+1)/(k+1))"
        e = parser.parse_expr(s)
        goal01 = compstate.Goal(goal = e, conds = conds_of_goal01)
        file.add_goal(goal01)
        proof_of_goal01 = goal01.proof_by_calculation()
        calc = proof_of_goal01.lhs_calc
        calc.perform_rule(rules.OnSubterm(rules.ExpandSeries(index_var='k')))
        calc.perform_rule(rules.FullSimplify())
        calc = proof_of_goal01.rhs_calc
        calc.perform_rule(rules.FullSimplify())

        s = "x * (-(x ^ 2) + 1) ^ (-1) = 1/2 * SUM(k, 0, oo, (-1) ^ k * (-x) ^ k) - 1/2 * SUM(k, 0, oo, x ^ k * (-1) ^ k)"
        e = parser.parse_expr(s)
        goal02 = compstate.Goal(goal = e, conds = None)
        file.add_goal(goal02)
        proof_of_goal02 = goal02.proof_by_rewrite_goal(begin = goal01)
        calc = proof_of_goal02.begin

        calc.perform_rule(rules.DerivEquation('x'))
        calc.perform_rule(rules.FullSimplify())
        old_expr = parser.parse_expr("(-x + 1) ^ (-1) - (x + 1) ^ (-1)")
        new_expr = parser.parse_expr("2 * (x / (1-x^2))")
        calc.perform_rule(rules.Equation(new_expr=new_expr, old_expr=old_expr))
        e = parser.parse_expr('1/2')
        calc.perform_rule(rules.MulEquation(e = e))

        e = parser.parse_expr("(INT x:[0, pi/2]. cos(x)/sin(x) * log(1/cos(x))) = pi^2/24")
        goal03 = compstate.Goal(goal = e, conds = None)
        file.add_goal(goal03)
        proof_of_goal03 = goal03.proof_by_calculation()
        calc = proof_of_goal03.lhs_calc
        e = parser.parse_expr("cos(x)")
        calc.perform_rule(rules.Substitution(var_name='t', var_subst=e))
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.OnSubterm(rules.ApplyLemma(lemma03.lemma, conds=None)))
        calc.perform_rule(rules.FullSimplify())
        e = parser.parse_expr("t")
        calc.perform_rule(rules.OnLocation(rules.Substitution(var_name='x', var_subst=e), '0'))
        old_expr = parser.parse_expr("x * log(x) * (-(x ^ 2) + 1) ^ (-1)")
        new_expr = parser.parse_expr("log(x) * (x * (-(x ^ 2) + 1) ^ (-1))")
        calc.perform_rule(rules.Equation(new_expr=new_expr, old_expr=old_expr))
        calc.perform_rule(rules.OnSubterm(rules.ApplyEquation(goal02.goal)))
        calc.perform_rule(rules.OnSubterm(rules.ExpandPolynomial()))
        calc.perform_rule(rules.FullSimplify())
        old_expr = parser.parse_expr("log(x) * SUM(k, 0, oo, (-1) ^ k * (-x) ^ k)")
        new_expr = parser.parse_expr("SUM(k, 0, oo, log(x)*(-1) ^ k * (-x) ^ k)")
        calc.perform_rule(rules.Equation(new_expr=new_expr, old_expr=old_expr))
        old_expr = parser.parse_expr("log(x) * SUM(k, 0, oo, x ^ k * (-1) ^ k)")
        new_expr = parser.parse_expr("SUM(k, 0, oo, log(x) * x ^ k * (-1) ^ k)")
        calc.perform_rule(rules.Equation(new_expr=new_expr, old_expr=old_expr))
        calc.perform_rule(rules.OnSubterm(rules.IntSumExchange()))
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.OnSubterm(rules.ApplyLemma(lemma=lemma04.lemma, conds=None)))
        calc.perform_rule(rules.OnLocation(rules.ApplyLemma(lemma=lemma05.lemma, conds=None), '0.1.0.1'))
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.OnSubterm(rules.ApplyLemma(lemma=lemma02.lemma, conds=None)))
        calc.perform_rule(rules.OnLocation(rules.ApplyLemma(lemma=lemma06.lemma, conds=None), '0.1'))
        calc.perform_rule(rules.FullSimplify())
        calc = proof_of_goal03.rhs_calc
        calc.perform_rule(rules.FullSimplify())
        # print(file)
        for i in range(6,9):
            self.assertTrue(file.content[i].is_finished())
        path = 'integral/examples/LogFunction02.json'
        with open(path, 'w', encoding='utf-8') as f:
            json.dump(file.export(), f, indent=4, ensure_ascii=False, sort_keys=True)


    def testBernoulliIntegral(self):
        file = compstate.CompFile("Bernoulli's Integral")

        e = parser.parse_expr("f(m, n) = INT x:[0, 1]. x^m * log(x) ^ n")
        Idef = compstate.FuncDef(e)
        file.add_definition(Idef)

        e = parser.parse_expr("f(m, n) = (-1)^n * factorial(n) / (m+1) ^ (n+1)")
        lemma = compstate.Lemma(lemma=e, conds=None)
        file.add_lemma(lemma)

        e = parser.parse_expr("f(a*k, k) = INT x:[0, 1]. x^(a*k) * log(x)^k")
        goal01 = compstate.Goal(goal=e, conds=None)
        file.add_goal(goal01)
        proof_of_goal01 = goal01.proof_by_calculation()
        calc = proof_of_goal01.lhs_calc
        calc.perform_rule(rules.ExpandDefinition(Idef.eq))

        e = parser.parse_expr("(INT x:[0,1]. x^(c*x^a)) = SUM(k,0,oo,(-c)^k / (k*a+1)^(k+1))")
        goal02 = compstate.Goal(goal=e, conds=None)
        file.add_goal(goal02)

        proof_of_goal02 = goal02.proof_by_calculation()
        calc = proof_of_goal02.lhs_calc
        old_expr = parser.parse_expr("x^(c*x^a)")
        new_expr = parser.parse_expr("exp(log(x^(c*x^a)))")
        calc.perform_rule(rules.Equation(old_expr=old_expr, new_expr=new_expr))
        calc.perform_rule(rules.OnSubterm(rules.ExpandSeries(index_var='k')))
        calc.perform_rule(rules.IntSumExchange())

        old_expr = parser.parse_expr("log(x ^ (c * x ^ a))")
        new_expr = parser.parse_expr("(c*x^a) * log(x)")
        calc.perform_rule(rules.Equation(old_expr=old_expr, new_expr=new_expr))

        old_expr = parser.parse_expr("(c * x ^ a * log(x)) ^ k")
        new_expr = parser.parse_expr("(c * x ^ a) ^ k * log(x) ^ k")
        calc.perform_rule(rules.Equation(old_expr=old_expr, new_expr=new_expr))

        old_expr = parser.parse_expr("(c * x ^ a)^k")
        new_expr = parser.parse_expr("(c^k * x ^ a^k)")
        calc.perform_rule(rules.Equation(old_expr=old_expr, new_expr=new_expr))
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.OnSubterm(rules.ApplyEquation(goal01.goal)))
        calc.perform_rule(rules.OnSubterm(rules.ApplyLemma(lemma=lemma.lemma, conds=None)))
        calc.perform_rule(rules.FullSimplify())
        old_expr = parser.parse_expr("c ^ k * (-1) ^ k")
        new_expr = parser.parse_expr("(-c)^k")
        calc.perform_rule(rules.Equation(old_expr=old_expr, new_expr=new_expr))
        calc = proof_of_goal02.rhs_calc
        calc.perform_rule(rules.FullSimplify())
        # print(file)
        for i in range(2,4):
            self.assertTrue(file.content[i].is_finished())
        path = 'integral/examples/BernoulliIntegral.json'
        with open(path, 'w', encoding='utf-8') as f:
            json.dump(file.export(), f, indent=4, ensure_ascii=False, sort_keys=True)

    def testAhmedIntegral(self):
        file = compstate.CompFile("Ahmed Integral")

        conds_of_Idef = compstate.Conditions()
        e = parser.parse_expr("u>0")
        conds_of_Idef.add_condition(str(e), e)

        s = "I(u) = (INT x:[0,1]. atan(u * sqrt(2+x*x)) / ((1+x*x)*sqrt(2+x*x)))"
        e = parser.parse_expr(s)

        Idef = compstate.FuncDef(eq=e, conds=conds_of_Idef)
        file.add_definition(Idef)

        e = "atan(sqrt(x ^ 2 + 2) ^ (-1)) = pi/2 - atan(sqrt(x^2+2))"
        lemma01 = compstate.Lemma(lemma=parser.parse_expr(e))
        file.add_lemma(lemma01)

        e = "I(1) = INT x:[0,1]. (x ^ 2 + 1) ^ (-1) * (x ^ 2 + 2) ^ (-1/2) * atan(sqrt(x ^ 2 + 2))"
        goal001 = compstate.Goal(parser.parse_expr(e))
        file.add_goal(goal = goal001)
        proof = goal001.proof_by_calculation()
        calc = proof.lhs_calc
        calc.perform_rule(rules.ExpandDefinition(Idef.eq))
        calc.perform_rule(rules.FullSimplify())
        e = "(LIM {u->oo}. I(u)) = 1/2 * pi * (INT x:[0,1]. (x ^ 2 + 1) ^ (-1) * (x ^ 2 + 2) ^ (-1/2))"
        conds_of_goal002 = compstate.Conditions()
        ce = parser.parse_expr("u>0")
        conds_of_goal002.add_condition(str(ce), ce)
        goal002 = compstate.Goal(parser.parse_expr(e))
        file.add_goal(goal = goal002)
        proof = goal002.proof_by_calculation()
        calc = proof.lhs_calc
        calc.perform_rule(rules.OnSubterm(rules.ExpandDefinition(Idef.eq)))
        calc.perform_rule(rules.LimIntExchange())
        calc.perform_rule(rules.FullSimplify())

        e = "(LIM {u->oo}. I(u)) = pi^2 / 12"
        goal01 = compstate.Goal(goal=parser.parse_expr(e))
        file.add_goal(goal=goal01)
        proof = goal01.proof_by_calculation()
        calc = proof.lhs_calc
        calc.perform_rule(rules.OnSubterm(rules.ExpandDefinition(Idef.eq)))
        calc.perform_rule(rules.LimIntExchange())
        calc.perform_rule(rules.FullSimplify())
        u = expr.Const(1)
        v = parser.parse_expr("atan(x/sqrt(2+x*x))")
        calc.perform_rule(rules.OnLocation(rules.IntegrationByParts(u=u,v=v), "1"))
        calc.perform_rule(rules.FullSimplify())
        calc = proof.rhs_calc
        calc.perform_rule(rules.FullSimplify())

        e = parser.parse_expr("(D u. I(u)) = (1+u^2)^(-1) * (pi/4 - u * sqrt(1+2*u^2)^(-1)*atan(u/sqrt(1+2*u^2)))")
        conds_of_goal02 = compstate.Conditions()
        ce = parser.parse_expr("u>0")
        conds_of_goal02.add_condition(str(ce), ce)
        goal02 = compstate.Goal(e, conds=conds_of_goal02)
        file.add_goal(goal02)
        proof = goal02.proof_by_calculation()
        calc = proof.lhs_calc
        calc.perform_rule(rules.OnSubterm(rules.ExpandDefinition(Idef.eq)))
        calc.perform_rule(rules.DerivIntExchange())
        calc.perform_rule(rules.FullSimplify())
        new_expr = parser.parse_expr("(1+u^2)^(-1) * ((1+x^2)^(-1) - u^2 / (1+2*u^2+u^2*x^2))")
        old_expr = parser.parse_expr("(x ^ 2 + 1) ^ (-1) * (u ^ 2 * (x ^ 2 + 2) + 1) ^ (-1)")
        calc.perform_rule(rules.Equation(new_expr=new_expr, old_expr=old_expr))
        calc.perform_rule(rules.FullSimplify())
        new_expr = parser.parse_expr("u^(-2) * (x ^ 2 + (2 * u ^ 2 + 1)/u^2) ^ (-1)")
        old_expr = parser.parse_expr("(u ^ 2 * x ^ 2 + 2 * u ^ 2 + 1) ^ (-1)")
        calc.perform_rule(rules.Equation(new_expr=new_expr, old_expr=old_expr))
        calc.perform_rule(rules.FullSimplify())
        e = parser.parse_expr("y * sqrt(u ^ (-2) * (2 * u ^ 2 + 1))")
        calc.perform_rule(rules.SubstitutionInverse(var_name='y', var_subst=e))
        calc.perform_rule(rules.OnSubterm(rules.ElimAbs()))
        old_expr = parser.parse_expr("(u ^ (-2) * (2 * u ^ 2 + 1) + (y * sqrt(u ^ (-2) * (2 * u ^ 2 + 1))) ^ 2) ^ (-1)")
        new_expr = parser.parse_expr("(u^(-2) * (2*u^2+1))^(-1) * (1+y^2)^(-1)")
        calc.perform_rule(rules.Equation(new_expr=new_expr, old_expr=old_expr))
        calc.perform_rule(rules.FullSimplify())
        calc = proof.rhs_calc
        calc.perform_rule(rules.FullSimplify())

        e = parser.parse_expr("(INT u:[1, oo]. D u. I(u)) = pi^2/12 - I(1)")
        goal03 = compstate.Goal(e)
        file.add_goal(goal03)
        proof = goal03.proof_by_calculation()
        calc = proof.lhs_calc
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.OnSubterm(rules.ApplyEquation(eq=goal01.goal)))
        calc.perform_rule(rules.FullSimplify())
        calc = proof.rhs_calc
        calc.perform_rule(rules.FullSimplify())

        e = parser.parse_expr("(INT u:[1,oo]. D u. I(u)) = - (pi^2 / 48) + I(1)")
        goal04 = compstate.Goal(e)
        file.add_goal(goal04)
        proof_of_goal04 = goal04.proof_by_calculation()
        calc = proof_of_goal04.lhs_calc
        calc.perform_rule(rules.OnSubterm(rules.ApplyEquation(goal02.goal)))
        calc.perform_rule(rules.OnLocation(rules.ExpandPolynomial(),'0'))
        calc.perform_rule(rules.FullSimplify())
        e = parser.parse_expr("1/x")

        calc.perform_rule(rules.OnLocation(rules.SubstitutionInverse(var_name='x', var_subst=e), '0.0'))
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.OnSubterm(rules.RewriteMulPower(0)))
        old_expr = parser.parse_expr("5 * x ^ 2 + 4 * x ^ 4 + x ^ 6 + 2")
        new_expr = parser.parse_expr("(1+x^2)^2*(2+x^2)")
        calc.perform_rule(rules.Equation(new_expr=new_expr, old_expr=old_expr))
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.OnSubterm(rules.ElimAbs()))
        old_expr = parser.parse_expr("(x ^ 2 + 2) ^ (-1/2)")
        new_expr = parser.parse_expr("sqrt(x^2+2) ^ (-1)")
        calc.perform_rule(rules.OnLocation(rules.Equation(new_expr=new_expr, old_expr=old_expr), '0.0.0.1.0'))
        calc.perform_rule(rules.OnSubterm(rules.ApplyLemma(lemma=lemma01.lemma,conds=lemma01.conds)))
        calc.perform_rule(rules.OnSubterm(rules.ExpandPolynomial()))
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.OnSubterm(rules.ApplyEquation(eq = goal001.goal)))
        calc.perform_rule(rules.OnSubterm(rules.ApplyEquation(eq = goal002.goal)))
        calc.perform_rule(rules.OnSubterm(rules.ApplyEquation(eq = goal01.goal)))
        calc.perform_rule(rules.FullSimplify())
        calc = proof_of_goal04.rhs_calc
        calc.perform_rule(rules.FullSimplify())

        e = parser.parse_expr("I(1) = 5*pi^2/96")
        goal05 = compstate.Goal(e)
        file.add_goal(goal05)
        proof_of_goal05 = goal05.proof_by_rewrite_goal(begin=goal03)
        calc = proof_of_goal05.begin
        calc.perform_rule(rules.OnLocation(rules.ApplyEquation(eq=goal04.goal), '0'))
        calc.perform_rule(rules.SolveEquation(parser.parse_expr("I(1)")))

        for i in range(2,9):
            self.assertTrue(file.content[i].is_finished())
        path = 'integral/examples/AhmedIntegral.json'
        with open(path, 'w', encoding='utf-8') as f:
            json.dump(file.export(), f, indent=4, ensure_ascii=False, sort_keys=True)


if __name__ == "__main__":
    unittest.main()
