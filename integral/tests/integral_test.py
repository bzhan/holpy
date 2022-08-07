"""Overall test for integrals."""

import unittest
import json

from logic import basic
from integral import compstate
from integral import rules
from integral import parser
from integral import conditions


class IntegralTest(unittest.TestCase):
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
        calc.perform_rule(rules.OnLocation(rules.Equation(parser.parse_expr("sin(x) * sin(x)^2")), "0.0.0"))
        calc.perform_rule(rules.OnLocation(rules.RewriteTrigonometric("TR5"), "0.0.0.1"))
        calc.perform_rule(rules.Substitution("u", parser.parse_expr("cos(x)")))
        calc.perform_rule(rules.FullSimplify())
        self.assertEqual(str(calc.last_expr), "pi - 4/3")

        calc = file.add_calculation("INT x:[pi/6, pi/2]. cos(x) ^ 2")
        calc.perform_rule(rules.OnLocation(rules.RewriteTrigonometric("TR7"), "0"))
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.Substitution("u", parser.parse_expr("2 * x")))
        calc.perform_rule(rules.FullSimplify())
        self.assertEqual(str(calc.last_expr), "-1/8 * sqrt(3) + 1/6 * pi")

        calc = file.add_calculation("INT x:[0, 1]. (1 - x^2) ^ (1/2)")
        calc.perform_rule(rules.SubstitutionInverse("u", parser.parse_expr("sin(u)")))
        calc.perform_rule(rules.OnLocation(rules.RewriteTrigonometric("TR5"), "0.0.0"))
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.ElimAbs())
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.OnLocation(rules.RewriteTrigonometric("TR7"), "0"))
        calc.perform_rule(rules.Substitution("v", parser.parse_expr("2 * u")))
        calc.perform_rule(rules.FullSimplify())
        self.assertEqual(str(calc.last_expr), "1/4 * pi")

        calc = file.add_calculation("INT x:[0, sqrt(2)]. sqrt(2 - x^2)")
        calc.perform_rule(rules.SubstitutionInverse("u", parser.parse_expr("sqrt(2) * sin(u)")))
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.OnLocation(rules.RewriteTrigonometric("TR5"), "1.0.1.0"))
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.ElimAbs())
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.OnLocation(rules.RewriteTrigonometric("TR7"), "1.0"))
        calc.perform_rule(rules.Substitution("v", parser.parse_expr("2 * u")))
        calc.perform_rule(rules.FullSimplify())
        self.assertEqual(str(calc.last_expr), "1/2 * pi")

        calc = file.add_calculation("INT y:[-sqrt(2), sqrt(2)]. sqrt(8 - 2*y^2)")
        calc.perform_rule(rules.SubstitutionInverse("u", parser.parse_expr("2 * sin(u)")))
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.OnLocation(rules.RewriteTrigonometric("TR5"), "1.0.1.0"))
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.ElimAbs())
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.OnLocation(rules.RewriteTrigonometric("TR7"), "1.0"))
        calc.perform_rule(rules.Substitution("v", parser.parse_expr("2 * u")))
        calc.perform_rule(rules.FullSimplify())
        self.assertEqual(str(calc.last_expr), "sqrt(2) * pi + 2 * sqrt(2)")

        calc = file.add_calculation("INT x:[1/sqrt(2), 1]. sqrt(1 - x^2) / x ^ 2")
        calc.perform_rule(rules.SubstitutionInverse("u", parser.parse_expr("sin(u)")))
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.OnLocation(rules.RewriteTrigonometric("TR5"), "0.1.0"))
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.ElimAbs())
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.OnLocation(rules.RewriteTrigonometric("TR6"), "0.0"))
        calc.perform_rule(rules.ExpandPolynomial())
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.OnLocation(rules.RewriteTrigonometric("TR111"), "0.0"))
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
        calc.perform_rule(rules.OnLocation(rules.Equation(parser.parse_expr("(x + 1) ^ 2 + 1")), "0.1"))
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
        calc.perform_rule(rules.OnLocation(rules.Equation(parser.parse_expr("(cos(x)^2)^2")), "0"))
        calc.perform_rule(rules.OnLocation(rules.RewriteTrigonometric("TR7"), "0.0"))
        calc.perform_rule(rules.ExpandPolynomial())
        calc.perform_rule(rules.Substitution("u", parser.parse_expr("2 * x")))
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.OnLocation(rules.RewriteTrigonometric("TR7"), "0.1.0"))
        calc.perform_rule(rules.Substitution("v", parser.parse_expr("2 * u")))
        calc.perform_rule(rules.FullSimplify())
        self.assertEqual(str(calc.last_expr), "3/8 * pi")

        calc = file.add_calculation("INT x:[-pi/2, pi/2]. sqrt(cos(x) - cos(x)^3)")
        calc.perform_rule(rules.OnLocation(rules.Equation(parser.parse_expr("cos(x) * (1 - cos(x)^2)")), "0.0"))
        calc.perform_rule(rules.OnLocation(rules.RewriteTrigonometric("TR6"), "0.0.1"))
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
        calc.perform_rule(rules.OnLocation(rules.RewriteTrigonometric("TR111"), "0"))
        calc.perform_rule(rules.IntegrationByParts(parser.parse_expr("x"), parser.parse_expr("-cot(x)")))
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.OnLocation(rules.RewriteTrigonometric("TR2"), "1.0"))
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
        calc.perform_rule(rules.OnLocation(rules.PolynomialDivision(), "0.1"))
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
        calc.perform_rule(rules.OnLocation(rules.RewriteTrigonometric("TR8"), "0.1"))
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
        calc.perform_rule(rules.OnLocation(rules.ExpandDefinition(Idef.eq), "0"))
        calc.perform_rule(rules.DerivIntExchange())
        calc.perform_rule(rules.FullSimplify())

        calc = proof.rhs_calc
        calc.perform_rule(rules.OnLocation(rules.ExpandDefinition(Idef.eq), "1"))
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
        calc.perform_rule(rules.OnLocation(rules.Equation(parser.parse_expr("b^-1 * (1 + u^2)^-1")), "1.0.0"))
        calc.perform_rule(rules.FullSimplify())

        # Induction case, LHS
        calc = proof_induct.lhs_calc
        calc.perform_rule(rules.ApplyEquation(Eq1.goal))
        calc.perform_rule(rules.OnLocation(rules.ApplyEquation("IH"), "1.0"))
        calc.perform_rule(rules.FullSimplify())

        # Induction step, RHS
        calc = proof_induct.rhs_calc
        calc.perform_rule(rules.OnLocation(rules.RewriteBinom(), "1"))
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
        calc.perform_rule(rules.OnLocation(
            rules.IntegrationByParts(parser.parse_expr("x^n"), parser.parse_expr("-exp(-x)")), "0"))
        calc.perform_rule(rules.FullSimplify())

        calc = proof.rhs_calc
        calc.perform_rule(rules.OnSubterm(rules.ExpandDefinition(gamma_def.eq)))
        calc.perform_rule(rules.OnLocation(rules.ElimInfInterval(), "1"))

        # Gamma function and factorial
        goal2 = compstate.Goal(parser.parse_expr("Gamma(n+1) = factorial(n)"))
        file.add_compstate(goal2)

        proof = goal2.proof_by_induction("n")
        proof_base = proof.base_case.proof_by_calculation()
        proof_induct = proof.induct_case.proof_by_calculation()

        calc = proof_base.lhs_calc
        calc.perform_rule(rules.ExpandDefinition(gamma_def.eq))
        calc.perform_rule(rules.ElimInfInterval())
        calc.perform_rule(rules.OnLocation(rules.Substitution("u", parser.parse_expr("-x")), "0"))
        calc.perform_rule(rules.FullSimplify())

        calc = proof_induct.lhs_calc
        calc.perform_rule(rules.ApplyEquation(goal1.goal, subMap={"n": parser.parse_expr("n + 1")}))
        calc.perform_rule(rules.OnSubterm(rules.ApplyEquation(goal2.goal)))
        calc.perform_rule(rules.RewriteFactorial())

        # Application
        goal3 = compstate.Calculation(parser.parse_expr("INT x:[0,oo]. exp(-x^3)"))
        file.add_calculation(goal3)
        goal3.perform_rule(rules.Substitution('y', parser.parse_expr('x^3')))
        goal3.perform_rule(rules.FullSimplify())
        goal3.perform_rule(rules.OnLocation(rules.ApplyEquation(gamma_def.eq, subMap={"n": parser.parse_expr('1/3')}), '1'))
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


if __name__ == "__main__":
    unittest.main()
