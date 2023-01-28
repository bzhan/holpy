"""Overall test for integrals."""

import unittest
import json

from integral import expr
from integral import compstate
from integral import rules
from integral import parser
from integral import conditions
from integral import context


class IntegralTest(unittest.TestCase):
    def checkAndOutput(self, file: compstate.CompFile, filename: str):
        # Test parsing of json file
        json_file = file.export()
        for i, item in enumerate(json_file['content']):
            self.assertEqual(compstate.parse_item(file, item).export(), file.content[i].export())

        # Test goals are finished
        for content in file.content:
            self.assertTrue(content.is_finished())

        # Output to file
        with open('integral/examples/' + filename + '.json', 'w', encoding='utf-8') as f:
            json.dump(file.export(), f, indent=4, ensure_ascii=False, sort_keys=True)

    def testStandard(self):
        ctx = context.Context()
        ctx.load_book("base")

        file = compstate.CompFile(ctx, "standard")

        goal1 = file.add_goal("(INT x. 1 / (x + a)) = log(abs(x + a))")
        proof = goal1.proof_by_calculation()
        calc = proof.lhs_calc
        calc.perform_rule(rules.Substitution("u", parser.parse_expr("x + a")))
        calc.perform_rule(rules.IndefiniteIntegralIdentity())
        calc.perform_rule(rules.ReplaceSubstitution())

        self.checkAndOutput(file, "standard")

    def testTongji(self):
        ctx = context.Context()
        file = compstate.CompFile(ctx, "Tongji")

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

        calc = file.add_calculation("INT x:[0, pi/2]. exp(2*x)*cos(x)")
        calc.perform_rule(rules.IntegrationByParts(parser.parse_expr("exp(2*x)"), parser.parse_expr("sin(x)")))
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.IntegrationByParts(parser.parse_expr("exp(2*x)"), parser.parse_expr("-cos(x)")))
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.IntegrateByEquation(parser.parse_expr("INT x:[0, pi/2]. exp(2*x)*cos(x)")))
        self.assertEqual(str(calc.last_expr), "1/5 * exp(pi) - 2/5")

        calc = file.add_calculation("INT x:[0,pi]. (x * sin(x))^2")
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

        calc = file.add_calculation("INT x:[1, exp(1)]. sin(log(x))")
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

        self.checkAndOutput(file, "tongji7")

    def testLHopital(self):
        ctx = context.Context()
        file = compstate.CompFile(ctx, "LHopital")

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

        self.checkAndOutput(file, "LHopital")

    def testWallis(self):
        ctx = context.Context()
        file = compstate.CompFile(ctx, 'Wallis')

        # Condition b > 0
        conds = conditions.Conditions()
        conds.add_condition(parser.parse_expr("b > 0"))

        # Make definition
        Idef = compstate.FuncDef(parser.parse_expr("I(m,b) = (INT x:[0,oo]. 1/(x^2+b)^(m+1))"), conds=conds)
        file.add_definition(Idef)

        # Prove the following equality
        Eq1 = file.add_goal("(D b. I(m,b)) = -(m+1) * I(m+1, b)", conds=["b > 0"])
        proof = Eq1.proof_by_calculation()

        calc = proof.lhs_calc
        calc.perform_rule(rules.OnSubterm(rules.ExpandDefinition(Idef.eq)))
        calc.perform_rule(rules.DerivIntExchange())
        calc.perform_rule(rules.FullSimplify())

        calc = proof.rhs_calc
        calc.perform_rule(rules.OnSubterm(rules.ExpandDefinition(Idef.eq)))
        calc.perform_rule(rules.FullSimplify())

        # Prove the following by induction
        Eq2 = file.add_goal("I(m,b) = pi / 2^(2*m+1) * binom(2*m, m) * (1/(b^((2*m+1)/2)))", conds=["b > 0"])
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
        calc.perform_rule(rules.OnSubterm(rules.ApplyEquation(
            parser.parse_expr("I(m,b) = pi / 2^(2*m+1) * binom(2*m, m) * (1/(b^((2*m+1)/2)))"))))
        calc.perform_rule(rules.FullSimplify())

        # Induction step, RHS
        calc = proof_induct.rhs_calc
        calc.perform_rule(rules.OnSubterm(rules.RewriteBinom()))
        calc.perform_rule(rules.FullSimplify())

        self.checkAndOutput(file, "wallis")

    def testGammaFunction(self):
        # Reference:
        # Inside interesting integrals, Section 4.1

        ctx = context.Context()
        file = compstate.CompFile(ctx, "GammaFunction")

        # Condition n > 0
        conds = conditions.Conditions()
        conds.add_condition(parser.parse_expr("n > 0"))

        # Definition of Gamma function
        gamma_def = compstate.FuncDef(parser.parse_expr("Gamma(n) = (INT x:[0,oo]. exp(-x) * x^(n-1))"), conds=conds)
        file.add_definition(gamma_def)

        # Recursive equation for gamma function
        goal1 = file.add_goal("Gamma(n+1) = n * Gamma(n)", conds=["n > 0"])

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
        goal2 = file.add_goal("Gamma(n+1) = factorial(n)")

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
        calc = file.add_calculation("INT x:[0,oo]. exp(-x^3)")
        calc.perform_rule(rules.Substitution('y', parser.parse_expr('x^3')))
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.OnSubterm(rules.ApplyEquation(gamma_def.eq, subMap={"n": parser.parse_expr('1/3')})))
        calc.perform_rule(rules.ApplyEquation(goal1.goal))
        calc.perform_rule(rules.FullSimplify())
        self.assertEqual(str(calc.last_expr), "Gamma(4/3)")

        self.checkAndOutput(file, "GammaFunction")

    def testTrick2a(self):
        # Reference:
        # Inside interesting integrals, Section 2.2, example 1
        ctx = context.Context()
        file = compstate.CompFile(ctx, "Trick2a")

        calc = file.add_calculation("INT x:[0,pi/2]. sqrt(sin(x)) / (sqrt(sin(x)) + sqrt(cos(x)))")
        calc.perform_rule(rules.Substitution("y", parser.parse_expr("pi / 2 - x")))
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.Equation(parser.parse_expr("1 - sqrt(sin(y)) / (sqrt(cos(y)) + sqrt(sin(y)))"),
                                         old_expr=parser.parse_expr("sqrt(cos(y)) * (sqrt(cos(y)) + sqrt(sin(y)))^-1")))
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.IntegrateByEquation(parser.parse_expr("INT x:[0,pi/2]. sqrt(sin(x)) / (sqrt(sin(x)) + sqrt(cos(x)))")))
        self.assertEqual(str(calc.last_expr), "1/4 * pi")

        self.checkAndOutput(file, "trick2a")

    def testTrick2b(self):
        # Reference:
        # Inside interesting integrals, Section 2.2, example 2
        ctx = context.Context()
        file = compstate.CompFile(ctx, "Trick2a")

        calc = file.add_calculation("INT x:[0,pi]. x * sin(x) / (1 + cos(x)^2)")
        calc.perform_rule(rules.Substitution("y", parser.parse_expr("pi - x")))
        calc.perform_rule(rules.ExpandPolynomial())
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.IntegrateByEquation(parser.parse_expr("INT x:[0,pi]. x * sin(x) / (1 + cos(x)^2)")))
        calc.perform_rule(rules.Substitution("u", parser.parse_expr("cos(y)")))
        calc.perform_rule(rules.FullSimplify())
        self.assertEqual(str(calc.last_expr), "1/4 * pi ^ 2")

        self.checkAndOutput(file, "trick2b")

    def testLeibniz01(self):
        # Reference
        # Inside interesting integrals, Section 3.1, example 1
        ctx = context.Context()
        file = compstate.CompFile(ctx, "Leibniz01")

        # Basic result: integral of 1 / (x^2 + a^2)
        goal1 = file.add_goal("(INT x:[0,oo]. 1 / (x^2 + a^2)) = pi / (2 * a)", conds=["a > 0"])

        proof = goal1.proof_by_calculation()
        calc = proof.lhs_calc
        calc.perform_rule(rules.ElimInfInterval())
        calc.perform_rule(rules.SubstitutionInverse("u", parser.parse_expr("a * u")))
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.Equation(old_expr=parser.parse_expr("(a ^ 2 * u ^ 2 + a ^ 2) ^ (-1)"),
                                         new_expr=parser.parse_expr("(u^2 + 1) ^ (-1) / (a ^ 2)")))
        calc.perform_rule(rules.FullSimplify())

        calc = proof.rhs_calc
        calc.perform_rule(rules.FullSimplify())

        # Derivate to get integral of 1 / (x^2 + a^2)^2
        goal2 = file.add_goal("(INT x:[0,oo]. 1 / (x^2 + a^2)^2) = pi / (4 * a^3)", conds=["a > 0"])
        proof = goal2.proof_by_rewrite_goal(begin=goal1)
        calc = proof.begin
        calc.perform_rule(rules.DerivEquation('a'))
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.MulEquation(parser.parse_expr("1 / (-2 * a)")))

        # Derivate again:
        goal3 = file.add_goal("(INT x:[0,oo]. 1 / (x^2 + a^2)^3) = 3*pi / (16 * a^5)", conds=["a > 0"])
        proof = goal3.proof_by_rewrite_goal(begin=goal2)
        calc = proof.begin
        calc.perform_rule(rules.DerivEquation('a'))
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.MulEquation(parser.parse_expr("1 / (-4 * a)")))

        self.checkAndOutput(file, "leibniz01")

    def testLeibniz02(self):
        # Reference
        # Inside interesting integrals, Section 3.1, example 2
        ctx = context.Context()
        file = compstate.CompFile(ctx, 'leibniz02')

        # Overall goal: (INT x:[-oo,oo]. exp(-(x^2)/2)) = sqrt(2*pi)

        # Make definition
        e = parser.parse_expr("g(t) = (INT x:[0,t].exp(-(x^2)/2))^2")
        Idef = compstate.FuncDef(e)
        file.add_definition(Idef)

        Eq1 = file.add_goal("(INT x:[-oo,oo]. exp(-x^2/2)) = 2 * LIM {t->oo}. sqrt(g(t))")
        Eq1_proof = Eq1.proof_by_calculation()
        calc = Eq1_proof.lhs_calc
        calc.perform_rule(rules.SplitRegion(expr.Const(0)))
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

        Eq2 = file.add_goal("(D t. g(t) + 2 * INT y:[0, 1].exp(-(1+y^2)*t^2/2)/(1+y^2)) = 0")
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

        Eq3 = file.add_goal("2 * (INT y:[0,1]. exp(1/2 * t ^ 2 * (-(y ^ 2) - 1)) * (y ^ 2 + 1) ^ -1) + g(t) = SKOLEM_FUNC(C(y))")
        Eq3_proof = Eq3.proof_by_rewrite_goal(begin=Eq2)
        calc = Eq3_proof.begin
        calc.perform_rule(rules.IntegralEquation(var = 't',left_skolem_name='E',right_skolem_name=None))
        calc.perform_rule(rules.OnLocation(rules.CommonIndefiniteIntegral(const_name='C'), '1'))
        calc.perform_rule(rules.FullSimplify())
        new_expr = parser.parse_expr("SKOLEM_FUNC(C(y))")
        calc.perform_rule(rules.RewriteSkolemConst(new_expr=new_expr))

        Eq4 = file.add_goal("g(0) = 0")
        proof_of_Eq4 = Eq4.proof_by_calculation()
        calc = proof_of_Eq4.lhs_calc
        calc.perform_rule(rules.ExpandDefinition(Idef.eq))
        calc.perform_rule(rules.FullSimplify())

        Eq5 = file.add_goal("pi/2 = SKOLEM_FUNC(C(y))")
        proof_of_Eq5 = Eq5.proof_by_rewrite_goal(begin = Eq3)
        calc = proof_of_Eq5.begin
        calc.perform_rule(rules.LimitEquation('t', expr.Const(0)))
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.OnLocation(rules.ApplyEquation(Eq4.goal), "0.0"))
        calc.perform_rule(rules.FullSimplify())

        Eq6 = file.add_goal("g(t) = -2 * (INT y:[0,1]. exp(1/2 * t ^ 2 * (-(y ^ 2) - 1)) * (y ^ 2 + 1) ^ -1) + 1/2 * pi")
        proof_of_Eq6 = Eq6.proof_by_calculation()
        calc = proof_of_Eq6.lhs_calc
        calc.perform_rule(rules.ApplyEquation(Eq3.goal))
        calc.perform_rule(rules.OnLocation(rules.ApplyEquation(Eq5.goal), '0'))
        calc.perform_rule(rules.FullSimplify())

        Eq7 = file.add_goal("(INT x:[-oo,oo]. exp(-x^2/2)) = sqrt(2*pi)", conds=["y^2 + 1 > 0"])
        proof_of_Eq7 = Eq7.proof_by_calculation()
        calc = proof_of_Eq7.lhs_calc
        calc.perform_rule(rules.ApplyEquation(Eq1.goal))
        calc.perform_rule(rules.OnSubterm(rules.ApplyEquation(Eq6.goal)))
        calc.perform_rule(rules.OnLocation(rules.LimFunExchange(), '1'))
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.OnLocation(rules.LimIntExchange(), '1.0.0.1'))
        old_expr = parser.parse_expr("1/2 * t ^ 2 * (-(y ^ 2) - 1)")
        new_expr = parser.parse_expr("-1/2 * t^2 * (y^2+1)")
        calc.perform_rule(rules.Equation(old_expr=old_expr,new_expr=new_expr))
        calc.perform_rule(rules.FullSimplify())
        calc = proof_of_Eq7.rhs_calc
        calc.perform_rule(rules.FullSimplify())

        self.checkAndOutput(file, "leibniz02")

    def testLeibniz03(self):
        # Reference:
        # Inside interesting integrals, Section 3.1, example #3

        # Overall goal: INT x:[0,oo]. cos(tx)*exp(-(x^2)/2) = sqrt(pi/2)*exp(-(t^2)/2)

        # Initial state
        ctx = context.Context()
        file = compstate.CompFile(ctx, 'Leibniz03')

        # Make definition
        e = parser.parse_expr("I(t) = INT x:[0, oo]. cos(t*x)*exp(-(x^2)/2)")
        Idef = compstate.FuncDef(e)
        file.add_definition(Idef)

        e = parser.parse_expr('I(0) = sqrt(pi/2)')
        lemma1 = compstate.Lemma(e)
        file.add_lemma(lemma1)

        # Prove the following equality
        Eq1 = file.add_goal("(D t. I(t)) = -t*I(t)")
        Eq1_proof = Eq1.proof_by_calculation()
        calc = Eq1_proof.lhs_calc
        calc.perform_rule(rules.OnLocation(rules.ExpandDefinition(Idef.eq), '0'))
        calc.perform_rule(rules.OnLocation(rules.ElimInfInterval(new_var='u'), '0'))
        calc.perform_rule(rules.FullSimplify())
        u = parser.parse_expr('sin(t*x)')
        v = parser.parse_expr('-exp(-x^2/2)')
        calc.perform_rule(rules.OnLocation(rules.IntegrationByParts(u, v), '0.0'))
        calc.perform_rule(rules.FullSimplify())

        calc = Eq1_proof.rhs_calc
        calc.perform_rule(rules.OnLocation(rules.ExpandDefinition(Idef.eq), '1'))
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.OnLocation(rules.ElimInfInterval(new_var='u'), '0.1'))

        Eq2 = file.add_goal("(D t. log(I(t)) + t^2/2) = 0")
        Eq2_proof = Eq2.proof_by_calculation()
        calc = Eq2_proof.lhs_calc
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.OnLocation(rules.ApplyEquation(Eq1.goal), '0.1'))
        calc.perform_rule(rules.FullSimplify())

        Eq3 = file.add_goal("1/2 * t ^ 2 + log(I(t)) = SKOLEM_CONST(C)")
        Eq3_proof = Eq3.proof_by_rewrite_goal(begin=Eq2)
        calc = Eq3_proof.begin
        calc.perform_rule(rules.IntegralEquation(var='t', left_skolem_name='E', right_skolem_name=None))
        calc.perform_rule(rules.OnLocation(rules.CommonIndefiniteIntegral(const_name='C'), '1'))
        new_expr = parser.parse_expr("SKOLEM_CONST(C)")
        calc.perform_rule(rules.RewriteSkolemConst(new_expr=new_expr))

        Eq4 = file.add_goal("log(sqrt(pi / 2)) = SKOLEM_CONST(C)")
        Eq4_proof = Eq4.proof_by_rewrite_goal(begin=Eq3)
        calc = Eq4_proof.begin
        calc.perform_rule(rules.LimitEquation('t', expr.Const(0)))
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.OnLocation(rules.ApplyLemma(lemma=lemma1.lemma, conds=None), '0.0'))

        Eq5 = file.add_goal("log(I(t)) = -t ^ 2 / 2 + log(sqrt(pi / 2))")
        Eq5_proof = Eq5.proof_by_calculation()
        calc = Eq5_proof.lhs_calc
        calc.perform_rule(rules.ApplyEquation(Eq3.goal))
        calc.perform_rule(rules.OnLocation(rules.ApplyEquation(Eq4.goal), '0'))
        calc.perform_rule(rules.FullSimplify())
        calc = Eq5_proof.rhs_calc
        calc.perform_rule(rules.FullSimplify())

        Eq6 = file.add_goal("I(t) = sqrt(pi/2) * exp(-t^2/2)")
        Eq6_proof = Eq6.proof_by_rewrite_goal(begin=Eq5)
        calc = Eq6_proof.begin
        calc.perform_rule(rules.ExpEquation())
        calc.perform_rule(rules.OnLocation(rules.RewriteExp(), '1'))
        calc.perform_rule(rules.FullSimplify())

        self.checkAndOutput(file, "leibniz03")

    def testEulerLogSineIntegral(self):
        # Reference:
        # Inside interesting integrals, Section 2.4
        ctx = context.Context()
        file = compstate.CompFile(ctx, "EulerLogSine")

        # Define I(a)
        e = parser.parse_expr('I(a) = INT x:[0,pi/2]. log(a * sin(x))')
        Idef1 = compstate.FuncDef(e)
        file.add_definition(Idef1)

        # Define J(a)
        e = parser.parse_expr('J(a) = INT x:[0,pi/2]. log(a * sin(2*x))')
        Idef2 = compstate.FuncDef(e)
        file.add_definition(Idef2)

        # Prove J(a) = I(a)
        goal1 = file.add_goal("J(a) = I(a)")
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
        goal2 = file.add_goal("J(a) = pi/2 * log(2/a) + 2 * I(a)")
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
        goal3 = file.add_goal("I(a) = pi/2 * log(a/2)")
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

        self.checkAndOutput(file, "euler_log_sin")

    def testDirichletIntegral(self):
        # Reference:
        # Inside interesting integrals, Section 3.2
        ctx = context.Context()
        file = compstate.CompFile(ctx, "DirichletIntegral")

        # Define I(b)
        e = parser.parse_expr('I(b) = INT x:[0,oo]. sin(x) / x * exp(-b * x)')
        conds = conditions.Conditions()
        conds.add_condition(parser.parse_expr("b >= 0"))
        Idef = compstate.FuncDef(e, conds=conds)
        file.add_definition(Idef)

        e = parser.parse_expr("I(0) = SKOLEM_CONST(C)")
        lemma1 = compstate.Lemma(e)
        file.add_lemma(lemma1)

        e = parser.parse_expr("(INT x:[0,oo]. exp(-(b * x)) * sin(x)) = 1/(b^2+1)")  # for b > 0
        conds_of_lemma2 = compstate.Conditions()
        e2 = parser.parse_expr("b > 0")
        conds_of_lemma2.add_condition(e2)
        lemma2 = compstate.Lemma(e, conds_of_lemma2)
        file.add_lemma(lemma2)

        e = parser.parse_expr("(LIM {b -> oo}. INT x:[0,oo]. x ^ -1 * exp(-(b * x)) * sin(x)) = 0")
        lemma3 = compstate.Lemma(e)
        file.add_lemma(lemma3)

        # goal: D b. I(b) = -1/(b^2+1)
        goal1 = file.add_goal("(D b. I(b)) = -1/(b^2+1)", conds=["b > 0"])
        proof = goal1.proof_by_calculation()
        calc = proof.lhs_calc
        calc.perform_rule(rules.OnSubterm(rules.ExpandDefinition(Idef.eq)))
        calc.perform_rule(rules.DerivIntExchange())
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.OnLocation(rules.ApplyLemma(lemma2.lemma, lemma2.conds), '0'))
        calc.perform_rule(rules.FullSimplify())
        calc = proof.rhs_calc
        calc.perform_rule(rules.FullSimplify())

        # goal: I(0) = INT x:[0, oo]. sin(x) / x
        goal2 = file.add_goal("I(0) = INT x:[0, oo]. sin(x) / x")
        proof = goal2.proof_by_calculation()
        calc = proof.lhs_calc
        # need to check whether 0 is satisfied the condition of b
        calc.perform_rule(rules.ExpandDefinition(Idef.eq))
        calc = proof.rhs_calc
        calc.perform_rule(rules.FullSimplify())

        # goal: I(b) = -atan(b) + C for C is some constant
        goal3 = file.add_goal("I(b) = -atan(b) + SKOLEM_CONST(C)", conds=["b >= 0"])
        proof = goal3.proof_by_case("b = 0")

        case_1_proof = proof.case_1.proof_by_calculation()
        calc = case_1_proof.lhs_calc
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.ApplyLemma(lemma1.lemma,lemma1.conds))
        calc = case_1_proof.rhs_calc
        calc.perform_rule(rules.FullSimplify())

        case_2_proof = proof.case_2.proof_by_rewrite_goal(begin=goal1)
        calc = case_2_proof.begin
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.IntegralEquation(var='b', left_skolem_name='E', right_skolem_name=None))
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.OnLocation(rules.CommonIndefiniteIntegral('C'), '1.0'))
        new_expr = parser.parse_expr("SKOLEM_CONST(C)")
        calc.perform_rule(rules.RewriteSkolemConst(new_expr=new_expr))

        goal4 = file.add_goal("0 = (INT x:[0,oo]. x ^ -1 * sin(x)) - 1/2 * pi")
        proof_of_goal4 = goal4.proof_by_rewrite_goal(begin=goal3)
        calc = proof_of_goal4.begin
        calc.perform_rule(rules.OnLocation(rules.ApplyLemma(lemma1.lemma, lemma1.conds), '1.1'))
        calc.perform_rule(rules.LimitEquation(var='b', lim=expr.POS_INF))
        calc.perform_rule(rules.OnSubterm(rules.ExpandDefinition(Idef.eq)))
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.OnLocation(rules.ApplyEquation(lemma3.lemma), '0'))

        goal5 = file.add_goal("(INT x:[0,oo]. x ^ -1 * sin(x)) = 1/2 * pi")
        proof_of_goal5 = goal5.proof_by_calculation()
        calc = proof_of_goal5.lhs_calc
        calc.perform_rule(rules.ApplyEquation(goal4.goal))
        calc.perform_rule(rules.FullSimplify())

        self.checkAndOutput(file, "dirichletIntegral")

    def testFlipside03(self):
        # Reference:
        # Inside interesting integrals, Section 3.4, example #3

        # goal: INT x:[0, 1]. (x ^ a - 1) / log(x) = log(a + 1)
        ctx = context.Context()
        file = compstate.CompFile(ctx, "Flipside03")

        # introduce definition
        e = parser.parse_expr("I(a) = INT x:[0, 1]. (x ^ a - 1) / log(x)")
        conds = compstate.Conditions()
        conds.add_condition(parser.parse_expr("a>=0"))
        Idef = compstate.FuncDef(e, conds)
        file.add_definition(Idef)

        # verify the following equation: D a. I(a) = 1/(a+1)
        goal1 = file.add_goal("(D a. I(a)) = 1/(a+1)", conds=["a >= 0"])
        proof_of_goal1 = goal1.proof_by_calculation()
        calc = proof_of_goal1.lhs_calc
        calc.perform_rule(rules.OnSubterm(rules.ExpandDefinition(Idef.eq)))
        calc.perform_rule(rules.DerivIntExchange())
        calc.perform_rule(rules.FullSimplify())
        calc = proof_of_goal1.rhs_calc
        calc.perform_rule(rules.FullSimplify())

        # verify the following equation: I(a) = log(a+1)
        goal2 = file.add_goal("I(0) = 0")
        proof_of_goal2 = goal2.proof_by_calculation()
        calc = proof_of_goal2.lhs_calc
        calc.perform_rule(rules.OnSubterm(rules.ExpandDefinition(Idef.eq)))
        calc.perform_rule(rules.FullSimplify())

        goal3 = file.add_goal("I(a) = log(a+1) + SKOLEM_CONST(C)", conds=["a >= 0"])
        proof_of_goal3 = goal3.proof_by_rewrite_goal(begin=goal1)
        calc = proof_of_goal3.begin
        calc.perform_rule(rules.IntegralEquation(var='a', left_skolem_name='E', right_skolem_name=None))
        calc.perform_rule(rules.OnLocation(rules.CommonIndefiniteIntegral('C'), '1'))
        calc.perform_rule(rules.OnSubterm(rules.ElimAbs()))
        new_expr = parser.parse_expr("SKOLEM_CONST(C)")
        calc.perform_rule(rules.RewriteSkolemConst(new_expr=new_expr))

        goal4 = file.add_goal("0 = SKOLEM_CONST(C)")
        proof_of_goal4 = goal4.proof_by_rewrite_goal(begin=goal3)
        calc = proof_of_goal4.begin
        calc.perform_rule(rules.VarSubsOfEquation('a', expr.Const(0)))
        calc.perform_rule(rules.OnLocation(rules.ApplyEquation(goal2.goal), '0'))
        calc.perform_rule(rules.FullSimplify())

        goal5 = file.add_goal("I(a) = log(a+1)", conds=["a >= 0"])
        proof_of_goal5 = goal5.proof_by_calculation()
        calc = proof_of_goal5.lhs_calc
        calc.perform_rule(rules.ApplyEquation(goal3.goal))
        # didn't check condition about goal4
        calc.perform_rule(rules.OnLocation(rules.ApplyEquation(goal4.goal), '1'))
        calc.perform_rule(rules.FullSimplify())

        self.checkAndOutput(file, "flipside03")

    def testFrullaniIntegral(self):
        # Reference:
        # Inside interesting integrals, Section 3.3

        ctx = context.Context()
        file = compstate.CompFile(ctx, "Frullani Integral")

        # Define I(a, b)
        e = parser.parse_expr("I(a, b) = INT x:[0,oo]. (atan(a*x) - atan(b*x))/x")
        conds_of_Idef = compstate.Conditions()
        e2 = parser.parse_expr("a > 0")
        conds_of_Idef.add_condition(e2)
        e2 = parser.parse_expr("b > 0")
        conds_of_Idef.add_condition(e2)
        Idef = compstate.FuncDef(e, conds_of_Idef)
        file.add_definition(Idef)

        # Show I(a, a) = 0
        goal1 = file.add_goal("I(a, a) = 0")
        proof_of_goal1 = goal1.proof_by_calculation()
        calc = proof_of_goal1.lhs_calc
        calc.perform_rule(rules.ExpandDefinition(Idef.eq))
        calc.perform_rule(rules.FullSimplify())

        # Evalute D a. I(a, b) for a > 0
        goal2 = file.add_goal("(D a. I(a,b)) = pi / (2*a)", conds=["a > 0"])
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
        goal3 = file.add_goal("I(a,b) = 1/2 * pi * log(a) - SKOLEM_FUNC(C(b))", conds=["a > 0"])
        proof_of_goal3 = goal3.proof_by_rewrite_goal(begin=goal2)
        calc = proof_of_goal3.begin
        calc.perform_rule(rules.IntegralEquation(var='a', left_skolem_name='E', right_skolem_name=None))
        calc.perform_rule(rules.OnLocation(rules.FullSimplify(), '1'))
        calc.perform_rule(rules.OnSubterm(rules.CommonIndefiniteIntegral(const_name='C')))
        calc.perform_rule(rules.OnLocation(rules.ExpandPolynomial(), '1'))
        new_expr = parser.parse_expr("-SKOLEM_FUNC(C(b))")
        calc.perform_rule(rules.RewriteSkolemConst(new_expr = new_expr))
        calc.perform_rule(rules.OnSubterm(rules.ElimAbs()))
        calc.perform_rule(rules.FullSimplify())

        # Special case I(a,a)
        goal4 = file.add_goal("I(a,a) = 1/2 * pi * log(a) - SKOLEM_FUNC(C(a))", conds=["a > 0"])
        proof_of_goal4 = goal4.proof_by_calculation()
        calc = proof_of_goal4.lhs_calc
        calc.perform_rule(rules.ExpandDefinition(goal3.goal))

        # Obtain value of Skolem function
        goal5 = file.add_goal("SKOLEM_FUNC(C(a)) = 1/2 * pi * log(a)", conds=["a > 0"])
        proof_of_goal5 = goal5.proof_by_calculation()
        calc = proof_of_goal5.lhs_calc
        calc.perform_rule(rules.ApplyEquation(goal4.goal))
        calc.perform_rule(rules.OnSubterm(rules.ApplyEquation(goal1.goal)))
        calc.perform_rule(rules.FullSimplify())

        # Final result
        goal6 = file.add_goal("I(a, b) = 1/2 * pi * log(a) - 1/2 * pi * log(b)", conds=["a > 0", "b > 0"])
        proof_of_goal6 = goal6.proof_by_calculation()
        calc = proof_of_goal6.lhs_calc
        calc.perform_rule(rules.ApplyEquation(goal3.goal))
        calc.perform_rule(rules.OnSubterm(rules.ExpandDefinition(goal5.goal)))

        self.checkAndOutput(file, "FrullaniIntegral")

    def testCatalanConstant01(self):
        # Reference:
        # Inside interesting integrals, Section 5.1, example #1

        ctx = context.Context()
        file = compstate.CompFile(ctx, 'CatalanConstant01')

        # Define Catalan's constant
        e = parser.parse_expr('G = SUM(n, 0, oo, (-1)^n / (2*n+1)^2)')
        Gdef = compstate.FuncDef(e)
        file.add_definition(Gdef)

        # Evaluate integral of atan(x) / x
        goal = file.add_goal("(INT x:[0, 1]. atan(x) / x) = G")
        proof_of_goal = goal.proof_by_calculation()
        calc = proof_of_goal.lhs_calc
        calc.perform_rule(rules.OnLocation(rules.ExpandSeries(), '0.0'))
        old_expr = parser.parse_expr("x ^ (2 * n + 1)")
        new_expr = parser.parse_expr("x^ (2*n) * x")
        calc.perform_rule(rules.Equation(old_expr=old_expr, new_expr=new_expr))
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.IntSumExchange())
        calc.perform_rule(rules.FullSimplify())
        calc = proof_of_goal.rhs_calc
        calc.perform_rule(rules.ApplyEquation(Gdef.eq))
        calc.perform_rule(rules.FullSimplify())

        self.checkAndOutput(file, "CatalanConstant01")

    def testCatalanConstant02(self):
        # Reference:
        # Inside interesting integrals, Section 5.1, example #2

        ctx = context.Context()
        file = compstate.CompFile(ctx, 'CatalanConstant02')

        # Define Catalan's constant
        e = parser.parse_expr('G = SUM(n, 0, oo, (-1)^n / (2*n+1)^2)')
        Gdef = compstate.FuncDef(e)
        file.add_definition(Gdef)

        # Define I(k)
        e = parser.parse_expr("I(k) = INT x:[1,oo]. log(x) / (x^k)")
        conds_of_Idef = compstate.Conditions()
        e2 = parser.parse_expr("k > 1")
        conds_of_Idef.add_condition(e2)
        Idef = compstate.FuncDef(e, conds=conds_of_Idef)
        file.add_definition(Idef)

        # Evaluate I(k)
        goal1 = file.add_goal("I(k) = 1/(k-1)^2", conds=["k > 1"])
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
        goal2 = file.add_goal("I(2 * n + 2) = 1/(2*n+1)^2")
        proof_of_goal2 = goal2.proof_by_calculation()
        calc = proof_of_goal2.lhs_calc
        calc.perform_rule(rules.ExpandDefinition(goal1.goal))
        calc = proof_of_goal2.rhs_calc
        calc.perform_rule(rules.FullSimplify())

        # Definition of I(2*n+2)
        goal3 = file.add_goal("I(2*n+2) = INT x:[1,oo]. log(x) / (x^(2*n+2))")
        proof_of_goal3 = goal3.proof_by_calculation()
        calc = proof_of_goal3.lhs_calc
        calc.perform_rule(rules.ExpandDefinition(Idef.eq))
        calc = proof_of_goal3.rhs_calc
        calc.perform_rule(rules.FullSimplify())

        # Combine previous two results
        # TODO: can simplify these three parts
        goal4 = file.add_goal("(INT x:[1,oo]. log(x) / x^(2*n+2)) = 1/(2*n+1)^2")
        proof_of_goal4 = goal4.proof_by_calculation()
        calc = proof_of_goal4.lhs_calc
        calc.perform_rule(rules.FullSimplify())
        calc = proof_of_goal4.rhs_calc
        calc.perform_rule(rules.ApplyEquation(goal2.goal))
        calc.perform_rule(rules.ApplyEquation(goal3.goal))
        calc.perform_rule(rules.FullSimplify())

        goal5 = file.add_goal("(INT x:[1,oo]. log(x) / (x^2+1)) = G")
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

        self.checkAndOutput(file, "CatalanConstant02")

    def testLogFunction01(self):
        # Reference:
        # Inside interesting integrals, Section 5.2, example #1

        ctx = context.Context()
        file = compstate.CompFile(ctx, "LogFunction01")

        # Series expansion for log(1+x)
        # TODO: add derivation
        conds_of_goal1 = compstate.Conditions()
        e = parser.parse_expr("abs(x) < 1")
        conds_of_goal1.add_condition(e)
        e = parser.parse_expr("log(1+x) = SUM(k,0,oo,(-1)^k * (x^(k+1))/(k+1))")
        goal1 = compstate.Lemma(lemma=e, conds=conds_of_goal1)
        file.add_lemma(goal1)

        # Series sum for alternating reciprocal of squares
        # TODO: add derivation
        e = parser.parse_expr("SUM(k,0,oo,(-1)^k * (k+1)^(-2))  = (pi^2) / 12")
        goal2 = compstate.Lemma(lemma=e)
        file.add_lemma(goal2)

        # Main result
        goal = file.add_goal("(INT x:[0,1]. log(x+1) / x) = (pi^2) / 12")
        proof_of_goal01 = goal.proof_by_calculation()
        calc = proof_of_goal01.lhs_calc

        # TODO: condition check
        # the domain of x is (0, 1), so the condition abs(x) < 1 is satisfied
        calc.perform_rule(rules.OnSubterm(rules.ApplyLemma(lemma=goal1.lemma)))
        old_expr = parser.parse_expr("SUM(k,0,oo,(-1) ^ k * x ^ (k + 1) / (k + 1)) / x")
        new_expr = parser.parse_expr("SUM(k,0,oo,(-1) ^ k * x ^ (k + 1) / (k + 1) * (1/x))")
        calc.perform_rule(rules.Equation(old_expr=old_expr, new_expr=new_expr))
        calc.perform_rule(rules.IntSumExchange())
        calc.perform_rule(rules.FullSimplify())

        calc.perform_rule(rules.ApplyLemma(lemma=goal2.lemma))
        calc.perform_rule(rules.FullSimplify())
        calc = proof_of_goal01.rhs_calc
        calc.perform_rule(rules.FullSimplify())

        self.checkAndOutput(file, "LogFunction01")

    def testLogFunction02(self):
        # Reference:
        # Inside interesting integrals, Section 5.2, example #2

        ctx = context.Context()
        file = compstate.CompFile(ctx, 'LogFunction02')

        conds_of_lemma01 = compstate.Conditions()
        e = parser.parse_expr("abs(x) < 1")
        conds_of_lemma01.add_condition(e)
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

        goal01 = file.add_goal("-log(1-x) - log(1+x) = \
                -SUM(k,0,oo,(-1)^k*(-x)^(k+1) / (k+1))-SUM(k,0,oo,(-1)^k*x^(k+1)/(k+1))", conds=["abs(x) < 1"])
        proof_of_goal01 = goal01.proof_by_calculation()
        calc = proof_of_goal01.lhs_calc
        calc.perform_rule(rules.OnSubterm(rules.ExpandSeries(index_var='k')))
        calc.perform_rule(rules.FullSimplify())
        calc = proof_of_goal01.rhs_calc
        calc.perform_rule(rules.FullSimplify())

        goal02 = file.add_goal("x * (-(x ^ 2) + 1) ^ (-1) = \
                1/2 * SUM(k, 0, oo, (-1) ^ k * (-x) ^ k) - 1/2 * SUM(k, 0, oo, x ^ k * (-1) ^ k)")
        proof_of_goal02 = goal02.proof_by_rewrite_goal(begin = goal01)
        calc = proof_of_goal02.begin

        calc.perform_rule(rules.DerivEquation('x'))
        calc.perform_rule(rules.FullSimplify())
        old_expr = parser.parse_expr("(-x + 1) ^ (-1) - (x + 1) ^ (-1)")
        new_expr = parser.parse_expr("2 * (x / (1-x^2))")
        calc.perform_rule(rules.Equation(new_expr=new_expr, old_expr=old_expr))
        e = parser.parse_expr('1/2')
        calc.perform_rule(rules.MulEquation(e = e))

        goal03 = file.add_goal("(INT x:[0, pi/2]. cos(x)/sin(x) * log(1/cos(x))) = pi^2/24")
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

        self.checkAndOutput(file, "LogFunction02")

    def testBernoulliIntegral(self):
        # Reference:
        # Inside interesting integrals, Section 6.1

        ctx = context.Context()
        file = compstate.CompFile(ctx, "Bernoulli's Integral")

        e = parser.parse_expr("f(m, n) = INT x:[0, 1]. x^m * log(x) ^ n")
        Idef = compstate.FuncDef(e)
        file.add_definition(Idef)

        e = parser.parse_expr("f(m, n) = (-1)^n * factorial(n) / (m+1) ^ (n+1)")
        lemma = compstate.Lemma(lemma=e, conds=None)
        file.add_lemma(lemma)

        goal01 = file.add_goal("f(a*k, k) = INT x:[0, 1]. x^(a*k) * log(x)^k")
        proof_of_goal01 = goal01.proof_by_calculation()
        calc = proof_of_goal01.lhs_calc
        calc.perform_rule(rules.ExpandDefinition(Idef.eq))

        goal02 = file.add_goal("(INT x:[0,1]. x^(c*x^a)) = SUM(k,0,oo,(-c)^k / (k*a+1)^(k+1))")
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

        self.checkAndOutput(file, "BernoulliIntegral")

    def testAhmedIntegral(self):
        # Reference:
        # Inside interesting integrals, Section 6.2

        ctx = context.Context()
        file = compstate.CompFile(ctx, "Ahmed Integral")

        conds_of_Idef = compstate.Conditions()
        e = parser.parse_expr("u>0")
        conds_of_Idef.add_condition(e)

        s = "I(u) = (INT x:[0,1]. atan(u * sqrt(2+x*x)) / ((1+x*x)*sqrt(2+x*x)))"
        e = parser.parse_expr(s)

        Idef = compstate.FuncDef(eq=e, conds=conds_of_Idef)
        file.add_definition(Idef)

        e = "atan(sqrt(x ^ 2 + 2) ^ (-1)) = pi/2 - atan(sqrt(x^2+2))"
        lemma01 = compstate.Lemma(lemma=parser.parse_expr(e))
        file.add_lemma(lemma01)

        goal001 = file.add_goal("I(1) = INT x:[0,1]. (x ^ 2 + 1) ^ (-1) * (x ^ 2 + 2) ^ (-1/2) * atan(sqrt(x ^ 2 + 2))")
        proof = goal001.proof_by_calculation()
        calc = proof.lhs_calc
        calc.perform_rule(rules.ExpandDefinition(Idef.eq))
        calc.perform_rule(rules.FullSimplify())

        goal002 = file.add_goal("(LIM {u->oo}. I(u)) = \
                1/2 * pi * (INT x:[0,1]. (x ^ 2 + 1) ^ (-1) * (x ^ 2 + 2) ^ (-1/2))", conds=["u > 0"])
        proof = goal002.proof_by_calculation()
        calc = proof.lhs_calc
        calc.perform_rule(rules.OnSubterm(rules.ExpandDefinition(Idef.eq)))
        calc.perform_rule(rules.LimIntExchange())
        calc.perform_rule(rules.FullSimplify())

        goal01 = file.add_goal("(LIM {u->oo}. I(u)) = pi^2 / 12")
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

        goal02 = file.add_goal("(D u. I(u)) = \
                (1+u^2)^(-1) * (pi/4 - u * sqrt(1+2*u^2)^(-1)*atan(u/sqrt(1+2*u^2)))", conds=["u > 0"])
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

        goal03 = file.add_goal("(INT u:[1, oo]. D u. I(u)) = pi^2/12 - I(1)")
        proof = goal03.proof_by_calculation()
        calc = proof.lhs_calc
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.OnSubterm(rules.ApplyEquation(eq=goal01.goal)))
        calc.perform_rule(rules.FullSimplify())
        calc = proof.rhs_calc
        calc.perform_rule(rules.FullSimplify())

        goal04 = file.add_goal("(INT u:[1,oo]. D u. I(u)) = - (pi^2 / 48) + I(1)")
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

        goal05 = file.add_goal("I(1) = 5*pi^2/96")
        proof_of_goal05 = goal05.proof_by_rewrite_goal(begin=goal03)
        calc = proof_of_goal05.begin
        calc.perform_rule(rules.OnLocation(rules.ApplyEquation(eq=goal04.goal), '0'))
        calc.perform_rule(rules.SolveEquation(parser.parse_expr("I(1)")))

        self.checkAndOutput(file, "AhmedIntegral")


if __name__ == "__main__":
    unittest.main()
