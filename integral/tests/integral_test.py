"""Overall test for integrals."""

import unittest

from logic import basic
from integral import compstate
from integral import rules
from integral import parser


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
        calc.perform_rule(rules.OnLocation(rules.ElimAbs(), "1"))
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
        calc.perform_rule(rules.OnLocation(rules.ElimAbs(), "1"))
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

        calc = file.add_calculation("INT x:[1,4]. 1/(1+sqrt(x))")
        calc.perform_rule(rules.Substitution("u", parser.parse_expr("sqrt(x)")))
        calc.perform_rule(rules.Substitution("v", parser.parse_expr("u + 1")))
        calc.perform_rule(rules.ExpandPolynomial())
        calc.perform_rule(rules.FullSimplify())
        self.assertEqual(str(calc.last_expr), "2 * log(2) - 2 * log(3) + 2")

        print(file)


if __name__ == "__main__":
    unittest.main()
