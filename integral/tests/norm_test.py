import unittest

from integral import expr
from integral.parser import parse_expr
from integral import norm
from integral.norm import eq_power, eq_quotient, normalize_exp

class NormalizeTest(unittest.TestCase):
    def testQuotientNormalize(self):
        test_data = [
            "(x ^ 2 + 2) ^ (-1)",
            "x ^ 2 * (x ^ 2 + 2) ^ (-1)",
            "x ^ 2 * (x ^ 2 + 2) ^ (-1) + 1",
            "(x ^ 2 * (x ^ 2 + 2) ^ (-1) + 1) ^ (-1)",
            "(-(x ^ 2 * (x ^ 2 + 2) ^ (-1/2)) + sqrt(x ^ 2 + 2))",
            "(x ^ 2 * (x ^ 2 + 2) ^ (-1) + 1) ^ (-1) * (-(x ^ 2 * (x ^ 2 + 2) ^ (-1/2)) + sqrt(x ^ 2 + 2))",
        ]

        for t in test_data:
            t = parse_expr(t)
            print(t)
            print(norm.normalize_quotient(t))

    def testNormalize(self):
        test_data = [
            ("(x ^ 2 + 2) ^ (-1) * (x ^ 2 * (x ^ 2 + 2) ^ (-1) + 1) ^ (-1) * (-(x ^ 2 * (x ^ 2 + 2) ^ (-1/2)) + sqrt(x ^ 2 + 2))",
             "(x ^ 2 + 1) ^ (-1) * (x ^ 2 + 2) ^ (-1/2)"),
        ]

        for s, t in test_data:
            s = parse_expr(s)
            t = parse_expr(t)
            self.assertTrue(eq_quotient(s, t))

    def testNormalizeExp(self):
        test_data = [
            ("exp(-(log(2) / 2) + log(pi) / 2 - 1/2 * t ^ 2)", "1")
        ]

        for s, t in test_data:
            s = parse_expr(s)
            self.assertEqual(str(normalize_exp(s)), t)


if __name__ == "__main__":
    unittest.main()
