"""Unit test for rules."""

import unittest

from integral import parser
from integral import rules


class RulesTest(unittest.TestCase):
    def testLinearity(self):
        test_data = [
            ("INT x:[a,b]. 1 + 2 * x + x ^ 2",
             "(INT x:[a,b]. 1) + 2 * (INT x:[a,b]. x) + (INT x:[a,b]. x ^ 2)")
        ]

        rule = rules.Linearity()
        for s, s2 in test_data:
            s = parser.parse_expr(s)
            s2 = parser.parse_expr(s2)
            self.assertEqual(rule.eval(s), s2)

    def testCommonIntegral(self):
        test_data = [
            ("INT x:[a,b]. 1", "[x]_x=a,b"),
            ("INT x:[a,b]. 2", "[2 * x]_x=a,b"),
            ("INT x:[a,b]. x", "[x ^ 2 / 2]_x=a,b"),
            ("INT x:[a,b]. x ^ 2", "[x ^ 3 / 3]_x=a,b"),
            ("INT x:[a,b]. x ^ 3", "[x ^ 4 / 4]_x=a,b"),
        ]

        rule = rules.CommonIntegral()
        for s, s2 in test_data:
            s = parser.parse_expr(s)
            s2 = parser.parse_expr(s2)
            self.assertEqual(rule.eval(s), s2)


if __name__ == "__main__":
    unittest.main()
