"""Unit test for conditions"""

import unittest

from integral import parser
from integral.conditions import Conditions
from integral import conditions


class ConditionsTest(unittest.TestCase):
    def testIsPositive(self):
        test_data = [
            ("a", "a > 0"),
            ("a ^ (1/2)", "a > 0"),
            ("a ^ (-1/2)", "a > 0"),
            ("m + 1", "m >= 0"),
        ]

        for a, b in test_data:
            e = parser.parse_expr(a)
            cond = parser.parse_expr(b)
            conds = Conditions()
            conds.add_condition("1", cond)
            self.assertTrue(conditions.is_positive(e, conds))


if __name__ == "__main__":
    unittest.main()
