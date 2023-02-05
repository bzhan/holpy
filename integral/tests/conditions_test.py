"""Unit test for conditions"""

import unittest

from integral import parser
from integral.conditions import Conditions


class ConditionsTest(unittest.TestCase):
    def testIsPositive(self):
        test_data = [
            # Constant
            ("1", [], True),

            # Variable
            ("a", ["a > 0"], True),

            # Function
            ("exp(a)", [], True),
            ("sqrt(a)", ["a > 0"], True),
            ("sqrt(a)", ["a >= 0"], False),

            # Power
            ("a ^ (1/2)", ["a > 0"], True),
            ("a ^ (-1/2)", ["a > 0"], True),

            # Plus
            ("m + 1", ["m >= 0"], True),
            ("1 + x ^ 2", [], True),

            # Integrals
            ("INT x:[1,oo]. 1 / x ^ 2", [], True),
            ("INT x:[0,oo]. exp(-1/2 * x ^ 2)", [], True),
        ]

        for a, conds_str, res in test_data:
            e = parser.parse_expr(a)
            conds = Conditions()
            for s in conds_str:
                conds.add_condition(parser.parse_expr(s))
            self.assertEqual(conds.is_positive(e), res, msg="Failed with %s" % e)


if __name__ == "__main__":
    unittest.main()
