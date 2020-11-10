"""Unit test for inequality module."""

import unittest

from integral.parser import parse_expr, parse_interval
from integral import inequality


class InequalityTest(unittest.TestCase):
    def testParseInterval(self):
        test_data = [
            "(0, 1)", "(0, 1]", "[0, 1)", "[0, 1]",
            "(INT x:[1,2]. 3 * x, 5)",
        ]
        
        for s in test_data:
            self.assertEqual(str(parse_interval(s)), s)

    def testGetBound(self):
        test_data = [
            ("x - 4", "(0, 1)", "(-4, -3)"),
        ]

        for s, i1, i2 in test_data:
            s = parse_expr(s)
            var_range = {'x': parse_interval(i1)}
            self.assertEqual(str(inequality.get_bound(s, var_range)), i2)


if __name__ == "__main__":
    unittest.main()
