"""Unit test for inequality module."""

import unittest

from logic import context
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
            ("sqrt(x)", "(1, 4)", "(1, 2)"),
            ("(x + 1) * (x + 2)", "(0, 1)", "(2, 6)"),
            ("(x + 1) * (x + 2)", "(0, 1]", "(2, 6]"),
            ("1 / sqrt(x)", "(1, 4)", "(1/2, 1)"),
            ("1 / sqrt(2 * x)", "(1, 4)", "(1/4 * sqrt(2), 1/2 * sqrt(2))"),
        ]

        for s, i1, i2 in test_data:
            context.set_context('transcendentals')
            s = parse_expr(s)
            var_range = {'x': parse_interval(i1)}
            self.assertEqual(str(inequality.get_bounds(s, var_range)), i2)


if __name__ == "__main__":
    unittest.main()
