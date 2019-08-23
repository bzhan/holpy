"""Unit test for parsing."""

import unittest

from integral.expr import Var, Const
from integral.parser import parse_expr


class ParserTest(unittest.TestCase):
    def testParseTerm(self):
        test_data = [
            "x", "1", "1.1", "-1", "-1.1",
            "x + y", "x - y", "-x", "x * y", "x / y", "x ^ y",
            "x + y * z", "(x + y) * z",
            "x * y + z", "x * (y + z)",
            "x * y ^ 2", "(x * y) ^ 2",
            "sin(x)", "cos(x)", "log(x)",
            "D x. 3 * x",
            "INT x:[1,2]. 3 * x",
            "[3 * x]_x=1,2",
        ]

        for s in test_data:
            e = parse_expr(s)
            self.assertEqual(str(e), s)

    def testParseTerm2(self):
        test_data = [
            ("-x", -Var("x")),
            ("-2", Const(-2)),
        ]

        for s, e, in test_data:
            self.assertEqual(parse_expr(s), e)


if __name__ == "__main__":
    unittest.main()
