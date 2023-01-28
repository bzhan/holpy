"""Unit test for contexts"""

import unittest

from integral.context import Context
from integral import parser


class ContextTest(unittest.TestCase):
    def testGetConds(self):
        ctx1 = Context()
        ctx1.add_condition("a", parser.parse_expr("a > 0"))
        ctx2 = Context(ctx1)
        ctx2.add_condition("b", parser.parse_expr("b > 0"))
        self.assertEqual(len(ctx2.conds.data), 1)
        self.assertEqual(len(ctx2.get_conds().data), 2)


if __name__ == "__main__":
    unittest.main()
