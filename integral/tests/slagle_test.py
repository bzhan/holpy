"""Unit test for Slagle."""

import unittest

from integral.parser import parse_expr
from integral import slagle


class SlagleTest(unittest.TestCase):
    def testCommonIntegral(self):
        test_data = [
            ('INT y:[tan(2),tan(1)]. (1 + y ^ 2) ^ -1', '[atan(y)]_y=tan(2),tan(1)'),
            ('INT y:[tan(2),tan(1)]. 1', '[y]_y=tan(2),tan(1)'),
        ]

        for v, v_res in test_data:
            v = parse_expr(v)
            v_res = parse_expr(v_res)
            self.assertEqual(slagle.CommonIntegral().eval(v), v_res)

    def testDividePolynomial(self):
        test_data = [
            ('INT y:[tan(2),tan(1)]. -y ^ 4 * (1 + y ^ 2) ^ -1',
             '(INT y:[tan(2),tan(1)]. 1) - (INT y:[tan(2),tan(1)]. y ^ 2) - (INT y:[tan(2),tan(1)]. (1 + y ^ 2) ^ -1)'),
        ]

        for v, v_res in test_data:
            v = parse_expr(v)
            v_res = parse_expr(v_res)
            self.assertEqual(slagle.DividePolynomial().eval(v), v_res)

    def testTrigFunction(self):
        test_data = [
            ('INT x:[1,2]. $sin(x)^4/cos(x)^4$',
             ['INT x:[1,2]. tan(x)^4'])
        ]

        for v, v_res in test_data:
            v = parse_expr(v)
            v_res = [parse_expr(v2) for v2 in v_res]
            self.assertEqual(slagle.TrigFunction().eval(v), v_res)

    def testHeuristicSubstitution(self):
        test_data = [
            ('INT x:[1,2]. tan(x)^4',
             ['INT y:[tan(2),tan(1)]. -y ^ 4 * (1 + y ^ 2) ^ -1']),
        ]

        for v, v_res in test_data:
            v = parse_expr(v)
            v_res = [parse_expr(v2) for v2 in v_res]
            self.assertEqual(slagle.HeuristicSubstitution().eval(v), v_res)
    
    def testBFS(self):
        node = slagle.OrNode('INT x:[1,2]. $sin(x)^4/cos(x)^4$')
        slagle.bfs(node)
        self.assertTrue(node.resolved)


if __name__ == "__main__":
    unittest.main()
