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
             '(-(INT y:[tan(2),tan(1)]. y ^ 2) + (INT y:[tan(2),tan(1)]. 1)) - (INT y:[tan(2),tan(1)]. 1 / (y ^ 2 + 1))'),
        ]

        for v, v_res in test_data:
            v = parse_expr(v)
            v_res = parse_expr(v_res)
            self.assertEqual(slagle.DividePolynomial().eval(v), v_res)

    def testLinearity(self):
        test_data = [
            ('INT x:[1, 2]. 3*x', '3*INT x:[1, 2]. x'),
            ('INT x:[1, 2]. 3*x + exp(x)', '3*(INT x:[1, 2]. x) + INT x:[1, 2]. exp(x)'),
            ('INT x:[1, 2]. x*exp(x)', 'INT x:[1, 2]. x*exp(x)'),
            ('INT x:[1, 2]. 4*exp(x) - sin(x)', '4 * (INT x:[1, 2]. exp(x)) - INT x:[1, 2]. sin(x)')
        ]

        for v, v_res in test_data:
            v = parse_expr(v)
            v_res = parse_expr(v_res)
            self.assertEqual(slagle.Linearity().eval(v), v_res)            

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
             ['INT y:[tan(2),tan(1)]. -1*y ^ 4 * (1 + y ^ 2) ^ -1']),
        ]

        for v, v_res in test_data:
            v = parse_expr(v)
            v_res = [parse_expr(v2) for v2 in v_res]
            self.assertEqual(slagle.HeuristicSubstitution().eval(v), v_res)

    def testHeuristicElimQuadratic(self):
        test_data = [
            ('INT x:[0,1]. x/(sqrt(x^2+2*x+5))',
            ['INT c:[1,2]. c * (4 + c ^ 2) ^ (-1/2) + -1 * (4 + c ^ 2) ^ (-1/2)']),
        ]

        for v, v_res in test_data:
            v = parse_expr(v)
            v_res = [parse_expr(v2) for v2 in v_res]
            self.assertEqual(slagle.HeuristicElimQuadratic().eval(v), v_res)

    def testHeuristicTrigSubstitution(self):
        test_data = [
            ('INT x:[-1/2,1/2]. x^4/(1-x^2)^(5/2)',
            ['INT u:[-pi / 6,pi / 6]. cos(u) * sin(u) ^ 4 * (1 + -1 * sin(u) ^ 2) ^ (-5/2)']),
        ]

        for v, v_res in test_data:
            v = parse_expr(v)
            v_res = [parse_expr(v2) for v2 in v_res]
            self.assertEqual(slagle.HeuristicTrigSubstitution().eval(v), v_res)

    def testHeuristicExpandPower(self):
        test_data = [
            ('INT x:[0,1]. x*(x^(1/2) + x^(-1/2))^2',
            ['INT x:[0,1]. x * (2 + x ^ -1 + x)']),
        ]

        for v, v_res in test_data:
            v = parse_expr(v)
            v_res = [parse_expr(v2) for v2 in v_res]
            self.assertEqual(slagle.HeuristicExpandPower().eval(v), v_res)

    def testHeuristicExponentBase(self):
        test_data = [
            ('INT x:[0,1]. exp(6*x)/(exp(4*x)+1)',
            ['INT u:[1,exp(2)]. u ^ 2 / (2 * (u ^ 2 + 1))']),
        ]

        for v, v_res in test_data:
            v = parse_expr(v)
            v_res = [parse_expr(v2) for v2 in v_res]
            self.assertEqual(slagle.HeuristicExponentBase().eval(v), v_res)
    
    def testBFS(self):
        test_data = [
            # 'INT x:[1,2]. $sin(x)^4/cos(x)^4$',
            'INT x:[0, 1]. (2*x + 5)*(x^2+5*x)^7',
            'INT x:[1,2]. sqrt(7*x+9)',
            'INT x:[0, 1]. x^3/(1+x^4)^(1/4)',
            'INT x:[0, 1].exp(5*x+2)',
            'INT x:[exp(1),exp(2)].3/(x*log(x))',
            'INT x:[0,1].cos(5*x)/exp(sin(5*x))',
            'INT x:[0,1]. x * (x ^ (1/2) + x ^ (-1/2)) ^ 2',
            # The following result in infinite loop in normalize!!!!
            # 'INT x:[0,1]. exp(6*x)/(exp(4*x)+1)',

        ]

        for v in test_data:
            node = slagle.OrNode(v)
            slagle.bfs(node)
            self.assertTrue(node.resolved)


if __name__ == "__main__":
    unittest.main()
