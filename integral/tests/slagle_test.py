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
            self.assertEqual(slagle.CommonIntegral().eval(v)[0], v_res)

    def testDividePolynomial(self):
        test_data = [
            ('INT y:[tan(2),tan(1)]. -y ^ 4 * (1 + y ^ 2) ^ -1',
             '(INT y:[tan(2),tan(1)]. 1) + -(INT y:[tan(2),tan(1)]. y ^ 2) + -(INT y:[tan(2),tan(1)]. (1 + y ^ 2) ^ -1)'),
        ]

        for v, v_res in test_data:
            v = parse_expr(v)
            self.assertEqual(str(slagle.DividePolynomial().eval(v)[0].normalize()), v_res)

    def testHalfAngleIdentity(self):
        test_data = [
            ('INT x:[0, pi/2]. sin(2*x) * cos(2*x)', 'INT x:[0, 1/2 * pi]. 1/2 * sin(4*x)'),
            ('INT x:[0, pi/2]. sin(x) ^ 2', 'INT x:[0, 1/2 * pi]. 1/2 + 1/2 * cos(2 * x)'),
            ('INT x:[0, pi/2]. cos(x) ^ 2', 'INT x:[0, 1/2 * pi]. 1/2 + -1/2 * cos(2 * x)')
        ]

        for v, v_res in test_data:
            v = parse_expr(v)
            v_res = parse_expr(v_res)
            self.assertEqual(slagle.HalfAngleIdentity().eval(v)[0].normalize(), v_res)

    def testLinearity(self):
        test_data = [
            ('INT x:[1, 2]. 3*x', '3 * (INT x:[1,2]. x)'),
            ('INT x:[1, 2]. 3*x + exp(x)', '3 * (INT x:[1,2]. x) + (INT x:[1,2]. exp(x))'),
            ('INT x:[1, 2]. x*exp(x)', 'INT x:[1,2]. x * exp(x)'),
            ('INT x:[1, 2]. 4*exp(x) - sin(x)', '4 * (INT x:[1,2]. exp(x)) + -(INT x:[1,2]. sin(x))')
        ]

        for v, v_res in test_data:
            v = parse_expr(v)
            self.assertEqual(str(slagle.Linearity().eval(v)[0].normalize()), v_res)            

    def testTrigIdentity(self):
        test_data = [
            ('INT u:[0,1/2 * pi]. cos(u) * (1 + -1 * sin(u) ^ 2) ^ (1/2)',
             'INT u:[0,1/2 * pi]. cos(u) ^ 2'),
            ('INT u:[0,1/2 * pi]. cos(u) * (1 + -1 * cos(u) ^ 2) ^ (1/2)',
             'INT u:[0,1/2 * pi]. cos(u) * sin(u)'),
            ('INT u:[0,1/2 * pi]. 6 + (-6) * sin(x) ^ 2', 'INT u:[0,1/2 * pi]. 6 * cos(x) ^ 2'),
            ('INT u:[0,1/2 * pi]. 6 + (-5) * sin(x) ^ 2', 'INT u:[0,1/2 * pi]. 6 + -5 * sin(x) ^ 2')
        ]

        for v, v_res in test_data:
            v = parse_expr(v)
            self.assertEqual(str(slagle.TrigIdentity().eval(v)[0].normalize()), v_res)

    def testTrigFunction(self):
        test_data = [
            ('INT x:[1,2]. $sin(x)^4/cos(x)^4$',
             ['INT x:[1,2]. tan(x)^4', 'INT x:[1,2]. cot(x)^(-4)'])
        ]

        for v, v_res in test_data:
            v = parse_expr(v)
            v_res = [parse_expr(v2) for v2 in v_res]
            self.assertEqual([r.normalize() for r, _ in slagle.TrigFunction().eval(v)], v_res)

    def testHeuristicTrigonometricSubstitution(self):
        test_data = [
            ('INT x:[0,1].sin(x)*cos(x)^3', 'INT s:[0,sin(1)]. s + -1 * s ^ 3'),
            ('INT x:[0,1].sin(x)^5*cos(x)', 'INT j:[cos(1),1]. j * (1 + -1 * j ^ 2) ^ 2'),
            ('INT x:[0,1].tan(x)', 'INT c:[0,tan(1)]. c * (1 + c ^ 2) ^ -1'),
        ]

    def testHeuristicSubstitution(self):
        test_data = [
            ('INT x:[1,2]. tan(x)^4',
             ['INT y:[tan(2),tan(1)]. -y ^ 4 * (1 + y ^ 2) ^ -1']),
        ]

        for v, v_res in test_data:
            v = parse_expr(v)
            self.assertEqual([str(r.normalize())
                              for r, _ in slagle.HeuristicSubstitution().eval(v)], v_res)

    def testHeuristicElimQuadratic(self):
        test_data = [
            ('INT x:[0,1]. x/(sqrt(5 + 2 * x + x ^ 2))',
             ['INT y:[1,2]. y * (4 + y ^ 2) ^ (-1/2) + -(4 + y ^ 2) ^ (-1/2)']),
        ]

        for v, v_res in test_data:
            v = parse_expr(v)
            self.assertEqual([str(r.normalize())
                              for r, _ in slagle.HeuristicElimQuadratic().eval(v)], v_res)

    def testHeuristicTrigSubstitution(self):
        test_data = [
            ('INT x:[-1/2,1/2]. x^4/(1-x^2)^(5/2)',
             ['INT u:[-1/6 * pi,1/6 * pi]. cos(u) * sin(u) ^ 4 * (1 + -sin(u) ^ 2) ^ (-5/2)']),
        ]

        for v, v_res in test_data:
            v = parse_expr(v)
            self.assertEqual([str(e.normalize())
                              for e, _ in slagle.HeuristicTrigSubstitution().eval(v)], v_res)

    def testHeuristicExpandPower(self):
        test_data = [
            ('INT x:[0,1]. x*(x^(1/2) + x^(-1/2))^2',
            ['INT x:[0,1]. 1 + 2 * x + x ^ 2']),
        ]

        for v, v_res in test_data:
            v = parse_expr(v)
            v_res = [parse_expr(v2) for v2 in v_res]
            self.assertEqual([r.normalize() for r, _ in slagle.HeuristicExpandPower().eval(v)], v_res)

    def testHeuristicExponentBase(self):
        test_data = [
            ('INT x:[0,1]. exp(6*x)/(exp(4*x)+1)',
            ['INT u:[1,exp(2)]. u ^ 2 * (2 + 2 * u ^ 2) ^ -1']),
        ]

        for v, v_res in test_data:
            v = parse_expr(v)
            self.assertEqual([str(r.normalize())
                              for r, _ in slagle.HeuristicExponentBase().eval(v)], v_res)
    
    def testBFS(self):
        test_data = [
            # 'INT x:[1,2]. sin(x)^4/cos(x)^4',
            'INT x:[0, 1]. (2*x + 5)*(x^2+5*x)^7',
            'INT x:[1,2]. sqrt(7*x+9)',
            'INT x:[0, 1]. x^3/(1+x^4)^(1/4)',
            'INT x:[0, 1].exp(5*x+2)',
            'INT x:[exp(1),exp(2)].3/(x*log(x))',
            'INT x:[0,1].cos(5*x)/exp(sin(5*x))',
            'INT x:[0,1]. x * (x ^ (1/2) + x ^ (-1/2)) ^ 2',
            # 'INT x:[0,1]. exp(6*x)/(exp(4*x)+1)',
        ]

        for v in test_data:
            node = slagle.OrNode(v)
            slagle.timeout(10)(slagle.bfs)(node)
            self.assertTrue(node.resolved)
            # print(node)
            # print(node.resolved_steps)
            # for step in node.resolved_steps:
            #     print(step.info())


if __name__ == "__main__":
    unittest.main()
