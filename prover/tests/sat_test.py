import unittest

from prover import sat

class SATTest(unittest.TestCase):
    def testDisplayCNF(self):
        cnf1 = [[('x', False), ('y', True)], [('y', False), ('z', True)]]
        res1 = "(~x | y) & (~y | z)"
        self.assertEqual(sat.display_cnf(cnf1), res1)

        cnf2 = [[('x', False)], [('y', True)]]
        res2 = "~x & y"
        self.assertEqual(sat.display_cnf(cnf2, res2))

        cnf2 = [[('x', False), ('y', True)]]
        res3 = "~x | y"
        self.assertEqual(sat.display_cnf(cnf3, res3))

    def testIsSolution(self):
        cnf = [[('x', False), ('y', True)], [('y', False), ('z', True)]]

        inst1 = {'x': True, 'y': True, 'z': True}
        self.assertTrue(sat.is_solution(cnf, inst1))

        inst2 = {'x': False, 'y': True, 'z': True}
        self.assertTrue(sat.is_solution(cnf, inst2))

        inst3 = {'x': True, 'y': False, 'z': True}
        self.assertFalse(sat.is_solution(cnf, inst3))

        inst4 = dict()
        self.assertRaises(sat.SATSolverException, sat.is_solution, cnf, inst4)

    def testSolveCNF1(self):
        cnf = [[('x', False), ('y', True)], [('y', False), ('z', True)]]
        res = sat.solve_cnf(cnf)
        self.assertTrue(sat.is_solution(cnf, res))

    def testSolveCNF2(self):
        cnf = [[('x', True)], [('x', False)]]
        self.assertIsNone(sat.solve_cnf(cnf))

    def testSolveCNF3(self):
        cnf = [[('x', True), ('y', True)], [('x', True), ('y', False)],
               [('x', False), ('y', True)], [('x', False), ('y', False)]]
        self.assertIsNone(sat.solve_cnf(cnf))
