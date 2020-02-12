import unittest
import json

from kernel.term import Not
from logic import logic
from logic import basic
from syntax import parser
from logic import context
from prover import tseitin
from prover import sat


class SATTest(unittest.TestCase):
    def testDisplayCNF(self):
        cnf1 = [[('x', False), ('y', True)], [('y', False), ('z', True)]]
        res1 = "(¬x ∨ y) ∧ (¬y ∨ z)"
        self.assertEqual(sat.str_of_cnf(cnf1), res1)

        cnf2 = [[('x', False)], [('y', True)]]
        res2 = "(¬x) ∧ (y)"
        self.assertEqual(sat.str_of_cnf(cnf2), res2)

        cnf3 = [[('x', False), ('y', True)]]
        res3 = "(¬x ∨ y)"
        self.assertEqual(sat.str_of_cnf(cnf3), res3)

    def testSolveCNF1(self):
        cnf = [[('x', False), ('y', True)], [('y', False), ('z', True)]]
        res, cert = sat.solve_cnf(cnf)
        self.assertEqual(res, 'satisfiable')
        self.assertTrue(sat.is_solution(cnf, cert))

    def testSolveCNF2(self):
        cnf = [[('x', True)], [('x', False)]]
        res, cert = sat.solve_cnf(cnf)
        self.assertEqual(res, 'unsatisfiable')
        self.assertEqual(cert, {2: [1, 0]})

    def testSolveCNF3(self):
        cnf = [[('x', True), ('y', True)], [('x', True), ('y', False)],
               [('x', False), ('y', True)], [('x', False), ('y', False)]]
        res, cert = sat.solve_cnf(cnf)
        self.assertEqual(res, 'unsatisfiable')

    def testSolveCNF4(self):
        cnf = [[]]
        res, cert = sat.solve_cnf(cnf)
        self.assertEqual(res, 'unsatisfiable')
        self.assertEqual(cert, {1: [0]})

    def testSolveCNF5(self):
        cnf = []
        res, cert = sat.solve_cnf(cnf)
        self.assertEqual(res, 'satisfiable')
        self.assertTrue(sat.is_solution(cnf, cert))
    
    def testPelletier(self):
        with open('prover/tests/pelletier.json', 'r', encoding='utf-8') as f:
            f_data = json.load(f)

        for problem in f_data:
            context.set_context('sat', vars=problem['vars'])
            prop = parser.parse_term(problem['prop'])
            cnf = tseitin.convert_cnf(tseitin.encode(Not(prop)).prop)
            res, cert = sat.solve_cnf(cnf)
            self.assertEqual(res, 'unsatisfiable')


if __name__ == "__main__":
    unittest.main()
