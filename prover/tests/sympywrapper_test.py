# Author: Bohua Zhan

import unittest
import sympy
from sympy import Symbol, sqrt, sin, cos
from sympy.abc import x

from logic.context import Context
from syntax import parser
from prover import sympywrapper


class SymPyWrapperTest(unittest.TestCase):
    def testConvert(self):
        test_data = [
            ("1 - x ^ (2::nat)", 1 - x ** 2),
            ("sqrt(2) * sin(x)", sqrt(2) * sin(x)),
        ]

        ctxt = Context('realintegral', vars={'x': 'real'})
        for s, res in test_data:
            s = parser.parse_term(ctxt, s)
            self.assertEqual(sympywrapper.convert(s), res)

    def testSymPySolve(self):
        test_data = [
            ("1 - x ^ (2::nat) >= 0", "x Mem real_closed_interval 0 1", True),
            ("1 - x ^ (2::nat) >= 0", "x Mem real_closed_interval 0 (sqrt 2)", False),
            ("2 - x ^ (2::nat) >= 0", "x Mem real_closed_interval 0 (sqrt 2)", True),
            ("2 - x ^ (2::nat) >= 0", "x Mem real_closed_interval 0 2", False),
            ("sqrt 2 * cos x >= 0", "x Mem real_closed_interval 0 (pi / 2)", True),
            ("sqrt 2 * cos x >= 0", "x Mem real_closed_interval 0 pi", False),
            ("log x >= 0", "x Mem real_closed_interval 1 (exp 1)", True),
            ("log x <= 0", "x Mem real_closed_interval (exp (-1)) 1", True),
            ("log x >= 0", "x Mem real_closed_interval (exp (-1)) (exp 1)", False),
        ]

        ctxt = Context('realintegral', vars={'x': 'real'})
        for goal, cond, res in test_data:
            goal = parser.parse_term(ctxt, goal)
            cond = parser.parse_term(ctxt, cond)
            self.assertEqual(sympywrapper.solve(goal, cond), res)


if __name__ == "__main__":
    unittest.main()
