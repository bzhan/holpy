# Author: Bohua Zhan

import unittest
import sympy
from sympy import Symbol, sqrt, sin, cos
from sympy.abc import x

from logic import context
from logic.tests.logic_test import test_macro
from syntax import parser
from prover import sympywrapper


class SymPyWrapperTest(unittest.TestCase):
    def testConvert(self):
        test_data = [
            ("1 - x ^ (2::nat)", 1 - x ** 2),
            ("sqrt(2) * sin(x)", sqrt(2) * sin(x)),
            ("real_closed_interval 0 1", sympy.Interval(0, 1)),
            ("real_open_interval 0 1", sympy.Interval.open(0, 1)),
        ]

        context.set_context('realintegral', vars={'x': 'real'})
        for s, res in test_data:
            s = parser.parse_term(s)
            self.assertEqual(sympywrapper.convert(s), res)

    def testSymPySolve(self):
        test_data = [
            # No conditions
            ("sqrt 2 >= 1", True),
            ("~((1::real) = 2)", True),
            ("(4::nat) > 2", True),
            ("(4::nat) >= 2", True),
            ("1 / 2 * 2 ^ (1 / 2) = 2 ^ -(1 / 2)", True),
        ]

        context.set_context('transcendentals')
        for goal, res in test_data:
            goal = parser.parse_term(goal)
            self.assertEqual(sympywrapper.solve_goal(goal), res)

    def testSymPySolve2(self):
        test_data = [
            # Interval condition
            ("1 - x ^ (2::nat) >= 0", "x Mem real_closed_interval 0 1", True),
            ("1 - x ^ (2::nat) >= 0", "x Mem real_closed_interval 0 (sqrt 2)", False),
            ("1 - x ^ (2::nat) > 0", "x Mem real_open_interval 0 1", True),
            ("2 - x ^ (2::nat) >= 0", "x Mem real_closed_interval 0 (sqrt 2)", True),
            ("2 - x ^ (2::nat) >= 0", "x Mem real_closed_interval 0 2", False),
            ("sqrt 2 * cos x >= 0", "x Mem real_closed_interval 0 (pi / 2)", True),
            ("sqrt 2 * cos x >= 0", "x Mem real_closed_interval 0 pi", False),
            ("log x >= 0", "x Mem real_closed_interval 1 (exp 1)", True),
            ("log x <= 0", "x Mem real_closed_interval (exp (-1)) 1", True),
            ("log x >= 0", "x Mem real_closed_interval (exp (-1)) (exp 1)", False),
            ("~(sin x = 0)", "x Mem real_closed_interval 1 2", True),
            ("~(sin x = 0)", "x Mem real_closed_interval (-1) 1", False),
            ("~(sin x = 0)", "x Mem real_closed_interval 0 1", False),
            ("~(x ^ (2::nat) = 0)", "x Mem real_closed_interval (-1) 1", False),
            ("~(x ^ (2::nat) + 1 = 0)", "x Mem real_closed_interval (-1) 1", True),
        ]

        context.set_context('transcendentals', vars={'x': 'real'})
        for goal, cond, res in test_data:
            goal = parser.parse_term(goal)
            cond = parser.parse_term(cond)
            self.assertEqual(sympywrapper.solve_with_interval(goal, cond), res)

    def testAuto(self):
        test_data = [
            # No conditions
            ("sqrt 2 >= 1"),
            ("~((1::real) = 2)"),
            ("(4::nat) > 2"),

            # Interval condition
            ("x Mem real_closed_interval 0 1 --> 1 - x ^ (2::nat) >= 0"),
            ("x Mem real_open_interval 0 1 --> 1 - x ^ (2::nat) > 0"),
            ("x Mem real_closed_interval 0 (sqrt 2) --> 2 - x ^ (2::nat) >= 0"),
            ("x Mem real_closed_interval 0 (pi / 2) --> sqrt 2 * cos x >= 0"),
            ("x Mem real_closed_interval 0 (2 ^ (1 / 2)) --> 2 - x ^ (2::nat) >= 0"),
        ]

        vars = {'x': 'real'}
        for expr in test_data:
            test_macro(self, 'interval_arith', 'auto', vars=vars, args=expr, res=expr)


if __name__ == "__main__":
    unittest.main()
