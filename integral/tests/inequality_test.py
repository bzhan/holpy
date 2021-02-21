"""Unit test for inequality module."""

import unittest

from kernel.type import RealType
from kernel import term
from kernel.proofterm import ProofTerm
from logic import context
from data import set as hol_set
from data import nat
from integral.parser import parse_expr, parse_interval
from integral import inequality
from integral.expr import expr_to_holpy
from integral import proof  # for additional auto convs.
from integral.inequality import get_bounds, get_bounds_proof, interval_to_holpy, IntervalInequalityMacro
from syntax import parser


class InequalityTest(unittest.TestCase):
    def testParseInterval(self):
        test_data = [
            "(0, 1)", "(0, 1]", "[0, 1)", "[0, 1]",
            "(INT x:[1,2]. 3 * x, 5)",
        ]
        
        for s in test_data:
            self.assertEqual(str(parse_interval(s)), s)

    def testGetBounds(self):
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

    def testParity(self):
        test_data = [0,1,2,3,10,11]
        for n in test_data:
            if n % 2 == 0:
                self.assertEqual(inequality.nat_as_even(n).prop, nat.even(term.Nat(n)))
            else:
                self.assertEqual(inequality.nat_as_odd(n).prop, nat.odd(term.Nat(n)))

    def testGetBoundsProof(self):
        test_data = [
            ("x + 3", "[0, 1]", "[3, 4]"),
            ("x + 3", "(0, 1)", "(3, 4)"),
            ("3 + x", "(0, 1)", "(3, 4)"),
            ("x + x", "(0, 1)", "(0, 2)"),
            ("-x", "[0, 2]", "[-2, 0]"),
            ("-x", "(1, 3)", "(-3, -1)"),
            ("-x", "(-1, 1)", "(-1, 1)"),
            ("x - 3", "[0, 1]", "[-3, -2]"),
            ("3 - x", "(0, 1)", "(2, 3)"),
            ("x * 2", "[0, 1]", "[0, 2]"),
            ("1 / x", "[1, 2]", "[1/2, 1]"),
            ("x ^ 2", "[1, 2]", "[1, 4]"),
            ("x ^ 2", "(-1, 0)", "(0, 1)"),
            ("x ^ 3", "(-1, 0)", "(-1, 0)"),
            ("sin(x)", "(0, pi/2)", "(0, 1)"),
            ("sin(x)", "(-pi/2, 0)", "(-1, 0)"),
            ("cos(x)", "(0, pi/2)", "(0, 1)"),
            ("cos(x)", "(-pi/2, pi/2)", "[0, 1]"),
        ]

        context.set_context('interval_arith')
        for s, i1, i2 in test_data:
            t = expr_to_holpy(parse_expr(s))
            cond = hol_set.mk_mem(term.Var('x', RealType), interval_to_holpy(parse_interval(i1)))
            var_range = {'x': ProofTerm.assume(cond)}
            res = hol_set.mk_mem(t, interval_to_holpy(parse_interval(i2)))
            pt = get_bounds_proof(t, var_range)
            self.assertEqual(pt.prop, res)

    def testInequalityMacro(self):
        test_data = [
            ("x < 2", "x Mem real_closed_interval 0 1"),
        ]

        context.set_context('interval_arith', vars={'x': 'real'})
        macro = IntervalInequalityMacro()
        for goal, cond in test_data:
            goal = parser.parse_term(goal)
            cond = parser.parse_term(cond)
            pt = macro.get_proof_term(goal, [ProofTerm.assume(cond)])
            self.assertEqual(pt.prop, goal)


if __name__ == "__main__":
    unittest.main()
