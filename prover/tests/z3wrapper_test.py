# Author: Bohua Zhan

import unittest

from kernel.type import TFun
from kernel.thm import Thm
from data import nat
from logic import basic
from syntax import parser
from syntax import printer
from syntax.context import Context
from prover import z3wrapper


class Z3WrapperTest(unittest.TestCase):
    def testNormTerm(self):
        ctxt = Context('real', vars={'S': 'real set', 'T': 'real set', 'x': 'real', 'a': 'real', 'b': 'real'})
        thy = ctxt.thy

        test_data = [
            ('S ⊆ T', '∀x. x ∈ S ⟶ x ∈ T'),
            ('x ∈ {a, b}', 'x = a ∨ x = b'),
            ('x ∈ {x. a < x ∧ x < b}', 'a < x ∧ x < b'),
            ('{x. (a ≤ x ∧ x ≤ b) ∧ ¬(a < x ∧ x < b)} ⊆ {a, b}',
             '∀x. (a ≤ x ∧ x ≤ b) ∧ ¬(a < x ∧ x < b) ⟶ x = a ∨ x = b')
        ]

        for t, res_t in test_data:
            t = parser.parse_term(ctxt, t)
            res_t = parser.parse_term(ctxt, res_t)
            self.assertEqual(z3wrapper.norm_term(thy, t), res_t)

    def testSolve(self):
        if not z3wrapper.z3_loaded:
            return

        ctxt = Context('nat', vars={"s": 'nat => nat', "A": 'nat', "B": 'nat'})
        test_data = [
            ("s 0 = 0 & s 1 = 0 --> s 1 = s 0 * B", True),
            ("s 1 = s 0 * B & ~~s 0 = A --> s 1 = A * B", True),
            ("s 1 = s 0 * B & ~s 0 = A --> s 1 + B = (s 0 + 1) * B", True),
            ("A * B + 1 = 1 + B * A", True),
            ("s 0 = s 1", False),
            ("s 0 + s 1 = A --> A + s 2 = B --> s 0 + s 2 + s 1 = B", True),
            ("s 0 + s 1 = A --> A + s 2 = B --> s 0 + s 2 = B", False),
            ("(!n. s n = 0) --> s 2 = 0", True),
            ("(!n. s n = 0) --> s 0 = 1", False),
        ]

        for s, res in test_data:
            t = parser.parse_term(ctxt, s)
            self.assertEqual(z3wrapper.solve(ctxt.thy, t), res)

    def testSolveSet(self):
        if not z3wrapper.z3_loaded:
            return

        ctxt = Context('set', vars={'m': 'nat', 'S': 'nat set', 'T': 'nat set'})
        test_data = [
            ('a Mem S --> S Sub T --> a Mem T', True),
        ]

        for s, res in test_data:
            t = parser.parse_term(ctxt, s)
            self.assertEqual(z3wrapper.solve(ctxt.thy, t), res)

    def testSolveReal(self):
        if not z3wrapper.z3_loaded:
            return

        ctxt = Context('real', vars={'a': 'real', 'b': 'real', 'x': 'real', 'f': 'real => real', 'S': 'real set', 'T': 'real set'})
        test_data = [
            ('max a b = (1/2) * (a + b + abs(a - b))', True),
            ('(x Mem T --> 0 <= f x) --> S Sub T --> (if x Mem S then f x else 0) <= (if x Mem T then f x else 0)', True),
            ('{x. (a <= x & x <= b) & ~(a < x & x < b)} Sub {a, b}', True),
        ]

        for s, res in test_data:
            t = parser.parse_term(ctxt, s)
            self.assertEqual(z3wrapper.solve(ctxt.thy, t), res)

    def testZ3Macro(self):
        if not z3wrapper.z3_loaded:
            return

        macro = z3wrapper.Z3Macro()

        ctxt = Context('nat', vars={'s': 'nat => nat', 'A': 'nat', 'B': 'nat'})
        thy = ctxt.thy
        test_data = [
            ("A * B + 1 = 1 + B * A", True),
            ("s 0 = s 1", False),
        ]

        for s, res in test_data:
            t = parser.parse_term(ctxt, s)
            if res:
                self.assertEqual(macro.eval(thy, t, []), Thm([], t))
            else:
                self.assertRaises(AssertionError, macro.eval, thy, t, [])


if __name__ == "__main__":
    unittest.main()
