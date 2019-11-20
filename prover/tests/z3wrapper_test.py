# Author: Bohua Zhan

import unittest

from kernel.type import TFun
from kernel.thm import Thm
from data import nat
from logic import basic
from logic.tests.logic_test import test_macro
from syntax import parser
from syntax import printer
from syntax.context import Context
from prover import z3wrapper
from server.tests.server_test import test_method


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

    def testSolveNat(self):
        if not z3wrapper.z3_loaded:
            return

        ctxt = Context('set', vars={
            'x': 'nat', 'y': 'nat', 'z': 'nat'
        })
        test_data = [
            ('x - y + z = x + z - y', False),
            ('x >= y --> x - y + z = x + z - y', True)
        ]
        for s, res in test_data:
            t = parser.parse_term(ctxt, s)
            self.assertEqual(z3wrapper.solve(ctxt.thy, t), res)

    def testSolveSet(self):
        if not z3wrapper.z3_loaded:
            return

        ctxt = Context('set', vars={
            'm': 'nat', 'S': 'nat set', 'T': 'nat set', 'x': 'nat',
            'a': "'a", 'A': "'a set"})
        test_data = [
            ('x Mem S --> S Sub T --> x Mem T', True),
            ('m Mem univ', True),
            ('(?x1. x = x1 & x1 Mem S) --> x Mem S', True),
            ('(?a1. a = a1 & a1 Mem A) --> a Mem A', True),
            ('x Mem (diff S T) --> x Mem S', True),
            ('x Mem S --> x Mem (diff S T)', False)
        ]

        for s, res in test_data:
            t = parser.parse_term(ctxt, s)
            self.assertEqual(z3wrapper.solve(ctxt.thy, t), res)

    def testSolveReal(self):
        if not z3wrapper.z3_loaded:
            return

        ctxt = Context('real', vars={
            'a': 'real', 'b': 'real', 'x': 'real', 'f': 'real => real', 'S': 'real set', 'T': 'real set',
            'n': 'nat'})
        test_data = [
            ('max a b = (1/2) * (a + b + abs(a - b))', True),
            ('(x Mem T --> 0 <= f x) --> S Sub T --> (if x Mem S then f x else 0) <= (if x Mem T then f x else 0)', True),
            ('{x. (a <= x & x <= b) & ~(a < x & x < b)} Sub {a, b}', True),
            ('max (if x Mem S then (1::real) else 0) (if x Mem T then 1 else 0) = (if x Mem (S Un T) then 1 else 0)', True),
            ('min (if x Mem S then (1::real) else 0) (if x Mem T then 1 else 0) = (if x Mem (S Int T) then 1 else 0)', True),
            ('S Int T = empty_set --> (if x Mem S then (1::real) else 0) + (if x Mem T then 1 else 0) = (if x Mem (S Un T) then 1 else 0)', True),
            ('S ∪ T = S ∩ T ∪ {x. x ∈ S ∧ ¬x ∈ T} ∪ {x. x ∈ T ∧ ¬x ∈ S}', True),
            ('(0::real) <= (if x Mem s & 1 / (of_nat n + 1) <= abs (f x) then 1 else 0)', True),
            ('(0::real) <= of_nat n + 1', True),
            ('1 / (of_nat n + 1) < b --> 1 < (of_nat n + 1) * b', True),
            ('1 / (a + 1) < b --> 1 < (a + 1) * b', False),
            ('a <= of_nat n --> a < of_nat (n + 1)', True),
            ('~(n = 0) --> of_nat (n - 1) + (1::real) = of_nat n', True),
        ]

        for s, res in test_data:
            t = parser.parse_term(ctxt, s)
            self.assertEqual(z3wrapper.solve(ctxt.thy, t), res)

    def testZ3Macro(self):
        if not z3wrapper.z3_loaded:
            return

        test_macro(
            self, 'real', 'z3',
            vars={'S': 'real set', 'T': 'real set', 'x': 'real'},
            assms=['S Int T = empty_set'],
            args='(if x Mem S then (1::real) else 0) + (if x Mem T then 1 else 0) = (if x Mem (S Un T) then 1 else 0)',
            res='(if x Mem S then (1::real) else 0) + (if x Mem T then 1 else 0) = (if x Mem (S Un T) then 1 else 0)',
            eval_only=True
        )

    def testZ3MacroFail(self):
        if not z3wrapper.z3_loaded:
            return

        test_macro(
            self, 'logic_base', 'z3',
            vars={'P': 'bool', 'Q': 'bool'},
            args='P --> Q',
            eval_only=True,
            failed=AssertionError
        )

    def testZ3Method(self):
        if not z3wrapper.z3_loaded:
            return

        test_method(
            self, 'real',
            vars={'S': 'real set', 'T': 'real set', 'x': 'real'},
            assms=['S Int T = empty_set'],
            concl='(if x Mem S then (1::real) else 0) + (if x Mem T then 1 else 0) = (if x Mem (S Un T) then 1 else 0)',
            method_name='z3',
            prevs=[0],
            gaps=False
        )

    def testZ3MethodFail(self):
        if not z3wrapper.z3_loaded:
            return

        test_method(
            self, 'logic_base',
            vars={'P': 'bool', 'Q': 'bool'},
            concl='P --> Q',
            method_name='z3',
            failed=AssertionError
        )


if __name__ == "__main__":
    unittest.main()
