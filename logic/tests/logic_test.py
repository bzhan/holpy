# Author: Bohua Zhan

import unittest

from kernel.type import TVar, hol_bool
from kernel.term import Term, Var, Abs, Bound
from logic import logic

Ta = TVar("a")
a = Var("a", hol_bool)
b = Var("b", hol_bool)
x = Var("x", Ta)
y = Var("y", Ta)
abs = Term.mk_abs

class LogicTest(unittest.TestCase):
    def testConj(self):
        test_data = [
            ([], logic.true),
            ([a], a),
            ([a, b], logic.conj(a, b)),
            ([a, b, a], logic.conj(a, logic.conj(b, a)))
        ]

        for ts, res in test_data:
            self.assertEqual(logic.mk_conj(*ts), res)

    def testConjFail(self):
        self.assertRaises(AssertionError, logic.mk_conj, [a])

    def testStripConj(self):
        test_data = [
            (a, [a]),
            (logic.mk_conj(a, b, a), [a, b, a])
        ]

        for t, res in test_data:
            self.assertEqual(logic.strip_conj(t), res)

    def testDisj(self):
        test_data = [
            ([], logic.false),
            ([a], a),
            ([a, b], logic.disj(a, b)),
            ([a, b, a], logic.disj(a, logic.disj(b, a)))
        ]

        for ts, res in test_data:
            self.assertEqual(logic.mk_disj(*ts), res)

    def testDisjFail(self):
        self.assertRaises(AssertionError, logic.mk_disj, [a])

    def testStripDisj(self):
        test_data = [
            (a, [a]),
            (logic.mk_disj(a, b, a), [a, b, a])
        ]

        for t, res in test_data:
            self.assertEqual(logic.strip_disj(t), res)

    def testBetaNorm(self):
        test_data = [
            (abs(x,x)(x), x),
            (abs(x,abs(y,y))(x,y), y),
            (abs(x,abs(y,x))(x,y), x),
        ]

        for t, res in test_data:
            self.assertEqual(logic.beta_norm(t), res)

if __name__ == "__main__":
    unittest.main()
