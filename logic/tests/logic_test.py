# Author: Bohua Zhan

import unittest

from kernel.type import TVar, boolT
from kernel.term import Term, Var, Abs, Bound
from kernel.thm import Thm
from logic import logic
from logic import basic

Ta = TVar("a")
a = Var("a", boolT)
b = Var("b", boolT)
c = Var("c", boolT)
d = Var("d", boolT)
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

    def testGetForallName(self):
        test_data = [
            (Term.mk_all(x, Term.mk_all(y, Term.mk_equals(x, y))), ["x", "y"]),
        ]

        for t, res in test_data:
            self.assertEqual(logic.get_forall_names(t), res)

    def testNormBoolExpr(self):
        neg, true, false = logic.neg, logic.true, logic.false
        test_data = [
            (true, true),
            (false, false),
            (neg(true), false),
            (neg(false), true),
        ]

        thy = basic.load_theory('logic')
        for t, res in test_data:
            cv = logic.norm_bool_expr()
            prf = cv.get_proof_term(thy, t).export()
            self.assertEqual(thy.check_proof(prf), Thm.mk_equals(t, res))

    def testNormConjAssoc(self):
        conj = logic.mk_conj
        test_data = [
            (a, a),
            (conj(a, b), conj(a, b)),
            (conj(conj(a, b), conj(c, d)), conj(a, b, c, d)),
            (conj(conj(conj(a, b), c), d), conj(a, b, c, d)),
        ]

        thy = basic.load_theory('logic')
        for t, res in test_data:
            cv = logic.norm_conj_assoc()
            prf = cv.get_proof_term(thy, t).export()
            self.assertEqual(thy.check_proof(prf), Thm.mk_equals(t, res))


if __name__ == "__main__":
    unittest.main()
