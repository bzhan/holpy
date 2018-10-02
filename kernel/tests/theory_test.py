# Author: Bohua Zhan

import unittest
from kernel.thm import *
from kernel.proof import *
from kernel.theory import *

thy = Theory.EmptyTheory()

Ta = TVar("a")
Tb = TVar("b")
Tab = TFun(Ta, Tb)
a = Var("a", Ta)
b = Var("b", Ta)
f = Var("f", Tab)
A = Var("A", hol_bool)
B = Var("B", hol_bool)
A_to_B = Term.mk_implies(A, B)

class TheoryTest(unittest.TestCase):
    def testEmptyTheory(self):
        self.assertEqual(thy.get_type_sig("bool"), 0)
        self.assertEqual(thy.get_type_sig("fun"), 2)
        self.assertEqual(thy.get_term_sig("equals"), TFun(Ta,TFun(Ta,hol_bool)))
        self.assertEqual(thy.get_term_sig("implies"), TFun(hol_bool,TFun(hol_bool,hol_bool)))

    def testCheckType(self):
        test_data = [
            Ta,
            TFun(Ta, Tb),
            TFun(TFun(Ta, Ta), Tb),
            TFun(hol_bool, hol_bool),
            TFun(TFun(Ta, hol_bool), hol_bool),
        ]

        for T in test_data:
            self.assertEqual(thy.check_type(T), None)

    def testCheckTypeFail(self):
        test_data = [
            Type("bool", Ta),
            Type("bool", [Ta, Ta]),
            Type("fun"),
            Type("fun", Ta),
            Type("fun", [Ta, Ta, Ta]),
            Type("random")
        ]

        for T in test_data:
            self.assertRaises(TheoryException, thy.check_type, T)

    def testCheckTerm(self):
        test_data = [
            a,
            Term.mk_equals(a, b),
            Term.mk_equals(f, f),
            Term.mk_implies(A, B),
            Abs("x", Ta, Term.mk_equals(a, b)),
        ]

        for t in test_data:
            self.assertEqual(thy.check_term(t), None)

    def testCheckTermFail(self):
        test_data = [
            Const("random", Ta),
            Const("equals", TFun(Ta, TFun(Tb, hol_bool))),
            Const("equals", TFun(Ta, TFun(Ta, Tb))),
            Const("implies", TFun(Ta, TFun(Ta, hol_bool))),
            Comb(Const("random", Tab), a),
            Comb(f, Const("random", Ta)),
            Abs("x", Ta, Const("random", Ta)),
        ]

        for t in test_data:
            self.assertRaises(TheoryException, thy.check_term, t)

    def testCheckProof(self):
        prf = Proof()
        prf.add_item("A1", Thm([A_to_B], A_to_B), "assume", A_to_B, None)
        prf.add_item("A2", Thm([A], A), "assume", A, None)
        prf.add_item("C", Thm([A, A_to_B], B), "implies_elim", None, ["A1", "A2"])

        self.assertEqual(thy.check_proof(prf), Thm([A, A_to_B], B))

if __name__ == "__main__":
    unittest.main()
