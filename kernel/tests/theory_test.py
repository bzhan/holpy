# Author: Bohua Zhan

import unittest
from kernel.thm import *
from kernel.proof import *
from kernel.theory import *

thy = Theory.EmptyTheory()

Ta = TVar("a")
Tb = TVar("b")
Tab = TFun(Ta, Tb)
x = Var("x", Ta)
y = Var("y", Ta)
z = Var("z", Ta)
f = Var("f", Tab)
A = Var("A", hol_bool)
B = Var("B", hol_bool)
C = Var("C", hol_bool)

thy.add_theorem("trivial", Thm([], Term.mk_implies(A,A)))

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
            x,
            Term.mk_equals(x, y),
            Term.mk_equals(f, f),
            Term.mk_implies(A, B),
            Abs("x", Ta, Term.mk_equals(x, y)),
        ]

        for t in test_data:
            self.assertEqual(thy.check_term(t), None)

    def testCheckTermFail(self):
        test_data = [
            Const("random", Ta),
            Const("equals", TFun(Ta, TFun(Tb, hol_bool))),
            Const("equals", TFun(Ta, TFun(Ta, Tb))),
            Const("implies", TFun(Ta, TFun(Ta, hol_bool))),
            Comb(Const("random", Tab), x),
            Comb(f, Const("random", Ta)),
            Abs("x", Ta, Const("random", Ta)),
        ]

        for t in test_data:
            self.assertRaises(TheoryException, thy.check_term, t)

    def testCheckProof(self):
        """Proof of [A, A --> B] |- B."""
        A_to_B = Term.mk_implies(A, B)
        th = Thm([A, A_to_B], B)
        prf = Proof(A_to_B, A)
        prf.add_item("C", th, "implies_elim", None, ["A1", "A2"])

        self.assertEqual(thy.check_proof(prf), th)

    def testCheckProof2(self):
        """Proof of |- A --> A."""
        th = Thm([], Term.mk_implies(A,A))
        prf = Proof(A)
        prf.add_item("C", th, "implies_intr", A, ["A1"])

        self.assertEqual(thy.check_proof(prf), th)

    def testCheckProof3(self):
        """Proof of [x = y, y = z] |- f z = f x."""
        x_eq_y = Term.mk_equals(x,y)
        y_eq_z = Term.mk_equals(y,z)
        th = Thm([x_eq_y, y_eq_z], Term.mk_equals(Comb(f,z), Comb(f,x)))
        prf = Proof(x_eq_y, y_eq_z)
        prf.add_item("S1", Thm([x_eq_y, y_eq_z], Term.mk_equals(x,z)), "transitive", None, ["A1", "A2"])
        prf.add_item("S2", Thm([x_eq_y, y_eq_z], Term.mk_equals(z,x)), "symmetric", None, ["S1"])
        prf.add_item("S3", Thm([], Term.mk_equals(f,f)), "reflexive", f, None)
        prf.add_item("C", th, "combination", None, ["S3", "S2"])

        self.assertEqual(thy.check_proof(prf), th)

    def testCheckProof4(self):
        """Proof of |- x = y --> x = y by instantiating an existing theorem."""
        x_eq_y = Term.mk_equals(x,y)
        th = Thm([], Term.mk_implies(x_eq_y,x_eq_y))
        prf = Proof()
        prf.add_item("S1", Thm([], Term.mk_implies(A,A)), "theorem", "trivial", [])
        prf.add_item("C", th, "substitution", {"A" : x_eq_y}, ["S1"])

        self.assertEqual(thy.check_proof(prf), th)

    def testCheckProofFail(self):
        """Previous item not found."""
        prf = Proof()
        prf.add_item("C", Thm([], A), "implies_intr", None, ["A1"])

        self.assertRaisesRegex(CheckProofException, "previous item not found", thy.check_proof, prf)

    def testCheckProofFail2(self):
        """Invalid derivation."""
        prf = Proof(A)
        prf.add_item("C", Thm([A], A), "symmetric", None, ["A1"])

        self.assertRaisesRegex(CheckProofException, "invalid derivation", thy.check_proof, prf)

    def testCheckProofFail3(self):
        """Invalid input to derivation."""
        prf = Proof(A)
        prf.add_item("C", Thm([], Term.mk_implies(A,A)), "implies_intr", None, ["A1"])

        self.assertRaisesRegex(CheckProofException, "invalid input to derivation", thy.check_proof, prf)

    def testCheckProofFail4(self):
        """Output does not match."""
        prf = Proof(A)
        prf.add_item("C", Thm([], Term.mk_implies(A,B)), "implies_intr", A, ["A1"])

        self.assertRaisesRegex(CheckProofException, "output does not match", thy.check_proof, prf)

    def testCheckProofFail5(self):
        """Theorem not found."""
        prf = Proof()
        prf.add_item("C", Thm([], Term.mk_implies(A,B)), "theorem", "random", None)

        self.assertRaisesRegex(CheckProofException, "theorem not found", thy.check_proof, prf)

    def testCheckProofFail6(self):
        """Typing error: non-boolean case."""
        prf = Proof(x)

        self.assertRaisesRegex(CheckProofException, "typing error", thy.check_proof, prf)

    def testCheckProofFail7(self):
        prf = Proof(Comb(Var("P", TFun(Tb, hol_bool)), x))

        self.assertRaisesRegex(CheckProofException, "typing error", thy.check_proof, prf)

if __name__ == "__main__":
    unittest.main()
