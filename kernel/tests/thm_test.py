# Author: Bohua Zhan

import unittest
from kernel.type import *
from kernel.term import *
from kernel.thm import *

Ta = TVar("a")
Tb = TVar("b")
Tab = TFun(Ta, Tb)
A = Var("A", hol_bool)
B = Var("B", hol_bool)
x = Var("x", Ta)
y = Var("y", Ta)
z = Var("z", Ta)
f = Var("f", Tab)
g = Var("g", Tab)

class ThmTest(unittest.TestCase):
    def testPrintThm(self):
        test_data = [
            (Thm([], A), "|- A"),
            (Thm([A], A), "A |- A"),
            (Thm([A,B], A), "A, B |- A"),
        ]

        for (th, str_th) in test_data:
            self.assertEqual(str(th), str_th)

    def testCheckThmType(self):
        self.assertEqual(Thm([A], A).check_thm_type(), None)

    def testCheckThmTypeFail(self):
        self.assertRaises(TypeCheckException, Thm([x], x).check_thm_type)

    def testAssume(self):
        self.assertEqual(Thm.assume(A), Thm([A], A))

    def testImpliesIntr(self):
        th = Thm([A], B)
        self.assertEqual(Thm.implies_intr(th, A), Thm([], Term.mk_implies(A,B)))

    def testImpliesIntr2(self):
        th = Thm([A, B], B)
        self.assertEqual(Thm.implies_intr(th, A), Thm([B], Term.mk_implies(A,B)))

    def testImpliesIntr3(self):
        th = Thm([], B)
        self.assertEqual(Thm.implies_intr(th, A), Thm([], Term.mk_implies(A,B)))

    def testImpliesElim(self):
        th1 = Thm([], Term.mk_implies(A,B))
        th2 = Thm([], A)
        self.assertEqual(Thm.implies_elim(th1, th2), Thm([], B))

    def testImpliesElim2(self):
        th1 = Thm([B], Term.mk_implies(A,B))
        th2 = Thm([B], A)
        self.assertEqual(Thm.implies_elim(th1, th2), Thm([B], B))

    def testImpliesElimFail(self):
        th1 = Thm([], A)
        th2 = Thm([], B)
        self.assertRaises(InvalidDerivationException, Thm.implies_elim, th1, th2)

    def testImpliesElimFail2(self):
        th1 = Thm([], Term.mk_implies(A,B))
        th2 = Thm([], B)
        self.assertRaises(InvalidDerivationException, Thm.implies_elim, th1, th2)

    def testReflexive(self):
        self.assertEqual(Thm.reflexive(x), Thm([], Term.mk_equals(x,x)))

    def testSymmetric(self):
        th = Thm([A], Term.mk_equals(x,y))
        self.assertEqual(Thm.symmetric(th), Thm([A], Term.mk_equals(y,x)))

    def testSymmetricFail(self):
        th = Thm([], A)
        self.assertRaises(InvalidDerivationException, Thm.symmetric, th)

    def testTransitive(self):
        th1 = Thm([A], Term.mk_equals(x,y))
        th2 = Thm([B], Term.mk_equals(y,z))
        self.assertEqual(Thm.transitive(th1, th2), Thm([A,B], Term.mk_equals(x,z)))

    def testTransitiveFail(self):
        th1 = Thm([], Term.mk_equals(x,y))
        th2 = Thm([], B)
        self.assertRaises(InvalidDerivationException, Thm.transitive, th1, th2)

    def testTransitiveFail2(self):
        th1 = Thm([], A)
        th2 = Thm([], Term.mk_equals(x,y))
        self.assertRaises(InvalidDerivationException, Thm.transitive, th1, th2)

    def testTransitiveFail3(self):
        th1 = Thm([], Term.mk_equals(x,y))
        th2 = Thm([], Term.mk_equals(z,x))
        self.assertRaises(InvalidDerivationException, Thm.transitive, th1, th2)

    def testCombination(self):
        th1 = Thm([A], Term.mk_equals(f,g))
        th2 = Thm([B], Term.mk_equals(x,y))
        self.assertEqual(Thm.combination(th1, th2), Thm([A,B], Term.mk_equals(Comb(f,x),Comb(g,y))))

    def testCombinationFail(self):
        th1 = Thm([], Term.mk_equals(x,y))
        th2 = Thm([], B)
        self.assertRaises(InvalidDerivationException, Thm.combination, th1, th2)

    def testCombinationFail2(self):
        th1 = Thm([], A)
        th2 = Thm([], Term.mk_equals(x,y))
        self.assertRaises(InvalidDerivationException, Thm.combination, th1, th2)

    def testEqualIntr(self):
        th1 = Thm([A], Term.mk_implies(A,B))
        th2 = Thm([B], Term.mk_implies(B,A))
        self.assertEqual(Thm.equal_intr(th1, th2), Thm([A,B], Term.mk_equals(A,B)))

    def testEqualIntrFail(self):
        th1 = Thm([], Term.mk_implies(A,B))
        th2 = Thm([], A)
        self.assertRaises(InvalidDerivationException, Thm.equal_intr, th1, th2)

    def testEqualIntrFail2(self):
        th1 = Thm([], B)
        th2 = Thm([], Term.mk_implies(B,A))
        self.assertRaises(InvalidDerivationException, Thm.equal_intr, th1, th2)

    def testEqualIntrFail3(self):
        th1 = Thm([], Term.mk_implies(A,B))
        th2 = Thm([], Term.mk_implies(A,B))
        self.assertRaises(InvalidDerivationException, Thm.equal_intr, th1, th2)

    def testEqualElim(self):
        th1 = Thm([A], Term.mk_equals(A,B))
        th2 = Thm([B], A)
        self.assertEqual(Thm.equal_elim(th1, th2), Thm([A,B], B))

    def testEqualElimFail(self):
        th1 = Thm([A], Term.mk_implies(A,B))
        th2 = Thm([B], A)
        self.assertRaises(InvalidDerivationException, Thm.equal_elim, th1, th2)

    def testEqualElimFail2(self):
        th1 = Thm([A], Term.mk_equals(A,B))
        th2 = Thm([B], B)
        self.assertRaises(InvalidDerivationException, Thm.equal_elim, th1, th2)

    def testSubstType(self):
        x_eq_y = Term.mk_equals(x,y)
        th = Thm([x_eq_y], x_eq_y)
        xb_eq_yb = Term.mk_equals(Var("x", Tb), Var("y", Tb))
        self.assertEqual(Thm.subst_type(th, {"a" : Tb}), Thm([xb_eq_yb], xb_eq_yb))

    def testSubstitution(self):
        x_eq_y = Term.mk_equals(x,y)
        th = Thm([x_eq_y], x_eq_y)
        y_eq_x = Term.mk_equals(y,x)
        self.assertEqual(Thm.substitution(th, {"x" : y, "y" : x}), Thm([y_eq_x], y_eq_x))

    def testSubstitutionFail(self):
        x_eq_y = Term.mk_equals(x,y)
        th = Thm([x_eq_y], x_eq_y)
        self.assertRaises(InvalidDerivationException, Thm.substitution, th, {"x" : Var("a", Tb)})

    def testBetaConv(self):
        t = Comb(Abs("x", Ta, Bound(0)), x)
        self.assertEqual(Thm.beta_conv(t), Thm([], Term.mk_equals(t, x)))

    def testBetaConvFail(self):
        self.assertRaises(InvalidDerivationException, Thm.beta_conv, x)

    def testAbstractOver(self):
        th = Thm([], Term.mk_equals(x,y))
        t_res = Term.mk_equals(Abs("x",Ta,Bound(0)),Abs("x",Ta,y))
        self.assertEqual(Thm.abstraction(th, x), Thm([], t_res))

    def testAbstractOverFail(self):
        x_eq_y = Term.mk_equals(x,y)
        th = Thm([x_eq_y], x_eq_y)
        self.assertRaises(InvalidDerivationException, Thm.abstraction, th, x)

    def testAbstractOverFail2(self):
        th = Thm([], Term.mk_equals(x,y))
        self.assertRaises(InvalidDerivationException, Thm.abstraction, th, Var("x", Tb))

    def testAbstractOverFail3(self):
        th = Thm([], Term.mk_equals(x,y))
        self.assertRaises(InvalidDerivationException, Thm.abstraction, th, Comb(f,x))

    def testAbstractOverFail4(self):
        th = Thm([], Term.mk_implies(x,y))
        self.assertRaises(InvalidDerivationException, Thm.abstraction, th, x)

if __name__ == "__main__":
    unittest.main()
