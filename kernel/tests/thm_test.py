# Author: Bohua Zhan

import unittest

from kernel.type import STVar, TVar, TFun, boolT
from kernel.term import Term, SVar, Var, Const, Comb, Abs, Bound, TypeCheckException
from kernel.thm import Thm, InvalidDerivationException

Ta = TVar("a")
Tb = TVar("b")
STa = STVar("a")
Tab = TFun(Ta, Tb)
A = Var("A", boolT)
B = Var("B", boolT)
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

        for th, str_th in test_data:
            self.assertEqual(str(th), str_th)

    def testCheckThmType(self):
        self.assertEqual(Thm([A], A).check_thm_type(), None)

    def testCheckThmTypeFail(self):
        self.assertRaises(TypeCheckException, Thm([x], x).check_thm_type)

    def testCheckCanProve(self):
        test_data = [
            (Thm([A], A), Thm([A], A), True),
            (Thm([A], A), Thm([A, B], A), True),
            (Thm([A], A), Thm([], A), False),
            (Thm([A], A), Thm([A], B), False),
        ]

        for th, target, res in test_data:
            self.assertEqual(th.can_prove(target), res)

    def testAssume(self):
        self.assertEqual(Thm.assume(A), Thm([A], A))

    def testImpliesIntr(self):
        th = Thm([A], B)
        self.assertEqual(Thm.implies_intr(A, th), Thm([], Term.mk_implies(A,B)))

    def testImpliesIntr2(self):
        th = Thm([A, B], B)
        self.assertEqual(Thm.implies_intr(A, th), Thm([B], Term.mk_implies(A,B)))

    def testImpliesIntr3(self):
        th = Thm([], B)
        self.assertEqual(Thm.implies_intr(A, th), Thm([], Term.mk_implies(A,B)))

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
        self.assertEqual(Thm.reflexive(x), Thm.mk_equals(x,x))

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
        th1 = Thm.mk_equals(x,y)
        th2 = Thm([], B)
        self.assertRaises(InvalidDerivationException, Thm.transitive, th1, th2)

    def testTransitiveFail2(self):
        th1 = Thm([], A)
        th2 = Thm.mk_equals(x,y)
        self.assertRaises(InvalidDerivationException, Thm.transitive, th1, th2)

    def testTransitiveFail3(self):
        th1 = Thm.mk_equals(x,y)
        th2 = Thm.mk_equals(z,x)
        self.assertRaises(InvalidDerivationException, Thm.transitive, th1, th2)

    def testCombination(self):
        th1 = Thm([A], Term.mk_equals(f,g))
        th2 = Thm([B], Term.mk_equals(x,y))
        self.assertEqual(Thm.combination(th1, th2), Thm([A,B], Term.mk_equals(f(x),g(y))))

    def testCombinationFail(self):
        th1 = Thm.mk_equals(x,y)
        th2 = Thm([], B)
        self.assertRaises(InvalidDerivationException, Thm.combination, th1, th2)

    def testCombinationFail2(self):
        th1 = Thm([], A)
        th2 = Thm.mk_equals(x,y)
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
        x_eq_y = Term.mk_equals(Var("x", STa), Var("y", STa))
        th = Thm([x_eq_y], x_eq_y)
        xb_eq_yb = Term.mk_equals(Var("x", Tb), Var("y", Tb))
        self.assertEqual(Thm.subst_type({"a" : Tb}, th), Thm([xb_eq_yb], xb_eq_yb))

    def testSubstitution(self):
        x_eq_y = Term.mk_equals(SVar('x', Ta), SVar('y', Ta))
        th = Thm([x_eq_y], x_eq_y)
        y_eq_x = Term.mk_equals(y,x)
        self.assertEqual(Thm.substitution({"x" : y, "y" : x}, th), Thm([y_eq_x], y_eq_x))

    def testSubstitutionFail(self):
        x_eq_y = Term.mk_equals(SVar('x', Ta), SVar('y', Ta))
        th = Thm([x_eq_y], x_eq_y)
        self.assertRaises(InvalidDerivationException, Thm.substitution, {"x" : Var("a", Tb)}, th)

    def testBetaConv(self):
        t = Comb(Abs("x", Ta, Bound(0)), x)
        self.assertEqual(Thm.beta_conv(t), Thm.mk_equals(t, x))

    def testBetaConvFail(self):
        self.assertRaises(InvalidDerivationException, Thm.beta_conv, x)

    def testAbstractOver(self):
        th = Thm.mk_equals(x,y)
        t_res = Term.mk_equals(Abs("x",Ta,Bound(0)),Abs("x",Ta,y))
        self.assertEqual(Thm.abstraction(x, th), Thm([], t_res))

    def testAbstractOverFail(self):
        x_eq_y = Term.mk_equals(x,y)
        th = Thm([x_eq_y], x_eq_y)
        self.assertRaises(InvalidDerivationException, Thm.abstraction, x, th)

    def testAbstractOverFail2(self):
        th = Thm.mk_equals(x,y)
        self.assertRaises(InvalidDerivationException, Thm.abstraction, Var("x", Tb), th)

    def testAbstractOverFail3(self):
        th = Thm.mk_equals(x,y)
        self.assertRaises(InvalidDerivationException, Thm.abstraction, f(x), th)

    def testAbstractOverFail4(self):
        th = Thm([], Term.mk_implies(x,y))
        self.assertRaises(InvalidDerivationException, Thm.abstraction, x, th)

    def testForallIntr(self):
        th = Thm.mk_equals(x,y)
        t_res = Term.mk_all(x, Term.mk_equals(x, y))
        self.assertEqual(Thm.forall_intr(x, th), Thm([], t_res))

    def testForallIntr2(self):
        """Also OK if the variable does not appear in theorem."""
        th = Thm.mk_equals(x,y)
        t_res = Term.mk_all(z, Term.mk_equals(x, y))
        self.assertEqual(Thm.forall_intr(z, th), Thm([], t_res))

    def testForallIntrFail(self):
        x_eq_y = Term.mk_equals(x,y)
        th = Thm([x_eq_y], x_eq_y)
        self.assertRaises(InvalidDerivationException, Thm.forall_intr, x, th)

    def testForallIntrFail2(self):
        th = Thm.mk_equals(x,y)
        self.assertRaises(InvalidDerivationException, Thm.forall_intr, Const("c", Ta), th)

    def testForallElim(self):
        P = Var("P", TFun(Ta, boolT))
        th = Thm([], Term.mk_all(x, P(x)))
        self.assertEqual(Thm.forall_elim(y, th), Thm([], P(y)))

    def testForallElimFail(self):
        th = Thm.mk_equals(x,y)
        self.assertRaises(InvalidDerivationException, Thm.forall_elim, x, th)

    def testForallElimFail2(self):
        P = Var("P", TFun(Ta, boolT))
        th = Thm([], Term.mk_all(x, P(x)))
        self.assertRaises(InvalidDerivationException, Thm.forall_elim, A, th)


if __name__ == "__main__":
    unittest.main()
