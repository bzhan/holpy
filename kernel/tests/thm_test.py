# Author: Bohua Zhan

import unittest

from kernel.type import STVar, TVar, TFun, BoolType, TyInst
from kernel.term import Term, SVar, Var, Const, Comb, Abs, Bound, Implies, Eq, Forall, \
    Inst, TypeCheckException
from kernel.thm import Thm, InvalidDerivationException
from syntax.settings import global_setting

Ta = TVar("a")
Tb = TVar("b")
STa = STVar("a")
Tab = TFun(Ta, Tb)
A = Var("A", BoolType)
B = Var("B", BoolType)
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
            with global_setting(unicode=False):
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
        self.assertEqual(Thm.implies_intr(A, th), Thm([], Implies(A,B)))

    def testImpliesIntr2(self):
        th = Thm([A, B], B)
        self.assertEqual(Thm.implies_intr(A, th), Thm([B], Implies(A,B)))

    def testImpliesIntr3(self):
        th = Thm([], B)
        self.assertEqual(Thm.implies_intr(A, th), Thm([], Implies(A,B)))

    def testImpliesElim(self):
        th1 = Thm([], Implies(A,B))
        th2 = Thm([], A)
        self.assertEqual(Thm.implies_elim(th1, th2), Thm([], B))

    def testImpliesElim2(self):
        th1 = Thm([B], Implies(A,B))
        th2 = Thm([B], A)
        self.assertEqual(Thm.implies_elim(th1, th2), Thm([B], B))

    def testImpliesElimFail(self):
        th1 = Thm([], A)
        th2 = Thm([], B)
        self.assertRaises(InvalidDerivationException, Thm.implies_elim, th1, th2)

    def testImpliesElimFail2(self):
        th1 = Thm([], Implies(A,B))
        th2 = Thm([], B)
        self.assertRaises(InvalidDerivationException, Thm.implies_elim, th1, th2)

    def testReflexive(self):
        self.assertEqual(Thm.reflexive(x), Thm([], Eq(x,x)))

    def testSymmetric(self):
        th = Thm([A], Eq(x,y))
        self.assertEqual(Thm.symmetric(th), Thm([A], Eq(y,x)))

    def testSymmetricFail(self):
        th = Thm([], A)
        self.assertRaises(InvalidDerivationException, Thm.symmetric, th)

    def testTransitive(self):
        th1 = Thm([A], Eq(x,y))
        th2 = Thm([B], Eq(y,z))
        self.assertEqual(Thm.transitive(th1, th2), Thm([A,B], Eq(x,z)))

    def testTransitiveFail(self):
        th1 = Thm([], Eq(x,y))
        th2 = Thm([], B)
        self.assertRaises(InvalidDerivationException, Thm.transitive, th1, th2)

    def testTransitiveFail2(self):
        th1 = Thm([], A)
        th2 = Thm([], Eq(x,y))
        self.assertRaises(InvalidDerivationException, Thm.transitive, th1, th2)

    def testTransitiveFail3(self):
        th1 = Thm([], Eq(x,y))
        th2 = Thm([], Eq(z,x))
        self.assertRaises(InvalidDerivationException, Thm.transitive, th1, th2)

    def testCombination(self):
        th1 = Thm([A], Eq(f,g))
        th2 = Thm([B], Eq(x,y))
        self.assertEqual(Thm.combination(th1, th2), Thm([A,B], Eq(f(x),g(y))))

    def testCombinationFail(self):
        th1 = Thm([], Eq(x,y))
        th2 = Thm([], B)
        self.assertRaises(InvalidDerivationException, Thm.combination, th1, th2)

    def testCombinationFail2(self):
        th1 = Thm([], A)
        th2 = Thm([], Eq(x,y))
        self.assertRaises(InvalidDerivationException, Thm.combination, th1, th2)

    def testEqualIntr(self):
        th1 = Thm([A], Implies(A,B))
        th2 = Thm([B], Implies(B,A))
        self.assertEqual(Thm.equal_intr(th1, th2), Thm([A,B], Eq(A,B)))

    def testEqualIntrFail(self):
        th1 = Thm([], Implies(A,B))
        th2 = Thm([], A)
        self.assertRaises(InvalidDerivationException, Thm.equal_intr, th1, th2)

    def testEqualIntrFail2(self):
        th1 = Thm([], B)
        th2 = Thm([], Implies(B,A))
        self.assertRaises(InvalidDerivationException, Thm.equal_intr, th1, th2)

    def testEqualIntrFail3(self):
        th1 = Thm([], Implies(A,B))
        th2 = Thm([], Implies(A,B))
        self.assertRaises(InvalidDerivationException, Thm.equal_intr, th1, th2)

    def testEqualElim(self):
        th1 = Thm([A], Eq(A,B))
        th2 = Thm([B], A)
        self.assertEqual(Thm.equal_elim(th1, th2), Thm([A,B], B))

    def testEqualElimFail(self):
        th1 = Thm([A], Implies(A,B))
        th2 = Thm([B], A)
        self.assertRaises(InvalidDerivationException, Thm.equal_elim, th1, th2)

    def testEqualElimFail2(self):
        th1 = Thm([A], Eq(A,B))
        th2 = Thm([B], B)
        self.assertRaises(InvalidDerivationException, Thm.equal_elim, th1, th2)

    def testSubstType(self):
        x_eq_y = Eq(Var("x", STa), Var("y", STa))
        th = Thm([x_eq_y], x_eq_y)
        xb_eq_yb = Eq(Var("x", Tb), Var("y", Tb))
        self.assertEqual(Thm.subst_type(TyInst(a=Tb), th), Thm([xb_eq_yb], xb_eq_yb))

    def testSubstitution(self):
        x_eq_y = Eq(SVar('x', Ta), SVar('y', Ta))
        th = Thm([x_eq_y], x_eq_y)
        y_eq_x = Eq(y,x)
        self.assertEqual(Thm.substitution(Inst(x=y, y=x), th), Thm([y_eq_x], y_eq_x))

    def testSubstitutionFail(self):
        x_eq_y = Eq(SVar('x', Ta), SVar('y', Ta))
        th = Thm([x_eq_y], x_eq_y)
        self.assertRaises(InvalidDerivationException, Thm.substitution, Inst(x=Var("a", Tb)), th)

    def testBetaConv(self):
        t = Comb(Abs("x", Ta, Bound(0)), x)
        self.assertEqual(Thm.beta_conv(t), Thm([], Eq(t, x)))

    def testBetaConvFail(self):
        self.assertRaises(InvalidDerivationException, Thm.beta_conv, x)

    def testAbstractOver(self):
        th = Thm([], Eq(x,y))
        t_res = Eq(Abs("x",Ta,Bound(0)),Abs("x",Ta,y))
        self.assertEqual(Thm.abstraction(x, th), Thm([], t_res))

    def testAbstractOverFail(self):
        x_eq_y = Eq(x,y)
        th = Thm([x_eq_y], x_eq_y)
        self.assertRaises(InvalidDerivationException, Thm.abstraction, x, th)

    def testAbstractOverFail2(self):
        th = Thm([], Eq(x,y))
        self.assertRaises(InvalidDerivationException, Thm.abstraction, Var("x", Tb), th)

    def testAbstractOverFail3(self):
        th = Thm([], Eq(x,y))
        self.assertRaises(InvalidDerivationException, Thm.abstraction, f(x), th)

    def testAbstractOverFail4(self):
        th = Thm([], Implies(x,y))
        self.assertRaises(InvalidDerivationException, Thm.abstraction, x, th)

    def testForallIntr(self):
        th = Thm([], Eq(x,y))
        t_res = Forall(x, Eq(x, y))
        self.assertEqual(Thm.forall_intr(x, th), Thm([], t_res))

    def testForallIntr2(self):
        """Also OK if the variable does not appear in theorem."""
        th = Thm([], Eq(x,y))
        t_res = Forall(z, Eq(x, y))
        self.assertEqual(Thm.forall_intr(z, th), Thm([], t_res))

    def testForallIntrFail(self):
        x_eq_y = Eq(x,y)
        th = Thm([x_eq_y], x_eq_y)
        self.assertRaises(InvalidDerivationException, Thm.forall_intr, x, th)

    def testForallIntrFail2(self):
        th = Thm([], Eq(x,y))
        self.assertRaises(InvalidDerivationException, Thm.forall_intr, Const("c", Ta), th)

    def testForallElim(self):
        P = Var("P", TFun(Ta, BoolType))
        th = Thm([], Forall(x, P(x)))
        self.assertEqual(Thm.forall_elim(y, th), Thm([], P(y)))

    def testForallElimFail(self):
        th = Thm([], Eq(x,y))
        self.assertRaises(InvalidDerivationException, Thm.forall_elim, x, th)

    def testForallElimFail2(self):
        P = Var("P", TFun(Ta, BoolType))
        th = Thm([], Forall(x, P(x)))
        self.assertRaises(InvalidDerivationException, Thm.forall_elim, A, th)


if __name__ == "__main__":
    unittest.main()
