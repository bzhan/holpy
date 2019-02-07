# Author: Bohua Zhan

import unittest

from kernel.type import TVar, Type, TFun
from kernel.term import Term, Var, Const, Abs, Bound, Term
from kernel.thm import Thm
from logic import basic
from logic.proofterm import ProofTerm
from logic.conv import beta_conv, else_conv, try_conv, abs_conv, top_conv, bottom_conv, \
    rewr_conv, rewr_conv_thm, ConvException
from logic import nat

thy = basic.loadTheory('logic_base')
abs = Term.mk_abs
eq = Thm.mk_equals

Ta = TVar("a")
x = Var("x", Ta)
f = Var("f", TFun(Ta, Ta, Ta))
lf = abs(x, f(x,x))

natT = nat.natT
zero = nat.zero
one = nat.one
plus = nat.mk_plus

class ConvTest(unittest.TestCase):
    def testBetaConv(self):
        cv = beta_conv()
        t = lf(x)
        self.assertEqual(cv(t), Thm.beta_conv(t))
        self.assertEqual(thy.check_proof(cv.get_proof_term(t).export()), Thm.beta_conv(t))

    def testBetaConvFail(self):
        cv = beta_conv()
        self.assertRaises(ConvException, cv, x)
        self.assertRaises(ConvException, cv.get_proof_term, x)

    def testTryConv(self):
        cv = try_conv(beta_conv())
        t = lf(x)
        self.assertEqual(cv(t), Thm.beta_conv(t))
        self.assertEqual(cv(x), Thm.reflexive(x))

    def testRewrConv(self):
        f = Const("f", TFun(natT, natT))
        g = Const("g", TFun(natT, natT))
        x = Var("x", natT)

        seq_dict = {"A1": eq(one, zero), "A2": eq(f(x), g(x))}

        # Test conversion using 1 = 0
        cv1 = rewr_conv(ProofTerm.atom("A1", seq_dict["A1"]))
        eq_th = eq(one, zero)
        prf = cv1.get_proof_term(one).export()
        self.assertEqual(cv1(one), eq_th)
        self.assertEqual(thy.check_proof_incr(0, seq_dict, prf), eq_th)
        self.assertRaises(ConvException, cv1, zero)
        self.assertRaises(ConvException, cv1.get_proof_term, zero)

        # Test conversion using f x = g x
        cv2 = rewr_conv(ProofTerm.atom("A2", seq_dict["A2"]))
        eq0 = eq(f(zero), g(zero))
        eq1 = eq(f(one), g(one))
        self.assertEqual(cv2(f(zero)), eq0)
        self.assertEqual(cv2(f(one)), eq1)
        prf0 = cv2.get_proof_term(f(zero)).export()
        prf1 = cv2.get_proof_term(f(one)).export()
        self.assertEqual(thy.check_proof_incr(0, seq_dict, prf0), eq0)
        self.assertEqual(thy.check_proof_incr(0, seq_dict, prf1), eq1)
        self.assertRaises(ConvException, cv1, zero)
        self.assertRaises(ConvException, cv1.get_proof_term, zero)

    def testAbsConv(self):
        nat0 = Const("zero", natT)
        nat1 = Const("one", natT)
        f = Const("f", TFun(natT, natT))
        g = Const("g", TFun(natT, natT))
        x = Var("x", natT)

        thy.add_theorem("f_eq_g", eq(f(x), g(x)))
        t = Term.mk_abs(x, f(x))
        cv = abs_conv(rewr_conv_thm(thy, "f_eq_g"))
        res_th = eq(t, Term.mk_abs(x, g(x)))
        self.assertEqual(cv(t), res_th)
        prf = cv.get_proof_term(t).export()
        self.assertEqual(thy.check_proof(prf), res_th)

    def testTopBetaConv(self):
        cv = top_conv(beta_conv())
        t = lf(lf(x))
        res = f(f(x,x),f(x,x))
        res_th = eq(t, res)
        self.assertEqual(cv(t), res_th)
        prf = cv.get_proof_term(t).export()
        self.assertEqual(len(prf.items), 5)
        self.assertEqual(thy.check_proof(prf), res_th)

    def testBottomBetaConv(self):
        cv = bottom_conv(beta_conv())
        t = lf(lf(x))
        res = f(f(x,x),f(x,x))
        res_th = eq(t, res)
        self.assertEqual(cv(t), res_th)
        prf = cv.get_proof_term(t).export()
        self.assertEqual(len(prf.items), 4)
        self.assertEqual(thy.check_proof(prf), res_th)

    def testTopBetaConvLarge(self):
        """Stress test for beta conversion in the top-down order."""
        cv = top_conv(beta_conv())
        t = x
        res = x
        for i in range(8):
            t = lf(t)
            res = f(res, res)
        prf = cv.get_proof_term(t).export()
        self.assertEqual(cv(t), eq(t, res))
        self.assertEqual(len(prf.items), 29)
        self.assertEqual(thy.check_proof(prf), eq(t, res))

    def testBottomBetaConvLarge(self):
        """Stress test for beta conversion in the bottom-up order."""
        cv = bottom_conv(beta_conv())
        t = x
        res = x
        for i in range(8):
            t = lf(t)
            res = f(res, res)
        prf = cv.get_proof_term(t).export()
        self.assertEqual(cv(t), eq(t, res))
        self.assertEqual(len(prf.items), 22)
        self.assertEqual(thy.check_proof(prf), eq(t, res))

    def testTopBetaConvAbs(self):
        cv = top_conv(beta_conv())

        # %x. (%a. f a) x reduces to %x. f x.
        a = Var("a", Ta)
        t = abs(x, abs(a, f(a))(x))
        res = abs(x, f(x))

        prf = cv.get_proof_term(t).export()
        self.assertEqual(cv(t), eq(t, res))
        self.assertEqual(len(prf.items), 2)
        self.assertEqual(thy.check_proof(prf), eq(t, res))

    def testLargeSum(self):
        f = Const("f", TFun(natT, natT))
        g = Const("g", TFun(natT, natT))
        x = Var("x", natT)

        seq_dict = {"A1": eq(one, zero), "A2": eq(f(x), g(x))}
        cv = top_conv(else_conv(
            rewr_conv(ProofTerm.atom("A1", seq_dict["A1"])),
            rewr_conv(ProofTerm.atom("A2", seq_dict["A2"]))))

        f1 = f(one)
        g0 = g(zero)
        t = plus(*([f1] * 10))
        res = plus(*([g0] * 10))
        prf = cv.get_proof_term(t).export()
        self.assertEqual(cv(t), eq(t, res))
        thy.check_level = 1
        self.assertEqual(thy.check_proof_incr(0, seq_dict, prf), eq(t, res))
        thy.check_level = 0


if __name__ == "__main__":
    unittest.main()
