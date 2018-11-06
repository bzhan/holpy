# Author: Bohua Zhan

import unittest

from kernel.type import TVar, Type, TFun
from kernel.term import Var, Const, Abs, Bound, Term
from kernel.thm import Thm
from logic.basic import BasicTheory
from logic.proofterm import ProofTerm
from logic.conv import beta_conv, else_conv, try_conv, abs_conv, top_conv, bottom_conv, rewr_conv, ConvException

thy = BasicTheory()
Ta = TVar("a")
Tf = TFun(Ta,Ta,Ta)

x = Var("x", Ta)
f = Var("f", Tf)
B0 = Bound(0)

# The term %x. f x x
lf = Abs("x", Ta, f(B0, B0))

# Setup a theory with nat, 0, 1, f, g, +
arith_thy = BasicTheory()
arith_thy.add_type_sig("nat", 0)
natT = Type("nat")
arith_thy.add_term_sig("0", natT)
arith_thy.add_term_sig("1", natT)
natFunT = TFun(natT, natT)
natFunT2 = TFun(natT, natT, natT)
arith_thy.add_term_sig("f", natFunT)
arith_thy.add_term_sig("g", natFunT)
arith_thy.add_term_sig("+", natFunT2)

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
        thy = arith_thy

        nat0 = Const("0", natT)
        nat1 = Const("1", natT)
        f = Const("f", natFunT)
        g = Const("g", natFunT)
        plus = Const("+", natFunT2)

        # Add axioms 1 = 0 and f x = g x
        thy.add_theorem("1_eq_0", Thm.mk_equals(nat1, nat0))
        thy.add_theorem("f_eq_g", Thm.mk_equals(f(Var("x",natT)), g(Var("x",natT))))

        # Test conversion using 1 = 0
        cv1 = rewr_conv(ProofTerm.theorem(thy, "1_eq_0"))
        eq_th = Thm.mk_equals(nat1, nat0)
        self.assertEqual(cv1(nat1), eq_th)
        self.assertEqual(thy.check_proof(cv1.get_proof_term(nat1).export()), eq_th)
        self.assertRaises(ConvException, cv1, nat0)
        self.assertRaises(ConvException, cv1.get_proof_term, nat0)

        # Test conversion using f x = g x
        cv2 = rewr_conv(ProofTerm.theorem(thy, "f_eq_g"))
        eq0 = Thm.mk_equals(f(nat0), g(nat0))
        eq1 = Thm.mk_equals(f(nat1), g(nat1))
        self.assertEqual(cv2(f(nat0)), eq0)
        self.assertEqual(cv2(f(nat1)), eq1)
        self.assertEqual(thy.check_proof(cv2.get_proof_term(f(nat0)).export()), eq0)
        self.assertEqual(thy.check_proof(cv2.get_proof_term(f(nat1)).export()), eq1)
        self.assertRaises(ConvException, cv1, nat0)
        self.assertRaises(ConvException, cv1.get_proof_term, nat0)

    def testAbsConv(self):
        thy = arith_thy

        nat0 = Const("0", natT)
        nat1 = Const("1", natT)
        f = Const("f", natFunT)
        g = Const("g", natFunT)
        x = Var("x", natT)

        thy.add_theorem("f_eq_g", Thm.mk_equals(f(x), g(x)))
        t = Term.mk_abs(x, f(x))
        cv = abs_conv(rewr_conv(ProofTerm.theorem(thy, "f_eq_g")))
        res_th = Thm.mk_equals(t, Term.mk_abs(x, g(x)))
        self.assertEqual(cv(t), res_th)
        prf = cv.get_proof_term(t).export()
        self.assertEqual(thy.check_proof(prf), res_th)

    def testTopBetaConv(self):
        cv = top_conv(beta_conv())
        t = lf(lf(x))
        res = f(f(x,x),f(x,x))
        res_th = Thm.mk_equals(t, res)
        self.assertEqual(cv(t), res_th)
        prf = cv.get_proof_term(t).export()
        self.assertEqual(prf.get_num_item(), 5)
        self.assertEqual(thy.check_proof(prf), res_th)

    def testBottomBetaConv(self):
        cv = bottom_conv(beta_conv())
        t = lf(lf(x))
        res = f(f(x,x),f(x,x))
        res_th = Thm.mk_equals(t, res)
        self.assertEqual(cv(t), res_th)
        prf = cv.get_proof_term(t).export()
        self.assertEqual(prf.get_num_item(), 4)
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
        self.assertEqual(cv(t), Thm.mk_equals(t, res))
        self.assertEqual(prf.get_num_item(), 29)
        self.assertEqual(thy.check_proof(prf), Thm.mk_equals(t, res))

    def testBottomBetaConvLarge(self):
        """Stress test for beta conversion in the bottom-up order."""
        cv = bottom_conv(beta_conv())
        t = x
        res = x
        for i in range(8):
            t = lf(t)
            res = f(res, res)
        prf = cv.get_proof_term(t).export()
        self.assertEqual(cv(t), Thm.mk_equals(t, res))
        self.assertEqual(prf.get_num_item(), 22)
        self.assertEqual(thy.check_proof(prf), Thm.mk_equals(t, res))

    def testTopBetaConvAbs(self):
        cv = top_conv(beta_conv())

        # %x. (%a. f a) x reduces to %x. f x.
        t = Abs("x", Ta, Abs("a", Ta, f(B0))(B0))
        res = Abs("x", Ta, f(B0))

        prf = cv.get_proof_term(t).export()
        self.assertEqual(cv(t), Thm.mk_equals(t, res))
        self.assertEqual(prf.get_num_item(), 2)
        self.assertEqual(thy.check_proof(prf), Thm.mk_equals(t, res))

    def testLargeSum(self):
        thy = arith_thy
        thy.check_level = 1

        nat0 = Const("0", natT)
        nat1 = Const("1", natT)
        f = Const("f", natFunT)
        g = Const("g", natFunT)
        plus = Const("+", natFunT2)

        # Add axioms 1 = 0 and f x = g x
        thy.add_theorem("1_eq_0", Thm.mk_equals(nat1, nat0))
        thy.add_theorem("f_eq_g", Thm.mk_equals(f(Var("x",natT)), g(Var("x",natT))))

        cv = top_conv(else_conv(
            rewr_conv(ProofTerm.theorem(thy, "f_eq_g")),
            rewr_conv(ProofTerm.theorem(thy, "1_eq_0"))))

        f1 = f(nat1)
        g0 = g(nat0)
        t = f1
        res = g0
        for i in range(10):
            t = plus(t, f1)
            res = plus(res, g0)

        prf = cv.get_proof_term(t).export()
        self.assertEqual(cv(t), Thm.mk_equals(t, res))
        self.assertEqual(thy.check_proof(prf), Thm.mk_equals(t, res))

if __name__ == "__main__":
    unittest.main()
