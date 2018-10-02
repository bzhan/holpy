# Author: Bohua Zhan

import unittest
from kernel.term import *
from kernel.theory import *
from logic.conv import *

thy = Theory.EmptyTheory()
Ta = TVar("a")
Tf = TFun(Ta,TFun(Ta,Ta))

x = Var("x", Ta)
f = Var("f", Tf)
B0 = Bound(0)

# The term %x. f x x
lf = Abs("x", Ta, Comb2(f, B0, B0))

class ConvTest(unittest.TestCase):
    def testBetaConv(self):
        cv = beta_conv()
        t = Comb(lf, x)
        self.assertEqual(cv.eval(t), Thm.beta_conv(t))
        self.assertEqual(thy.check_proof(cv.get_proof_term(t).export()), Thm.beta_conv(t))

    def testBetaConvFail(self):
        cv = beta_conv()
        self.assertRaises(ConvException, cv.eval, x)
        self.assertRaises(ConvException, cv.get_proof_term, x)

    def testTryConv(self):
        cv = try_conv(beta_conv())
        t = Comb(lf, x)
        self.assertEqual(cv.eval(t), Thm.beta_conv(t))
        self.assertEqual(cv.eval(x), Thm.reflexive(x))

    def testRewrConv(self):
        thy = Theory.EmptyTheory()

        # Setup a theory containing nat, 0, 1.
        thy.add_type_sig("nat", 0)
        natT = Type("nat")
        thy.add_term_sig("0", natT)
        thy.add_term_sig("1", natT)
        nat0 = Const("0", natT)
        nat1 = Const("1", natT)

        # Add axioms 1 = 0
        thy.add_theorem("1_eq_0", Thm.mk_equals(nat1, nat0))
        cv = rewr_conv("1_eq_0", thy.get_theorem("1_eq_0"))
        eq_th = Thm.mk_equals(nat1, nat0)
        self.assertEqual(cv.eval(nat1), eq_th)
        self.assertEqual(thy.check_proof(cv.get_proof_term(nat1).export()), eq_th)
        self.assertRaises(ConvException, cv.eval, nat0)
        self.assertRaises(ConvException, cv.get_proof_term, nat0)

    def testTopBetaConv(self):
        cv = top_conv(beta_conv())
        t = Comb(lf, Comb(lf, x))
        res = Comb2(f, Comb2(f,x,x), Comb2(f,x,x))
        res_th = Thm.mk_equals(t, res)
        self.assertEqual(cv.eval(t), res_th)
        prf = cv.get_proof_term(t).export()
        self.assertEqual(prf.get_num_item(), 6)
        self.assertEqual(thy.check_proof(prf), res_th)

    def testBottomBetaConv(self):
        cv = bottom_conv(beta_conv())
        t = Comb(lf, Comb(lf, x))
        res = Comb2(f, Comb2(f,x,x), Comb2(f,x,x))
        res_th = Thm.mk_equals(t, res)
        self.assertEqual(cv.eval(t), res_th)
        prf = cv.get_proof_term(t).export()
        self.assertEqual(prf.get_num_item(), 5)
        self.assertEqual(thy.check_proof(prf), res_th)

    def testTopBetaConvLarge(self):
        """Stress test for beta conversion in the top-down order."""
        cv = top_conv(beta_conv())
        t = x
        res = x
        for i in range(8):
            t = Comb(lf, t)
            res = Comb2(f, res, res)
        prf = cv.get_proof_term(t).export()
        self.assertEqual(cv.eval(t), Thm.mk_equals(t, res))
        self.assertEqual(prf.get_num_item(), 30)
        self.assertEqual(thy.check_proof(prf), Thm.mk_equals(t, res))

    def testBottomBetaConvLarge(self):
        """Stress test for beta conversion in the bottom-up order."""
        cv = bottom_conv(beta_conv())
        t = x
        res = x
        for i in range(8):
            t = Comb(lf, t)
            res = Comb2(f, res, res)
        prf = cv.get_proof_term(t).export()
        self.assertEqual(cv.eval(t), Thm.mk_equals(t, res))
        self.assertEqual(prf.get_num_item(), 23)
        self.assertEqual(thy.check_proof(prf), Thm.mk_equals(t, res))

    def testLargeSum(self):
        thy = Theory.EmptyTheory()

        # Setup a theory containing nat, 0, 1, f, g, +.
        thy.add_type_sig("nat", 0)
        natT = Type("nat")
        thy.add_term_sig("0", natT)
        thy.add_term_sig("1", natT)
        natFunT = TFun(natT, natT)
        natFunT2 = TFun(natT, natFunT)
        thy.add_term_sig("f", natFunT)
        thy.add_term_sig("g", natFunT)
        thy.add_term_sig("+", natFunT2)
        nat0 = Const("0", natT)
        nat1 = Const("1", natT)
        f = Const("f", natFunT)
        g = Const("g", natFunT)
        plus = Const("+", natFunT2)

        # Add axioms 1 = 0 and f 0 = g 0
        thy.add_theorem("1_eq_0", Thm.mk_equals(nat1, nat0))
        thy.add_theorem("f0_eq_g0", Thm.mk_equals(Comb(f,nat0), Comb(g,nat0)))

        cv = then_conv(
            top_conv(rewr_conv("1_eq_0", thy.get_theorem("1_eq_0"))),
            top_conv(rewr_conv("f0_eq_g0", thy.get_theorem("f0_eq_g0"))))

        f1 = Comb(f,nat1)
        g0 = Comb(g,nat0)
        t = f1
        res = g0
        for i in range(25):
            t = Comb2(plus, t, f1)
            res = Comb2(plus, res, g0)

        prf = cv.get_proof_term(t).export()
        self.assertEqual(cv.eval(t), Thm.mk_equals(t, res))
        self.assertEqual(thy.check_proof(prf), Thm.mk_equals(t, res))

if __name__ == "__main__":
    unittest.main()
