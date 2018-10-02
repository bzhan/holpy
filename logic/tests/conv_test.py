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

    def testTryConv(self):
        cv = try_conv(beta_conv())
        t = Comb(lf, x)
        self.assertEqual(cv.eval(t), Thm.beta_conv(t))
        self.assertEqual(cv.eval(x), Thm.reflexive(x))

    def testTopBetaConv(self):
        cv = top_conv(beta_conv())
        t = Comb(lf, Comb(lf, x))
        res = Comb2(f, Comb2(f,x,x), Comb2(f,x,x))
        res_th = Thm([], Term.mk_equals(t, res))
        self.assertEqual(cv.eval(t), res_th)
        prf = cv.get_proof_term(t).export()
        self.assertEqual(prf.get_num_item(), 6)
        self.assertEqual(thy.check_proof(prf), res_th)

    def testBottomBetaConv(self):
        cv = bottom_conv(beta_conv())
        t = Comb(lf, Comb(lf, x))
        res = Comb2(f, Comb2(f,x,x), Comb2(f,x,x))
        res_th = Thm([], Term.mk_equals(t, res))
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
        self.assertEqual(cv.eval(t), Thm([], Term.mk_equals(t, res)))
        self.assertEqual(prf.get_num_item(), 30)
        self.assertEqual(thy.check_proof(prf), Thm([], Term.mk_equals(t, res)))

    def testBottomBetaConvLarge(self):
        """Stress test for beta conversion in the bottom-up order."""
        cv = bottom_conv(beta_conv())
        t = x
        res = x
        for i in range(8):
            t = Comb(lf, t)
            res = Comb2(f, res, res)
        prf = cv.get_proof_term(t).export()
        self.assertEqual(cv.eval(t), Thm([], Term.mk_equals(t, res)))
        self.assertEqual(prf.get_num_item(), 23)
        self.assertEqual(thy.check_proof(prf), Thm([], Term.mk_equals(t, res)))

if __name__ == "__main__":
    unittest.main()
