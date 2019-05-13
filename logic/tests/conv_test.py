# Author: Bohua Zhan

import unittest

from kernel.type import TVar, Type, TFun
from kernel.term import Term, Var, Const, Abs, Bound, Term
from kernel.thm import Thm
from kernel.proof import Proof
from logic import basic
from logic.proofterm import ProofTerm
from logic.conv import beta_conv, else_conv, try_conv, abs_conv, top_conv, bottom_conv, \
    top_sweep_conv, arg_conv, rewr_conv, ConvException
from logic import nat

thy = basic.load_theory('logic_base')
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
        self.assertEqual(cv.eval(thy, t), Thm.beta_conv(t))
        self.assertEqual(thy.check_proof(cv.get_proof_term(thy, t).export()), Thm.beta_conv(t))

    def testBetaConvFail(self):
        cv = beta_conv()
        self.assertRaises(ConvException, cv.eval, thy, x)
        self.assertRaises(ConvException, cv.get_proof_term, thy, x)

    def testTryConv(self):
        cv = try_conv(beta_conv())
        t = lf(x)
        self.assertEqual(cv.eval(thy, t), Thm.beta_conv(t))
        self.assertEqual(cv.eval(thy, x), Thm.reflexive(x))

    def testRewrConv(self):
        f = Const("f", TFun(natT, natT))
        g = Const("g", TFun(natT, natT))
        x = Var("x", natT)

        assum0 = eq(one, zero)
        assum1 = eq(f(x), g(x))

        # Test conversion using 1 = 0
        cv1 = rewr_conv(ProofTerm.atom(0, assum0))
        prf = Proof()
        prf.add_item(0, "sorry", th=assum0)
        eq_th = eq(one, zero)
        cv1.get_proof_term(thy, one).export(prf=prf)
        self.assertEqual(cv1.eval(thy, one), eq_th)
        self.assertEqual(thy.check_proof(prf), eq_th)
        self.assertRaises(ConvException, cv1.eval, thy, zero)
        self.assertRaises(ConvException, cv1.get_proof_term, thy, zero)

        # Test conversion using f x = g x
        cv2 = rewr_conv(ProofTerm.atom(0, assum1))
        eq0 = eq(f(zero), g(zero))
        eq1 = eq(f(one), g(one))
        self.assertEqual(cv2.eval(thy, f(zero)), eq0)
        self.assertEqual(cv2.eval(thy, f(one)), eq1)

        prf0 = Proof()
        prf0.add_item(0, "sorry", th=assum1)
        cv2.get_proof_term(thy, f(zero)).export(prf=prf0)
        self.assertEqual(thy.check_proof(prf0), eq0)
        self.assertRaises(ConvException, cv1.eval, thy, zero)

        prf1 = Proof()
        prf1.add_item(0, "sorry", th=assum1)
        cv2.get_proof_term(thy, f(one)).export(prf=prf1)
        self.assertEqual(thy.check_proof(prf1), eq1)
        self.assertRaises(ConvException, cv1.get_proof_term, thy, zero)

    def testRewrConvWithAssum(self):
        x = Const("x", natT)
        y = Const("y", natT)
        x_eq_y = Term.mk_equals(x, y)
        th = Thm([], Term.mk_implies(x_eq_y, x_eq_y))
        cv = arg_conv(rewr_conv(ProofTerm.atom(0, th)))
        f = Const("f", TFun(natT, natT))
        res = Thm([x_eq_y], Term.mk_equals(f(x), f(y)))
        self.assertEqual(cv.eval(thy, f(x)), res)
        prf = Proof()
        prf.add_item(0, "sorry", th=th)
        cv.get_proof_term(thy, f(x)).export(prf=prf)
        self.assertEqual(thy.check_proof(prf), res)

    def testAbsConv(self):
        nat0 = Const("zero", natT)
        nat1 = Const("one", natT)
        f = Const("f", TFun(natT, natT))
        g = Const("g", TFun(natT, natT))
        x = Var("x", natT)

        thy.add_theorem("f_eq_g", eq(f(x), g(x)))
        t = Term.mk_abs(x, f(x))
        cv = abs_conv(rewr_conv("f_eq_g"))
        res_th = eq(t, Term.mk_abs(x, g(x)))
        self.assertEqual(cv.eval(thy, t), res_th)
        prf = cv.get_proof_term(thy, t).export()
        self.assertEqual(thy.check_proof(prf), res_th)

    def testTopBetaConv(self):
        cv = top_conv(beta_conv())
        t = lf(lf(x))
        res = f(f(x,x),f(x,x))
        res_th = eq(t, res)
        self.assertEqual(cv.eval(thy, t), res_th)
        prf = cv.get_proof_term(thy, t).export()
        self.assertEqual(len(prf.items), 5)
        self.assertEqual(thy.check_proof(prf), res_th)

    def testBottomBetaConv(self):
        cv = bottom_conv(beta_conv())
        t = lf(lf(x))
        res = f(f(x,x),f(x,x))
        res_th = eq(t, res)
        self.assertEqual(cv.eval(thy, t), res_th)
        prf = cv.get_proof_term(thy, t).export()
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
        prf = cv.get_proof_term(thy, t).export()
        self.assertEqual(cv.eval(thy, t), eq(t, res))
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
        prf = cv.get_proof_term(thy, t).export()
        self.assertEqual(cv.eval(thy, t), eq(t, res))
        self.assertEqual(len(prf.items), 22)
        self.assertEqual(thy.check_proof(prf), eq(t, res))

    def testTopBetaConvAbs(self):
        cv = top_conv(beta_conv())

        # %x. (%a. f a) x reduces to %x. f x.
        a = Var("a", Ta)
        t = abs(x, abs(a, f(a))(x))
        res = abs(x, f(x))

        prf = cv.get_proof_term(thy, t).export()
        self.assertEqual(cv.eval(thy, t), eq(t, res))
        self.assertEqual(len(prf.items), 2)
        self.assertEqual(thy.check_proof(prf), eq(t, res))

    def testLargeSum(self):
        f = Const("f", TFun(natT, natT))
        g = Const("g", TFun(natT, natT))
        x = Var("x", natT)

        th0, th1 = eq(one,zero), eq(f(x),g(x))
        cv = top_conv(else_conv(rewr_conv(ProofTerm.atom(0, th0)),
                                rewr_conv(ProofTerm.atom(1, th1))))

        f1 = f(one)
        g0 = g(zero)
        t = plus(*([f1] * 50))
        res = plus(*([g0] * 50))
        self.assertEqual(cv.eval(thy, t), eq(t, res))

        prf = Proof()
        prf.add_item(0, "sorry", th=th0)
        prf.add_item(1, "sorry", th=th1)
        cv.get_proof_term(thy, t).export(prf=prf)
        self.assertEqual(thy.check_proof(prf, check_level=1), eq(t, res))

    def testTopSweepConv(self):
        f = Const("f", TFun(natT, natT))
        x = Var("x", natT)

        th0 = eq(x, f(x))
        cv = top_sweep_conv(rewr_conv(ProofTerm.atom(0, th0), match_vars=False))

        prf = Proof()
        prf.add_item(0, "sorry", th=th0)
        cv.get_proof_term(thy, f(x)).export(prf=prf)
        self.assertEqual(thy.check_proof(prf), eq(f(x), f(f(x))))

if __name__ == "__main__":
    unittest.main()
