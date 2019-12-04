"""Unit test for proof."""

import unittest

from kernel.term import Term, Var
from data.real import realT
from data.set import setT
from data.integral import within, atreal
from integral import proof
from logic.context import Context
from syntax import parser
from syntax import printer
from logic.tests.conv_test import test_conv


class ProofTest(unittest.TestCase):
    def testHasRealDerivativeI(self):
        test_data = [
            ("y", "(0::real)"),
            ("x", "(1::real)"),
            ("x * y", "a * 0 + 1 * y"),
            ("x * x", "a * 1 + 1 * a"),
            ("x ^ (2::nat)", "of_nat 2 * a ^ ((2::nat) - 1) * 1"),
            ("x ^ (3::nat)", "of_nat 3 * a ^ ((3::nat) - 1) * 1"),
            ("(x + 1) ^ (3::nat)", "of_nat 3 * (a + 1) ^ ((3::nat) - 1) * (1 + 0)"),
            ("exp(x)", "exp(a) * 1"),
            ("exp(x ^ (2::nat))", "exp (a ^ (2::nat)) * (of_nat 2 * a ^ ((2::nat) - 1) * 1)"),
            ("exp(exp(x))", "exp (exp a) * (exp a * 1)"),
            ("sin(x)", "cos a * 1"),
            ("cos(x)", "-sin a * 1"),
            ("sin(x) * cos(x)", "sin a * (-(sin a) * 1) + cos a * 1 * cos a"),
        ]

        ctxt = Context('realintegral', vars={'x': 'real', 'y': 'real', 'a': 'real', 'b': 'real'})
        thy = ctxt.thy
        x = Var('x', realT)
        a = Var('a', realT)
        S = Var('S', setT(realT))
        for s, deriv_s in test_data:
            s = parser.parse_term(ctxt, s)
            deriv_s = parser.parse_term(ctxt, deriv_s)
            f = Term.mk_abs(x, s)
            pt = proof.has_real_derivativeI(thy, f, a, S)
            th = thy.check_proof(pt.export())
            self.assertEqual(th.prop, proof.mk_has_real_derivative(f, deriv_s, a, S))

    def testHasRealDerivative(self):
        test_data = [
            ("y", "(0::real)"),
            ("x", "(1::real)"),
            ("x * y", "y"),
            ("x * x", "2 * a"),
            ("x ^ (2::nat)", "2 * a"),
            ("x ^ (3::nat)", "3 * a ^ (2::nat)"),
            ("(x + 1) ^ (3::nat)", "3 * (a + 1) ^ (2::nat)"),
            ("exp(x)", "exp(a)"),
            ("exp(x ^ (2::nat))", "2 * a * exp (a ^ (2::nat))"),
            ("exp(exp(x))", "exp (exp a) * exp a"),
            ("sin(x)", "cos a"),
            ("cos(x)", "-sin a"),
            ("sin(x) * cos(x)", "- ((sin a) ^ (2::nat)) + (cos a) ^ (2::nat)"),
        ]

        ctxt = Context('realintegral', vars={'x': 'real', 'y': 'real', 'a': 'real', 'b': 'real'})
        thy = ctxt.thy
        x = Var('x', realT)
        a = Var('a', realT)
        S = Var('S', setT(realT))
        for s, deriv_s in test_data:
            s = parser.parse_term(ctxt, s)
            deriv_s = parser.parse_term(ctxt, deriv_s)
            f = Term.mk_abs(x, s)
            goal = proof.mk_has_real_derivative(f, deriv_s, a, S)    
            pt = proof.has_real_derivative(thy, goal)
            th = thy.check_proof(pt.export())
            self.assertEqual(th.prop, goal)

    def testRealContinuousOn(self):
        test_data = [
            "y",
            "x",
            "x * y",
            "x * x",
            "x ^ (2::nat)",
            "x ^ (3::nat)",
            "(x + 1) ^ (3::nat)",
            "exp(x)",
            "exp(x ^ (2::nat))",
            "exp(exp(x))",
            "sin(x)",
            "cos(x)",
            "sin(x) * cos(x)",
        ]

        ctxt = Context('realintegral', vars={'x': 'real', 'y': 'real'})
        thy = ctxt.thy
        x = Var('x', realT)
        a = Var('a', realT)
        b = Var('b', realT)
        for s in test_data:
            s = parser.parse_term(ctxt, s)
            f = Term.mk_abs(x, s)
            pt = proof.real_continuous_onI(thy, f, a, b)
            th = thy.check_proof(pt.export())
            self.assertEqual(th.prop, proof.mk_real_continuous_on(f, a, b))
            pt2 = proof.real_integrable_onI(thy, f, a, b)
            th2 = thy.check_proof(pt2.export())
            self.assertEqual(pt2.prop, proof.mk_real_integrable_on(f, a, b))

    def testLinearityConv(self):
        test_data = [
            ("real_integral (real_closed_interval a b) (%x. 2 * x)",
             "2 * real_integral (real_closed_interval a b) (%x. x)"),

            ("real_integral (real_closed_interval a b) (%x. x + y)",
             "real_integral (real_closed_interval a b) (%x. x) + real_integral (real_closed_interval a b) (%x. y)"),

            ("real_integral (real_closed_interval a b) (%x. -x - y)",
             "-real_integral (real_closed_interval a b) (%x. x) - real_integral (real_closed_interval a b) (%x. y)"),
        ]

        vars = {'x': 'real', 'y': 'real', 'a': 'real', 'b': 'real'}
        for expr, res in test_data:
            test_conv(self, 'realintegral', proof.linearity(), vars=vars, t=expr, t_res=res)

    def testCommonIntegralConv(self):
        test_data = [
            ("real_integral (real_closed_interval 1 2) (%x. c)",
             "evalat (%x. c * x) 1 2"),

            ("real_integral (real_closed_interval 1 2) (%x. x)",
             "evalat (%x. x ^ (2::nat) / 2) 1 2"),

            ("real_integral (real_closed_interval 1 2) (%x. x ^ (2::nat))",
             "evalat (%x. x ^ ((2::nat) + 1) / (of_nat 2 + 1)) 1 2"),

            ("real_integral (real_closed_interval 1 2) (%x. exp x)",
             "evalat (%x. exp x) 1 2"),

            ("real_integral (real_closed_interval 1 2) (%x. sin x)",
             "evalat (%x. -cos x) 1 2"),

            ("real_integral (real_closed_interval 1 2) (%x. cos x)",
             "evalat (%x. sin x) 1 2"),
        ]

        vars = {'a': 'real', 'b': 'real', 'c': 'real'}
        for expr, res in test_data:
            test_conv(self, 'realintegral', proof.common_integral(), vars=vars, t=expr, t_res=res)


if __name__ == "__main__":
    unittest.main()
