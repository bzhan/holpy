"""Unit test for proof."""

import unittest

from kernel.term import Term, Var
from kernel.thm import Thm
from data import real
from data.real import realT
from data.set import setT
from data.integral import within, atreal
from integral import proof
from logic import auto
from logic.context import Context
from logic.proofterm import refl, ProofTerm
from logic.conv import top_conv, arg_conv
from logic.logic import TacticException
from syntax import parser
from syntax import printer
from logic.tests.logic_test import test_macro
from logic.tests.conv_test import test_conv
from prover import sympywrapper
import integral


class ProofTest(unittest.TestCase):
    def testRealContinuousOn(self):
        test_data = [
            "real_continuous_on (%x. x) (real_closed_interval 0 1)",
            "real_continuous_on (%x. x * x) (real_closed_interval 0 1)",
            "real_continuous_on (%x. -x) (real_closed_interval 0 1)",
            "real_continuous_on (%x. x ^ (2::nat)) (real_closed_interval 0 1)",
            "real_continuous_on (%x. x ^ (3::nat)) (real_closed_interval 0 1)",
            "real_continuous_on (%x. (x + 1) ^ (3::nat)) (real_closed_interval 0 1)",
            "real_continuous_on (%x. exp x) (real_closed_interval 0 1)",
            "real_continuous_on (%x. exp (x ^ (2::nat))) (real_closed_interval 0 1)",
            "real_continuous_on (%x. exp (exp x)) (real_closed_interval 0 1)",
            "real_continuous_on (%x. sin x) (real_closed_interval 0 1)",
            "real_continuous_on (%x. cos x) (real_closed_interval 0 1)",
            "real_continuous_on (%x. sin x * cos x) (real_closed_interval 0 1)",
            "real_continuous_on (%x. sin (cos x)) (real_closed_interval 0 1)",
            "real_continuous_on (%x. 1 / x) (real_closed_interval 1 2)",
            "real_continuous_on (%x. 1 / (x ^ (2::nat))) (real_closed_interval 1 2)",
            "real_continuous_on (%x. 1 / (x ^ (2::nat))) (real_closed_interval (-2) (-1))",
            "real_continuous_on (%x. 1 / (x ^ (2::nat) + 1)) (real_closed_interval (-1) 1)",
            "real_continuous_on (%x. abs x) (real_closed_interval (-1) 1)",
            "real_continuous_on (%x. log x) (real_closed_interval (exp (-1)) (exp 1))",
            "real_continuous_on (%x. log (x ^ (2::nat) + 1)) (real_closed_interval (-1) 1)",
            "real_continuous_on (%x. sqrt x) (real_closed_interval 0 1)",
            "real_continuous_on (%x. sqrt (1 - x ^ (2::nat))) (real_closed_interval 0 1)",
            "real_continuous_on (%x. sqrt (2 - x ^ (2::nat))) (real_closed_interval 0 (sqrt 2))",
            "real_continuous_on (%x. x ^ (-(2::real))) (real_closed_interval 1 2)",
            "real_continuous_on (%x. (3 * x + 1) ^ (-(2::real))) (real_closed_interval 0 1)",
            "real_continuous_on (%x. x ^ (1 / 2)) (real_closed_interval 0 1)",
            "real_continuous_on (%x::real. 2 ^ x) (real_closed_interval 0 1)",
        ]

        for expr in test_data:
            test_macro(self, 'realintegral', 'auto', args=expr, res=expr)

    def testRealContinuousOnFail(self):
        test_data = [
            "real_continuous_on (%x. 1 / x) (real_closed_interval (-1) 1)",
            "real_continuous_on (%x. 1 / x) (real_closed_interval 0 1)",
            "real_continuous_on (%x. log x) (real_closed_interval 0 1)",
            "real_continuous_on (%x. sqrt x) (real_closed_interval (-1) 1)",
            "real_continuous_on (%x. sqrt (1 - x ^ (2::nat))) (real_closed_interval 0 (sqrt 2))",
            "real_continuous_on (%x. sqrt (2 - x ^ (2::nat))) (real_closed_interval 0 2)",
        ]

        for expr in test_data:
            test_macro(self, 'realintegral', 'auto', args=expr, failed=TacticException)

    def testRealIntegrableOn(self):
        test_data = [
            "real_integrable_on (%x. x) (real_closed_interval 0 1)",
            "real_integrable_on (%x. sqrt x) (real_closed_interval 0 1)",
        ]

        for expr in test_data:
            test_macro(self, 'realintegral', 'auto', args=expr, res=expr)

    def testRealDifferentiable(self):
        test_data = [
            "real_differentiable (%x. x) (atreal x)",
            "real_differentiable (%x. x * x) (atreal x)",
            "real_differentiable (%x. -x) (atreal x)",
            "real_differentiable (%x. x ^ (2::nat)) (atreal x)",
            "real_differentiable (%x. x ^ (3::nat)) (atreal x)",
            "real_differentiable (%x. (x + 1) ^ (3::nat)) (atreal x)",
            "real_differentiable (%x. exp x) (atreal x)",
            "real_differentiable (%x. exp (x ^ (2::nat))) (atreal x)",
            "real_differentiable (%x. exp (exp x)) (atreal x)",
            "real_differentiable (%x. sin x) (atreal x)",
            "real_differentiable (%x. cos x) (atreal x)",
            "real_differentiable (%x. sin x * cos x) (atreal x)",
            "real_differentiable (%x. sin (cos x)) (atreal x)",
            "x Mem real_open_interval 0 1 --> real_differentiable (%x. 1 / x) (atreal x)",
            "x Mem real_open_interval 0 1 --> real_differentiable (%x. 1 / (x ^ (2::nat))) (atreal x)",
            "x Mem real_open_interval (-1) 0 --> real_differentiable (%x. 1 / (x ^ (2::nat))) (atreal x)",
            "x Mem real_open_interval (-1) 1 --> real_differentiable (%x. 1 / (x ^ (2::nat) + 1)) (atreal x)",
            "x Mem real_open_interval 0 (exp 1) --> real_differentiable (%x. log x) (atreal x)",
            "x Mem real_open_interval (-1) 1 --> real_differentiable (%x. log (x ^ (2::nat) + 1)) (atreal x)",
            "x Mem real_open_interval 0 1 --> real_differentiable (%x. sqrt x) (atreal x)",
            "x Mem real_open_interval 0 1 --> real_differentiable (%x. sqrt (1 - x ^ (2::nat))) (atreal x)",
            "x Mem real_open_interval 0 (sqrt 2) --> real_differentiable (%x. sqrt (2 - x ^ (2::nat))) (atreal x)",
            "x Mem real_open_interval 0 1 --> real_differentiable (%x. x ^ (-(2::real))) (atreal x)",
            "x Mem real_open_interval 0 1 --> real_differentiable (%x. (3 * x + 1) ^ (-(2::real))) (atreal x)",
            "x Mem real_open_interval 0 1 --> real_differentiable (%x. x ^ (1 / 2)) (atreal x)",
            "x Mem real_open_interval (-1) 1 --> real_differentiable (%x::real. 2 ^ x) (atreal x)",
        ]

        for expr in test_data:
            test_macro(self, 'realintegral', 'auto', vars={'x': 'real'}, args=expr, res=expr)

    def testNormTranscendental(self):
        test_data = [
            ("sin 0", "(0::real)"),
            ("sin (1 / 6 * pi)", "1 / 2"),
            ("cos 0", "(1::real)"),
            ("cos (1 / 6 * pi)", "1 / 2 * 3 ^ (1 / 2)"),
            ("exp 0", "(1::real)"),
            ("cos (pi / 4)", "1 / 2 * 2 ^ (1 / 2)"),
            ("sin (13 / 6 * pi)", "1 / 2"),
            ("sin (7 / 6 * pi)", "-(1 / 2)"),
            ("sin (5 / 6 * pi)", "1 / 2"),
            ("cos (7 / 6 * pi)", "-(1 / 2) * 3 ^ (1 / 2)"),
            ("cos (-pi / 2)", "(0::real)"),
        ]

        for t, res in test_data:
            test_conv(self, 'realintegral', auto.auto_conv(), t=t, t_res=res)

    def testNormAbsoluteValue(self):
        test_data = [
            ("abs x", ["x >= 0"], "x"),
            ("abs x", ["x Mem real_closed_interval 0 1"], "x"),
            ("abs x", ["x Mem real_closed_interval (-1) 0"], "-1 * x"),
            ("abs (sin x)", ["x Mem real_closed_interval 0 (pi / 2)"], "sin x"),
            ("abs (sin x)", ["x Mem real_closed_interval (-pi / 2) 0"], "-1 * sin x"),
            ("abs (log x)", ["x Mem real_open_interval (exp (-1)) 1"], "-1 * log x"),
        ]

        vars = {'x': 'real'}
        ctxt = Context('realintegral', vars=vars)
        for t, conds, res in test_data:
            conds_pt = [ProofTerm.assume(parser.parse_term(ctxt, cond)) for cond in conds]
            cv = auto.auto_conv(conds_pt)
            test_conv(self, 'realintegral', cv, vars=vars, t=t, t_res=res, assms=conds)

    def testNormRealDerivative(self):
        test_data = [
            # Differentiable everywhere
            ("real_derivative (%x. x) x", [], "(1::real)"),
            ("real_derivative (%x. 3) x", [], "(0::real)"),
            ("real_derivative (%x. 3 * x) x", [], "(3::real)"),
            ("real_derivative (%x. x ^ (2::nat)) x", [], "2 * x"),
            ("real_derivative (%x. x ^ (3::nat)) x", [], "3 * x ^ (2::nat)"),
            ("real_derivative (%x. (x + 1) ^ (3::nat)) x", [], "3 + 6 * x + 3 * x ^ (2::nat)"),
            ("real_derivative (%x. exp x) x", [], "exp x"),
            ("real_derivative (%x. exp (x ^ (2::nat))) x", [], "2 * (exp (x ^ (2::nat)) * x)"),
            ("real_derivative (%x. exp (exp x)) x", [], "exp (x + exp x)"),
            ("real_derivative (%x. sin x) x", [], "cos x"),
            ("real_derivative (%x. cos x) x", [], "-1 * sin x"),
            ("real_derivative (%x. sin x * cos x) x", [], "(cos x) ^ (2::nat) + -1 * (sin x) ^ (2::nat)"),

            # Differentiable with conditions
            ("real_derivative (%x. 1 / x) x", ["x Mem real_open_interval 0 1"], "-1 * x ^ -(2::real)"),
            ("real_derivative (%x. 1 / (x ^ (2::nat) + 1)) x", ["x Mem real_open_interval (-1) 1"],
             "-2 * (x * (1 + 2 * x ^ (2::nat) + x ^ (4::nat)) ^ -(1::real))"),
            ("real_derivative (%x. log x) x", ["x Mem real_open_interval 0 1"], "x ^ -(1::real)"),
            ("real_derivative (%x. log (sin x)) x", ["x Mem real_open_interval 0 1"],
             "cos x * (sin x) ^ -(1::real)"),
            ("real_derivative (%x. sqrt x) x", ["x Mem real_open_interval 0 1"], "1 / 2 * x ^ -(1 / 2)"),
            ("real_derivative (%x. sqrt (x ^ (2::nat) + 1)) x", ["x Mem real_open_interval (-1) 1"],
             "x * (1 + x ^ (2::nat)) ^ -(1 / 2)"),

            # Real power
            ("real_derivative (%x. x ^ (1 / 3)) x", ["x Mem real_open_interval 0 1"],
             "1 / 3 * x ^ -(2 / 3)"),
            ("real_derivative (%x. 2 ^ x) x", ["x Mem real_open_interval (-1) 1"], "log 2 * 2 ^ x"),
        ]

        vars = {'x': 'real'}
        ctxt = Context('realintegral', vars=vars)
        for t, conds, res in test_data:
            conds_pt = [ProofTerm.assume(parser.parse_term(ctxt, cond)) for cond in conds]
            cv = auto.auto_conv(conds_pt)
            test_conv(self, 'realintegral', cv, vars=vars, t=t, t_res=res, assms=conds)

    def testIneq(self):
        test_data = [
            ("x Mem real_open_interval 0 (pi / 2) --> sin x > 0"),
            ("x Mem real_open_interval 0 (pi / 2) --> exp(-x) + sin x > 0"),
            ("x Mem real_open_interval 0 (pi / 2) --> ~(exp(-x) + sin x = 0)"),
        ]

        for expr in test_data:
            test_macro(self, 'realintegral', 'auto', vars={'x': 'real'}, args=expr, res=expr)

    def testRealIncreasing(self):
        test_data = [
            "real_derivative (%x. x) x >= 0",
            "real_derivative (%x. 3 * x + 1) x >= 0",
        ]

        for expr in test_data:
            test_macro(self, 'realintegral', 'auto', vars={'x': 'real'}, args=expr, res=expr)

    def testNormRealIntegral(self):
        test_data = [
            # Linearity and common integrals
            ("real_integral (real_closed_interval 0 1) (%x. 1)", "(1::real)"),
            ("real_integral (real_closed_interval 0 1) (%x. 2 * x)", "(1::real)"),
            ("real_integral (real_closed_interval 0 1) (%x. x + 1)", "3 / 2"),
            ("real_integral (real_closed_interval 0 1) (%x. x ^ (2::nat))", "1 / 3"),
            ("real_integral (real_closed_interval 0 1) (%x. exp x)", "-1 + exp 1"),
            ("real_integral (real_closed_interval 0 1) (%x. sin x)", "1 + -1 * cos 1"),
            ("real_integral (real_closed_interval 0 1) (%x. cos x)", "sin 1"),
            ("1/2 * (-2 * real_integral (real_closed_interval 0 (1/2)) (%x. exp x))", "1 + -1 * exp (1 / 2)"),

            # Normalize body
            ("real_integral (real_closed_interval 0 1) (%x. x ^ (2::nat) * x)", "1 / 4"),
            ("real_integral (real_closed_interval 0 1) (%x. x ^ (1 / 3) * (x ^ (1 / 2) + 1))", "57 / 44"),
            ("real_integral (real_closed_interval (exp (-1)) 1) (%x. abs (log x))",
             "-1 * real_integral (real_closed_interval (exp (-1)) 1) (%x. log x)"),
            ("real_integral (real_closed_interval 0 (1 / 2 * pi)) (%x. 2 ^ (1 / 2) * cos x * (2 + -2 * sin x ^ (2::nat)) ^ (1 / 2))",
             "2 ^ (1 / 2) * real_integral (real_closed_interval 0 (1 / 2 * pi)) (%x. cos x * (2 + -2 * sin x ^ (2::nat)) ^ (1 / 2))")
        ]

        for expr, res in test_data:
            test_conv(self, 'realintegral', auto.auto_conv(), t=expr, t_res=res)

    def testIntegrateByParts(self):
        test_data = [
            ("real_integral (real_closed_interval (-1) 2) (%x. x * exp x)",
             "%x::real. x",
             "%x::real. exp x",
             "evalat (%x. x * exp x) (-1) 2 - real_integral (real_closed_interval (-1) 2) (%x. exp x)"),
        ]

        ctxt = Context('realintegral')
        for expr, u, v, res in test_data:
            u = parser.parse_term(ctxt, u)
            v = parser.parse_term(ctxt, v)
            test_conv(self, 'realintegral', proof.integrate_by_parts(u, v), t=expr, t_res=res)

    def testSubstitution(self):
        test_data = [
            ("real_integral (real_closed_interval 0 1) (%x. exp (6 * x))",
             "%x::real. (1/6) * exp x",
             "%x::real. 6 * x",
             "real_integral (real_closed_interval 0 6) (%x. 1 / 6 * exp x)"),
        ]

        ctxt = Context('realintegral')
        for expr, f, g, res in test_data:
            f = parser.parse_term(ctxt, f)
            g = parser.parse_term(ctxt, g)
            test_conv(self, 'realintegral', proof.substitution(f, g), t=expr, t_res=res)

    def testSimplifyRewrConv(self):
        test_data = [
            ("(sin x) ^ (3::nat)", "sin x * (sin x) ^ (2::nat)"),
        ]

        ctxt = Context('realintegral', vars={'x': 'real'})
        for s, t in test_data:
            s = parser.parse_term(ctxt, s)
            t = parser.parse_term(ctxt, t)
            test_conv(self, 'realintegral', proof.simplify_rewr_conv(t), t=s, t_res=t)

    def testLocationConv(self):
        test_data = [
            ("(sin x) ^ (3::nat) + (cos x) ^ (3::nat)", "0", "sin x * (sin x) ^ (2::nat)",
             "(sin x) * (sin x) ^ (2::nat) + (cos x) ^ (3::nat)"),

            ("real_integral (real_closed_interval 0 1) (%x. (sin x) ^ (3::nat))", "0", "sin x * (sin x) ^ (2::nat)",
             "real_integral (real_closed_interval 0 1) (%x. (sin x) * (sin x) ^ (2::nat))"),
        ]

        ctxt = Context('realintegral', vars={'x': 'real'})
        for s, loc, t, res in test_data:
            s = parser.parse_term(ctxt, s)
            t = parser.parse_term(ctxt, t)
            res = parser.parse_term(ctxt, res)
            cv = proof.simplify_rewr_conv(t)
            test_conv(self, 'realintegral', proof.location_conv(loc, cv), t=s, t_res=res)

    def testNormMonomialAllConv(self):
        test_data = [
            ("2 * (2 * x + 3)", "2 * (3 + 2 * x)"),
            ("7 / (2 * (2 * x + 3))", "7/2 * (3 + 2 * x) ^ -(1::real)"),
        ]

        ctxt = Context('realintegral', vars={'x': 'real'})
        for s, res in test_data:
            s = parser.parse_term(ctxt, s)
            res = parser.parse_term(ctxt, res)
            cv = proof.norm_monomial_all_conv()
            test_conv(self, 'realintegral', cv, t=s, t_res=res)

    def testTrigRewrConv(self):
        test_data = [
            ("sin x ^ (2::nat)", "", "TR5", "1 - cos x ^ (2::nat)"),
            ("1 - cos x ^ (2::nat)", "", "TR6", "1 - (1 - sin x ^ (2::nat))"),

            ("real_integral (real_closed_interval 0 pi) (%x. sin x ^ (2::nat) * sin x)", "0.0", "TR5",
             "real_integral (real_closed_interval 0 pi) (%x. (1 - cos x ^ (2::nat)) * sin x)"),
        ]

        ctxt = Context('realintegral', vars={'x': 'real'})
        for s, loc, code, res in test_data:
            s = parser.parse_term(ctxt, s)
            res = parser.parse_term(ctxt, res)
            cv = proof.location_conv(loc, proof.trig_rewr_conv(code, var_name="x"))
            test_conv(self, 'realintegral', cv, t=s, t_res=res)

    def testExprToHolpy(self):
        test_data = [
            ("INT x:[2,3]. 2 * x + x ^ 2", "real_integral (real_closed_interval 2 3) (%x. 2 * x + x ^ (2::nat))"),
        ]

        ctxt = Context('realintegral', vars={'x': 'real'})
        for s, res in test_data:
            s = integral.parser.parse_expr(s)
            res = parser.parse_term(ctxt, res)
            self.assertEqual(proof.expr_to_holpy(s), res)


if __name__ == "__main__":
    unittest.main()
