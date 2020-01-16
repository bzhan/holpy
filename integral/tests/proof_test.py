"""Unit test for proof."""

import unittest

from kernel.term import Term, Var
from kernel.thm import Thm
from data import real
from data.real import realT
from data.set import setT
from data.integral import within, atreal
from integral import proof
from logic.auto import auto_conv
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

    def testRealDifferentiableOn(self):
        test_data = [
            "real_differentiable_on (%x. x) (real_closed_interval 0 1)",
            "real_differentiable_on (%x. x * x) (real_closed_interval 0 1)",
            "real_differentiable_on (%x. -x) (real_closed_interval 0 1)",
            "real_differentiable_on (%x. x ^ (2::nat)) (real_closed_interval 0 1)",
            "real_differentiable_on (%x. x ^ (3::nat)) (real_closed_interval 0 1)",
            "real_differentiable_on (%x. (x + 1) ^ (3::nat)) (real_closed_interval 0 1)",
            "real_differentiable_on (%x. exp x) (real_closed_interval 0 1)",
            "real_differentiable_on (%x. exp (x ^ (2::nat))) (real_closed_interval 0 1)",
            "real_differentiable_on (%x. exp (exp x)) (real_closed_interval 0 1)",
            "real_differentiable_on (%x. sin x) (real_closed_interval 0 1)",
            "real_differentiable_on (%x. cos x) (real_closed_interval 0 1)",
            "real_differentiable_on (%x. sin x * cos x) (real_closed_interval 0 1)",
            "real_differentiable_on (%x. sin (cos x)) (real_closed_interval 0 1)",
            "real_differentiable_on (%x. 1 / x) (real_closed_interval 1 2)",
            "real_differentiable_on (%x. 1 / (x ^ (2::nat))) (real_closed_interval 1 2)",
            "real_differentiable_on (%x. 1 / (x ^ (2::nat))) (real_closed_interval (-2) (-1))",
            "real_differentiable_on (%x. 1 / (x ^ (2::nat) + 1)) (real_closed_interval (-1) 1)",
            "real_differentiable_on (%x. log x) (real_closed_interval (exp (-1)) (exp 1))",
            "real_differentiable_on (%x. log (x ^ (2::nat) + 1)) (real_closed_interval (-1) 1)",
            "real_differentiable_on (%x. sqrt x) (real_closed_interval 1 2)",
            "real_differentiable_on (%x. sqrt (1 - x ^ (2::nat))) (real_closed_interval 0 (sqrt 2 / 2))",
            "real_differentiable_on (%x. sqrt (2 - x ^ (2::nat))) (real_closed_interval 0 1)",
            "real_differentiable_on (%x. x ^ (-(2::real))) (real_closed_interval 1 2)",
            "real_differentiable_on (%x. (3 * x + 1) ^ (-(2::real))) (real_closed_interval 0 1)",
            "real_differentiable_on (%x. x ^ (1 / 2)) (real_closed_interval 1 2)",
            "real_differentiable_on (%x::real. 2 ^ x) (real_closed_interval 0 1)",
        ]

        for expr in test_data:
            test_macro(self, 'realintegral', 'auto', args=expr, res=expr)

    def testRealDifferentiableOnFail(self):
        test_data = [
            "real_differentiable_on (%x. 1 / x) (real_closed_interval (-1) 1)",
            "real_differentiable_on (%x. 1 / x) (real_closed_interval 0 1)",
            "real_differentiable_on (%x. log x) (real_closed_interval 0 1)",
            "real_differentiable_on (%x. sqrt x) (real_closed_interval 0 1)",
            "real_differentiable_on (%x. sqrt (1 - x ^ (2::nat))) (real_closed_interval 0 1)",
            "real_differentiable_on (%x. sqrt (2 - x ^ (2::nat))) (real_closed_interval 0 (sqrt 2))",
        ]

        for expr in test_data:
            test_macro(self, 'realintegral', 'auto', args=expr, failed=TacticException)

    def testNormTranscendental(self):
        test_data = [
            ("sin 0", [], "(0::real)"),
            ("sin (1 / 6 * pi)", [], "1 / 2"),
            ("cos 0", [], "(1::real)"),
            ("cos (1 / 6 * pi)", [], "sqrt 3 / 2"),
            ("exp 0", [], "(1::real)"),
        ]

        ctxt = Context('realintegral')
        for t, conds, res in test_data:
            conds_pt = [ProofTerm.assume(parser.parse_term(ctxt, cond)) for cond in conds]
            cv = auto_conv(conds_pt)
            test_conv(self, 'realintegral', cv, t=t, t_res=res, assms=conds)

    def testNormAbsoluteValue(self):
        test_data = [
            ("abs x", ["x >= 0"], "x"),
            ("abs x", ["x Mem real_closed_interval 0 1"], "x"),
            ("abs x", ["x Mem real_closed_interval (-1) 0"], "-x"),
            ("abs (sin x)", ["x Mem real_closed_interval 0 (pi / 2)"], "sin x"),
            ("abs (sin x)", ["x Mem real_closed_interval (-pi / 2) 0"], "-sin x"),
        ]

        vars = {'x': 'real'}
        ctxt = Context('realintegral', vars=vars)
        for t, conds, res in test_data:
            conds_pt = [ProofTerm.assume(parser.parse_term(ctxt, cond)) for cond in conds]
            cv = auto_conv(conds_pt)
            test_conv(self, 'realintegral', cv, vars=vars, t=t, t_res=res, assms=conds)

    def testRealIneqOnInterval(self):
        test_data = [
            # Nonnegative
            ("x Mem real_closed_interval 0 pi", "sin x >= 0", True),
            ("x Mem real_closed_interval 0 (2 * pi)", "sin x >= 0", False),
            ("x Mem real_closed_interval (-pi / 2) (pi / 2)", "cos x >= 0", True),
            ("x Mem real_closed_interval 0 pi", "cos x >= 0", False),

            # Nonpositive
            ("x Mem real_closed_interval (-pi) 0", "sin x <= 0", True),
            ("x Mem real_closed_interval (-pi) pi", "sin x <= 0", False),

            # Nonzero
            ("x Mem real_closed_interval (pi / 4) (3 * pi / 4)", "~sin x = 0", True),
            ("x Mem real_closed_interval 0 pi", "~sin x = 0", False),
        ]

        ctxt = Context('realintegral', vars={'x': 'real'})
        thy = ctxt.thy
        for assm, goal, success in test_data:
            if success:
                test_macro(self, 'realintegral', 'real_ineq_on_interval', vars={'x': 'real'},
                           assms=[assm], res=goal, args=goal, eval_only=True)
            else:
                test_macro(self, 'realintegral', 'real_ineq_on_interval', vars={'x': 'real'},
                           assms=[assm], failed=AssertionError, args=goal, eval_only=True)

    def testRealIncreasingOn(self):
        test_data = [
            ("6 * x", "a", "b"),
            ("sin x", "(0::real)", "pi / 2"),
        ]

        ctxt = Context('realintegral', vars={'x': 'real', 'y': 'real', 'a': 'real', 'b': 'real'})
        thy = ctxt.thy
        x = Var('x', realT)
        for s, a, b in test_data:
            s = parser.parse_term(ctxt, s)
            f = Term.mk_abs(x, s)
            a = parser.parse_term(ctxt, a)
            b = parser.parse_term(ctxt, b)
            pt = proof.real_increasing_onI(thy, f, a, b)
            th = thy.check_proof(pt.export())
            self.assertEqual(th.prop, proof.mk_real_increasing_on(f, a, b))

    def testRealDecreasingOn(self):
        test_data = [
            ("- 6 * x", "a", "b"),
            ("cos x", "(0::real)", "pi / 2"),
        ]

        ctxt = Context('realintegral', vars={'x': 'real', 'y': 'real', 'a': 'real', 'b': 'real'})
        thy = ctxt.thy
        x = Var('x', realT)
        for s, a, b in test_data:
            s = parser.parse_term(ctxt, s)
            f = Term.mk_abs(x, s)
            a = parser.parse_term(ctxt, a)
            b = parser.parse_term(ctxt, b)
            pt = proof.real_decreasing_onI(thy, f, a, b)
            th = thy.check_proof(pt.export())
            self.assertEqual(th.prop, proof.mk_real_decreasing_on(f, a, b))

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

        vars = {'c': 'real'}
        for expr, res in test_data:
            test_conv(self, 'realintegral', proof.common_integral(), vars=vars, t=expr, t_res=res)

    def testSimplify(self):
        test_data = [
            ("evalat (%x. c * x) 1 2", "c"),
            ("evalat (%x. x ^ (2::nat) / 2) 1 2", "(3::real) / 2"),
            ("evalat (%x. x ^ ((2::nat) + 1) / (of_nat 2 + 1)) 1 2", "(7::real) / 3"),
            ("evalat (%x. exp x) 1 2", "-1 * exp 1 + exp 2"),
            ("evalat (%x. -cos x) 1 2", "cos 1 + -1 * cos 2"),
            ("evalat (%x. sin x) 1 2", "-1 * sin 1 + sin 2"),
        ]

        vars = {'c': 'real'}
        for expr, res in test_data:
            test_conv(self, 'realintegral', proof.simplify(), vars=vars, t=expr, t_res=res)

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

    def testTrigRewrConv(self):
        test_data = [
            ("sin x ^ (2::nat)", "", "TR5",
             "1 - cos x ^ (2::nat)"),

            ("real_integral (real_closed_interval 0 pi) (%x. sin x ^ (2::nat) * sin x)", "0.0", "TR5",
             "real_integral (real_closed_interval 0 pi) (%x. (1 - cos x ^ (2::nat)) * sin x)"),
        ]

        ctxt = Context('realintegral', vars={'x': 'real'})
        for s, loc, code, res in test_data:
            s = parser.parse_term(ctxt, s)
            res = parser.parse_term(ctxt, res)
            cv = proof.location_conv(loc, proof.trig_rewr_conv(code))
            test_conv(self, 'realintegral', cv, t=s, t_res=res)

    def testRealAbsConv(self):
        test_data = [
            ("abs (cos x)", "x Mem real_closed_interval 0 (pi / 2)", "cos x"),
            ("abs (cos x)", "x Mem real_closed_interval (pi / 2) pi", "-cos x"),
            ("abs (sin x)", "x Mem real_closed_interval 0 (pi / 2)", "sin x"),
            ("abs (sin x)", "x Mem real_closed_interval (- pi / 2) 0", "-sin x"),
        ]

        ctxt = Context('realintegral', vars={'x': 'real'})
        for s, cond, res in test_data:
            s = parser.parse_term(ctxt, s)
            cond_t = parser.parse_term(ctxt, cond)
            res = parser.parse_term(ctxt, res)
            cv = proof.real_abs_conv(ProofTerm.assume(cond_t))
            test_conv(self, 'realintegral', cv, t=s, t_res=res, assms=[cond])

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
