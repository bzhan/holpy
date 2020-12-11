# Author: Bohua Zhan

import unittest
import math
from fractions import Fraction

from logic.tests.conv_test import test_conv
from logic.tests.logic_test import test_macro
from logic import context
from logic import auto
from kernel.proofterm import ProofTerm
from data import real
from syntax import parser
from prover import sympywrapper


class RealTest(unittest.TestCase):
    def testRealNormMacro(self):
        test_data = [
            ("x * (y * z) = y * (z * x)"),
            ("-x = -1 * x"),
            ("x - y = x + -1 * y"),
        ]

        vars = {'x': 'real', 'y': 'real', 'z': 'real'}
        for expr in test_data:
            test_macro(self, 'real', 'real_norm', vars=vars, args=expr, res=expr, eval_only=True)

    def testRealNormMacroFailed(self):
        test_data = [
            ("x * y * z = x * y + z"),
            ("1 + x + y = x + y + 2"),
        ]

        vars = {'x': 'real', 'y': 'real', 'z': 'real'}
        for expr in test_data:
            test_macro(self, 'real', 'real_norm', vars=vars, args=expr, failed=AssertionError, eval_only=True)

    def testRealNormConv(self):
        test_data = [
            ("x + 0", "x"),
            ("x * (y + z)", "x * y + x * z"),
            ("of_nat 2 + x", "2 + x"),
            ("of_nat (m + n) + x", "of_nat m + of_nat n + x"),
            ("of_nat (m * n) + x", "x + of_nat m * of_nat n"),
            ("x ^ (1::nat)", "x"),
            ("(x + y) ^ (2::nat)", "x ^ (2::nat) + y ^ (2::nat) + 2 * x * y"),
            ("x ^ ((2::nat) - 1)", "x"),
            ("x ^ (0::nat) + y", "1 + y"),
        ]

        vars = {'x': 'real', 'y': 'real', 'z': 'real', 'm': 'nat', 'n': 'nat'}
        for expr, res in test_data:
            test_conv(self, 'real', real.real_norm_conv(), vars=vars, t=expr, t_res=res)

    def testRealEval(self):
        test_data = [
            ("3 + (2::real) * 5", 13),
            ("(2::real) / 1", 2),
            ("(1::real) / 3", Fraction(1,3)),
            ("(2 + 3) / (3::real)", Fraction(5,3)),
            ("(2::real) ^ (3::nat)", 8),
            ("(2::real) ^ (-(1::real))", Fraction(1,2)),
            ("(0::real) ^ (0::real)", 1),
            ("(0::real) ^ (0::nat)", 1),
            ("(1::real) ^ (1 / 2)", 1),
        ]

        for expr, res in test_data:
            context.set_context('real')
            t = parser.parse_term(expr)
            eval_res = real.real_eval(t)
            self.assertEqual(type(eval_res), type(res))
            self.assertEqual(eval_res, res)

    def testRealEvalConv(self):
        test_data = [
            ("3 + (2::real) * 5", "(13::real)"),
            ("(2 + 3) / (3::real)", "5 / (3::real)"),
        ]

        for expr, res in test_data:
            test_conv(self, 'real', real.real_eval_conv(), t=expr, t_res=res)

    def testCombineAtomConv(self):
        test_data = [
            ("x ^ (2::nat) * x ^ (3::nat)", [], "x ^ (5::nat)"),
            ("x ^ (2::nat) * x ^ (1 / 2)", ["x > 0"], "x ^ (5 / 2)"),
            ("x * x", [], "x ^ (2::nat)"),
            ("x * (x ^ (2::nat))", [], "x ^ (3::nat)"),
            ("x * (x ^ (1 / 2))", ["x > 0"], "x ^ (3 / 2)"),
            ("x ^ (1 / 2) * x ^ (1 / 2)", ["x > 0"], "x"),
            ("x ^ (1 / 2) * x ^ (3 / 2)", ["x > 0"], "x ^ (2::nat)"),
            ("x * x ^ (-(1::real))", ["x > 0"], "(1::real)"),
            ("x ^ (1 / 2) * x ^ -(1 / 2)", ["x > 0"], "(1::real)"),
        ]

        vars = {'x': 'real'}
        context.set_context('realintegral', vars=vars)
        for t, conds, res in test_data:
            conds_pt = [ProofTerm.assume(parser.parse_term(cond)) for cond in conds]
            cv = real.combine_atom(conds_pt)
            test_conv(self, 'realintegral', cv, vars=vars, t=t, t_res=res, assms=conds)

    def testNormMultMonomials(self):
        test_data = [
            ("x * y", [], "x * y"),
            ("(1 / 2 * x) * (1 / 2 * y)", [], "1 / 4 * (x * y)"),
            ("x * (1 / 2 * y)", [], "1 / 2 * (x * y)"),
            ("(1 / 2 * x) * y", [], "1 / 2 * (x * y)"),
            ("(1 / 2 * x) * (2 * y)", [], "x * y"),
            ("(x * y) * (x * y)", [], "x ^ (2::nat) * y ^ (2::nat)"),
            ("(x * y) * (1 / 2 * x ^ (-(1::real)))", ["x > 0"], "1 / 2 * y"),
            ("(x * y) * (x ^ (-(1::real)) * y ^ (-(1::real)))", ["x > 0", "y > 0"], "(1::real)"),
            ("(1 / 2) * x", [], "1 / 2 * x"),
            ("(1 / 2) * (1 / 2 * x)", [], "1 / 4 * x"),
            ("(1 / 2) * (2 * x)", [], "x"),
            ("0 * x", [], "(0::real)"),
        ]

        vars = {'x': 'real', 'y': 'real'}
        context.set_context('realintegral', vars=vars)
        for t, conds, res in test_data:
            conds_pt = [ProofTerm.assume(parser.parse_term(cond)) for cond in conds]
            cv = real.norm_mult_monomials(conds_pt)
            test_conv(self, 'realintegral', cv, vars=vars, t=t, t_res=res, assms=conds)

    def testNormPoly(self):
        test_data = [
            ("x + x", "2 * x"),
            ("x + 2 * x", "3 * x"),
            ("(1 / 2) * x + (1 / 3) * x", "5 / 6 * x"),
            ("x + y + x", "2 * x + y"),
            ("x + (-1) * x", "(0::real)"),
            ("x + (-1) * y + y", "x"),
            ("x + y + (-1) * x", "y"),
            ("(x + y) * (x + y)", "2 * (x * y) + x ^ (2::nat) + y ^ (2::nat)"),
            ("(x + y) * (x - y)", "x ^ (2::nat) + -1 *  y ^ (2::nat)"),
            ("x ^ (3::real)", "x ^ (3::nat)"),
            ("(2::real) ^ (3::nat)", "(8::real)"),
            ("(2::real) ^ (-(1::real))", "1 / 2"),
            ("(9::real) ^ (1 / 2)", "(3::real)"),
            ("(9::real) ^ (1 / 3)", "(3::real) ^ (2 / 3)"),
            ("(3::real) ^ (4 / 3)", "3 * (3::real) ^ (1 / 3)"),
            ("(2::real) ^ -(1 / 2)", "1 / 2 * 2 ^ (1 / 2)"),
            ("(1 / 4) ^ (1 / 2)", "1 / 2"),
            ("((3::real) ^ (1 / 2) * 3 ^ (1 / 2))", "(3::real)"),
            ("(2::real) * (-((1/2) * -(3 ^ (1/2))) + 1)", "2 + (3::real) ^ (1 / 2)"),
        ]

        vars = {'x': 'real', 'y': 'real'}
        for expr, res in test_data:
            test_conv(self, 'transcendentals', auto.auto_conv(), vars=vars, t=expr, t_res=res)

    def testNegInequation(self):
        test_data = [
            ("~(x > y)", "x <= y"),
            ("~(x >= y)", "y > x"),
            ("~(x < y)", "y <= x"),
            ("~(x <= y)", "x > y")
        ]

        vars = {'x' : 'real', 'y' : 'real'}
        for expr, res in test_data:
            test_conv(self, 'transcendentals', real.norm_neg_real_ineq_conv(), vars=vars, t=expr, t_res=res)

    def testNormInequation(self):
        test_data = [
            ("a - b > c", "0 < a + -1 * b + -1 * c"),
            ("a + b < c", "0 < -1 * a + -1 * b + c"),
            ("-b * 5 <= 2 * a + -4 * c", "0 <= 2 * a + 5 * b + -4 * c"),
            ("a - a >= b - c", "0 <= -1 * b + c")
        ]

        for expr, res in test_data:
            vars = {'a' : 'real', 'b' : 'real', 'c' : 'real'}
            test_conv(self, 'transcendentals', real.norm_real_ineq_conv(), vars=vars, t=expr, t_res=res)

    def testNonStrictSimplexMarco(self):
        test_data = [
            (["1 * x + -1 * z < 0"], "1 * x + -1 * z < 0 --> ?t. 1 * x + -1 * z <= 0 - t"),
            (["1 * x + -1 * z < 0", "1 * x + -1 * y > 0"], 
            "1 * x + -1 * z < 0 --> 1 * x + -1 * y > 0 --> (?t. 1 * x + -1 * z <= 0 - t & 1 * x + -1 * y >= 0 + t)")
        ]
        
        vars = {"x": "real", "y": "real", "z": "real"}
        context.set_context("real", vars=vars)

        for ts, res in test_data:
            ts = [parser.parse_term(t) for t in ts]
            res = parser.parse_term(res)
            # test_macro(self, 'real', 'non_strict_simplex', vars=vars, args=ts, res=res)
            self.assertEqual(real.non_strict_simplex_macro().get_proof_term(args=ts).prop, res)

if __name__ == "__main__":
    unittest.main()
