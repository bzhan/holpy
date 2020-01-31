# Author: Bohua Zhan

import unittest

from kernel.type import boolT
from kernel.term import Term, Var
from kernel.thm import Thm
from kernel import theory
from logic.proofterm import ProofTerm
from logic import conv
from logic.conv import beta_conv, else_conv, try_conv, abs_conv, top_conv, bottom_conv, \
    top_sweep_conv, arg_conv, rewr_conv, has_rewrite, ConvException
from syntax import parser, printer
from logic import context


def test_conv(self, thy_name, cv, *, vars=None, t, t_res=None, failed=None, assms=None, limit=None):
    context.set_context(thy_name, vars=vars, limit=limit)

    if isinstance(t, str):
        t = parser.parse_term(t)
    assert isinstance(t, Term)

    if failed is not None:
        self.assertRaises(failed, cv.eval, t)
        self.assertRaises(failed, cv.get_proof_term, t)
        return

    assms = [parser.parse_term(assm) for assm in assms] if assms is not None else []

    if isinstance(t_res, str):
        t_res = parser.parse_term(t_res)
    assert isinstance(t_res, Term)

    res_th = cv.eval(t)
    expected_th = Thm(assms, Term.mk_equals(t, t_res))
    self.assertTrue(res_th.can_prove(expected_th),
        msg="\nExpected: %s\nGot %s" % (printer.print_thm(expected_th), printer.print_thm(res_th)))
    pt = cv.get_proof_term(t)
    prf = pt.export()
    self.assertEqual(theory.thy.check_proof(prf), res_th)

class ConvTest(unittest.TestCase):
    def testBetaConv(self):
        test_conv(
            self, 'logic_base', beta_conv(),
            vars={"f": "'a => 'a => 'a", "x": "'a"},
            t="(%x. f x x) x",
            t_res="f x x"
        )

    def testBetaConvFail(self):
        test_conv(
            self, 'logic_base', beta_conv(),
            vars={"x": "'a"},
            t="x",
            failed=ConvException
        )

    def testTryConv(self):
        test_conv(
            self, 'logic_base', try_conv(beta_conv()),
            vars={"f": "'a => 'a => 'a", "x": "'a"},
            t="(%x. f x x) x",
            t_res="f x x"
        )

    def testTryConv2(self):
        test_conv(
            self, 'logic_base', try_conv(beta_conv()),
            vars={"x": "'a"},
            t="x",
            t_res="x"
        )

    def testRewrConv(self):
        test_conv(
            self, 'nat', rewr_conv("nat_plus_def_1"),
            vars={"x": "nat"},
            t="0 + x",
            t_res="x"
        )

    def testRewrConv2(self):
        test_conv(
            self, 'nat', rewr_conv("nat_plus_def_2"),
            vars={"x": "nat", "y": "nat"},
            t="Suc x + y",
            t_res="Suc (x + y)"
        )

    def testRewrConv3(self):
        test_conv(
            self, 'nat', rewr_conv("min_simp1"),
            vars={"x": "nat", "y": "nat"},
            t="min x y",
            t_res="x",
            failed=ConvException
        )

    def testRewrConv4(self):
        cond = parser.parse_term("(x::nat) <= y")
        test_conv(
            self, 'nat', rewr_conv("min_simp1", conds=[ProofTerm.sorry(Thm([], cond))]),
            vars={"x": "nat", "y": "nat"},
            t="min x y",
            t_res="x"
        )

    def testRewrConv5(self):
        cond = Var('P', boolT)
        test_conv(
            self, 'logic_base', rewr_conv('if_P', conds=[ProofTerm.sorry(Thm([], cond))]),
            vars={'a': "'a", 'b': "'a", 'P': "bool"},
            t="if P then a else b",
            t_res="a"
        )

    def testRewrConv6(self):
        test_conv(
            self, 'set', rewr_conv('image_combine', sym=True),
            vars={'g': "'a => 'b", 'f': "'b => 'c", 's': "'a set"},
            t="image f (image g s)",
            t_res="image (f O g) s"
        )

    def testRewrConv7(self):
        test_conv(
            self, 'logic_base', rewr_conv('eta_conversion'),
            vars={'f': "'a => 'b"},
            t="%x. f x",
            t_res="f"
        )

    def testEtaConv(self):
        test_conv(
            self, 'logic_base', conv.eta_conv(),
            vars={'f': "'a => 'b"},
            t="%x. f x",
            t_res="f"
        )

    def testEtaConv2(self):
        test_conv(
            self, 'nat', conv.eta_conv(),
            vars={'x': 'nat'},
            t="%y. x + y",
            t_res='plus x'
        )

    def testAbsConv(self):
        test_conv(
            self, 'nat', abs_conv(rewr_conv('nat_plus_def_2')),
            vars={"x": "nat"},
            t="%y. Suc x + y",
            t_res="%y. Suc (x + y)"
        )

    def testTopBetaConv(self):
        test_conv(
            self, 'logic_base', top_conv(beta_conv()),
            vars={"f": "'a => 'a => 'a", "x": "'a"},
            t="(%x. f x x) ((%x. f x x) x)",
            t_res="f (f x x) (f x x)"
        )

    def testTopBetaConvAbs(self):
        test_conv(
            self, 'logic_base', top_conv(beta_conv()),
            vars={"f": "'a => 'a => 'a", "x": "'a"},
            t="%x. (%a. f a) x",
            t_res="%x. f x"
        )

    def testBottomBetaConv(self):
        test_conv(
            self, 'logic_base', bottom_conv(beta_conv()),
            vars={"f": "'a => 'a => 'a", "x": "'a"},
            t="(%x. f x x) ((%x. f x x) x)",
            t_res="f (f x x) (f x x)"
        )

    def testBottomBetaConv2(self):
        test_conv(
            self, 'logic_base', bottom_conv(beta_conv()),
            vars={'f': "'a => 'a => 'a", 'x': "'a"},
            t="(%x. %y. f x y) x x",
            t_res="f x x"
        )

    def testTopSweepConv(self):
        test_conv(
            self, 'real', top_sweep_conv(rewr_conv('real_poly_neg1')),
            vars={"x": "real"},
            t="-x",
            t_res="-1 * x"
        )

    def testTopSweepConv2(self):
        test_conv(
            self, 'set', top_sweep_conv(rewr_conv('if_P')),
            vars={'s': 'nat set'},
            t="(%x. if x Mem s then x else 0)",
            t_res="(%x. if x Mem s then x else 0)"
        )

    def testTopSweepConv3(self):
        cond = Var('P', boolT)
        test_conv(
            self, 'logic_base', top_sweep_conv(rewr_conv('if_P', conds=[ProofTerm.sorry(Thm([], cond))])),
            vars={'a': "'a", 'b': "'a", 'P': "bool"},
            t="(if P then a else b) = a",
            t_res="a = a"
        )

    def testTopSweepConv4(self):
        test_conv(
            self, 'set', top_sweep_conv(rewr_conv('image_combine', sym=True)),
            vars={'g': "'a => 'b", 'f': "'b => 'c", 's': "'a set"},
            t="image f (image g s) = t",
            t_res="image (f O g) s = t"
        )

    def testHasRewrite(self):
        test_data = [
            ("(0::nat) + x = x", "nat_plus_def_1", True),
            ("(0::nat) + x = x + 0", "add_0_right", True),
            ("%x. comp_fun g f x = y", "comp_fun_eval", True),
        ]

        context.set_context('function', vars={'x': 'nat', 'y': 'nat', 'f': 'nat => nat', 'g': 'nat => nat'})
        for t, th_name, res in test_data:
            t = parser.parse_term(t)
            self.assertEqual(has_rewrite(th_name, t), res)

    def testHasRewriteSym(self):
        test_data = [
            ("image f (image g s)", "image_combine", True),
            ("image h (image h t) = t", "image_combine", True),
        ]

        context.set_context('set', vars={'g': "'a => 'b", 'f': "'b => 'c", 's': "'a set", 'h': 'nat => nat', 't': 'nat set'})
        for t, th_name, res in test_data:
            t = parser.parse_term(t)
            self.assertEqual(has_rewrite(th_name, t, sym=True), res)


if __name__ == "__main__":
    unittest.main()
