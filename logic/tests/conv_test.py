# Author: Bohua Zhan

import unittest

from kernel.term import Term
from kernel.thm import Thm
from logic import basic
from logic.proofterm import ProofTerm
from logic.conv import beta_conv, else_conv, try_conv, abs_conv, top_conv, bottom_conv, \
    top_sweep_conv, arg_conv, rewr_conv, ConvException
from syntax import parser

def test_conv(self, thy_name, cv, *, ctxt=None, t, t_res=None, failed=None, assms=None):
    thy = basic.load_theory(thy_name)
    ctxt = {'vars': dict((nm, parser.parse_type(thy, s))
                         for nm, s in ctxt.items()) if ctxt is not None else {}}
    
    if isinstance(t, str):
        t = parser.parse_term(thy, ctxt, t)
    assert isinstance(t, Term)

    if failed is not None:
        self.assertRaises(failed, cv.eval, thy, t)
        self.assertRaises(failed, cv.get_proof_term, thy, t)
        return

    assms = [parser.parse_term(thy, ctxt, assm)
             for assm in assms] if assms is not None else []

    if isinstance(t_res, str):
        t_res = parser.parse_term(thy, ctxt, t_res)
    assert isinstance(t_res, Term)

    self.assertEqual(cv.eval(thy, t), Thm(assms, Term.mk_equals(t, t_res)))
    pt = cv.get_proof_term(thy, t)
    prf = pt.export()
    self.assertEqual(thy.check_proof(prf), Thm(assms, Term.mk_equals(t, t_res)))

class ConvTest(unittest.TestCase):
    def testBetaConv(self):
        test_conv(
            self, 'logic_base', beta_conv(),
            ctxt={"f": "'a => 'a => 'a", "x": "'a"},
            t="(%x. f x x) x",
            t_res="f x x"
        )

    def testBetaConvFail(self):
        test_conv(
            self, 'logic_base', beta_conv(),
            ctxt={"x": "'a"},
            t="x",
            failed=ConvException
        )

    def testTryConv(self):
        test_conv(
            self, 'logic_base', try_conv(beta_conv()),
            ctxt={"f": "'a => 'a => 'a", "x": "'a"},
            t="(%x. f x x) x",
            t_res="f x x"
        )

    def testTryConv2(self):
        test_conv(
            self, 'logic_base', try_conv(beta_conv()),
            ctxt={"x": "'a"},
            t="x",
            t_res="x"
        )

    def testRewrConv(self):
        test_conv(
            self, 'nat', rewr_conv("nat_plus_def_1"),
            ctxt={"x": "nat"},
            t="0 + x",
            t_res="x"
        )

    def testRewrConv2(self):
        test_conv(
            self, 'nat', rewr_conv("nat_plus_def_2"),
            ctxt={"x": "nat", "y": "nat"},
            t="Suc x + y",
            t_res="Suc (x + y)"
        )

    def testRewrConv3(self):
        test_conv(
            self, 'nat', rewr_conv("min_simp1"),
            ctxt={"x": "nat", "y": "nat"},
            t="min x y",
            t_res="x",
            assms=["x <= y"]
        )

    def testRewrConv4(self):
        thy = basic.load_theory('nat')
        cond = parser.parse_term(thy, {'vars': {}}, "(x::nat) <= y")
        test_conv(
            self, 'nat', rewr_conv("min_simp1", conds=[ProofTerm.sorry(Thm([], cond))]),
            ctxt={"x": "nat", "y": "nat"},
            t="min x y",
            t_res="x"
        )

    def testAbsConv(self):
        test_conv(
            self, 'nat', abs_conv(rewr_conv('nat_plus_def_2')),
            ctxt={"x": "nat"},
            t="%y. Suc x + y",
            t_res="%y. Suc (x + y)"
        )

    def testTopBetaConv(self):
        test_conv(
            self, 'logic_base', top_conv(beta_conv()),
            ctxt={"f": "'a => 'a => 'a", "x": "'a"},
            t="(%x. f x x) ((%x. f x x) x)",
            t_res="f (f x x) (f x x)"
        )

    def testBottomBetaConv(self):
        test_conv(
            self, 'logic_base', bottom_conv(beta_conv()),
            ctxt={"f": "'a => 'a => 'a", "x": "'a"},
            t="(%x. f x x) ((%x. f x x) x)",
            t_res="f (f x x) (f x x)"
        )

    def testTopBetaConvAbs(self):
        test_conv(
            self, 'logic_base', top_conv(beta_conv()),
            ctxt={"f": "'a => 'a => 'a", "x": "'a"},
            t="%x. (%a. f a) x",
            t_res="%x. f x"
        )

    def testTopSweepConv(self):
        test_conv(
            self, 'real', top_sweep_conv(rewr_conv('real_poly_neg1')),
            ctxt={"x": "real"},
            t="-x",
            t_res="-1 * x"
        )

    def testTopSweepConv2(self):
        test_conv(
            self, 'set', top_sweep_conv(rewr_conv('if_P')),
            ctxt={'s': 'nat set'},
            t="(%x. if x Mem s then x else 0)",
            t_res="(%x. if x Mem s then x else 0)"
        )


if __name__ == "__main__":
    unittest.main()
