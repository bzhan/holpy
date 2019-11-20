"""Unit test for proof."""

import unittest

from kernel.term import Term, Var
from data.real import realT
from data.set import setT
from data.integral import within, atreal
from integral import proof
from logic.basic import Context
from syntax import parser
from syntax import printer



class ProofTest(unittest.TestCase):
    def testHasRealDerivativeI(self):
        test_data = [
            ("y", "(0::real)"),
            ("x", "(1::real)"),
            ("x * y", "a * 0 + 1 * y"),
            ("x * x", "a * 1 + 1 * a"),
        ]

        ctxt = Context('realintegral', vars={'x': 'real', 'y': 'real', 'a': 'real', 'b': 'real', 'n': 'nat'})
        thy = ctxt.thy
        x = Var('x', realT)
        a = Var('a', realT)
        S = Var('S', setT(realT))
        for s, deriv_s in test_data:
            s = parser.parse_term(ctxt, s)
            deriv_s = parser.parse_term(ctxt, deriv_s)
            f = Term.mk_abs(x, s)
            pt = proof.has_real_derivativeI(thy, f, a, S)
            th = (thy.check_proof(pt.export()))
            self.assertEqual(th.prop.args, [f, deriv_s, within(atreal(a), S)])


if __name__ == "__main__":
    unittest.main()
