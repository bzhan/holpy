# Author: Bohua Zhan

import unittest

from kernel.type import TFun
from kernel.term import Var
from kernel.thm import Thm
from logic import basic
from logic import nat
from logic import expr
from logic import function
from syntax import printer

natT = nat.natT
zero = nat.zero
one = nat.one

thy = basic.loadTheory('expr')

class ExprTest(unittest.TestCase):
    def testProveEvalI(self):
        s = function.mk_fun_upd(function.mk_const_fun(natT, zero), one, nat.to_binary(7))

        test_data = [
            (expr.Plus(expr.V(one), expr.N(nat.to_binary(5))), nat.to_binary(12)),
            (expr.Plus(expr.V(zero), expr.N(nat.to_binary(5))), nat.to_binary(5)),
        ]

        for t, n in test_data:
            goal = expr.avalI(s, t, n)
            prf = expr.prove_avalI_macro().get_proof_term(thy, goal).export()
            self.assertEqual(thy.check_proof(prf), Thm([], goal))


if __name__ == "__main__":
    unittest.main()
