# Author: Bohua Zhan

import unittest

from kernel.type import TFun
from kernel.term import Term, Var
from kernel.thm import Thm
from logic import basic
from data import nat
from data import expr
from data import function
from data.expr import N, V, Plus, Times
from syntax import printer
from server.server import ProofState

thy = basic.load_theory('expr')

natT = nat.natT
zero = nat.zero
one = nat.one
to_binary = nat.to_binary_nat

def fun_upd_of_seq(*ns):
    return function.mk_fun_upd(function.mk_const_fun(natT, zero), *[to_binary(n) for n in ns])

class ExprTest(unittest.TestCase):
    def testProveAvalI(self):
        s = fun_upd_of_seq(1, 7)

        test_data = [
            (Plus(V(one), N(to_binary(5))), to_binary(12)),
            (Plus(V(zero), N(to_binary(5))), to_binary(5)),
            (Times(V(one), N(to_binary(5))), to_binary(35)),
        ]

        macro = expr.prove_avalI_macro()
        for t, n in test_data:
            goal = expr.avalI(s, t, n)

            # Test get_avalI
            self.assertEqual(to_binary(macro.get_avalI(thy, s, t)), n)

            # Test can_eval
            self.assertTrue(macro.can_eval(thy, goal))

            # Test eval
            self.assertEqual(macro.eval(thy, goal, []), Thm([], goal))

            # Test get_proof_term
            prf = macro.get_proof_term(thy, goal, []).export()
            self.assertEqual(thy.check_proof(prf), Thm([], goal))

    def testProveAvalIFail(self):
        s = fun_upd_of_seq(1, 7)
        s2 = Var("s2", TFun(natT, natT))
        s3 = function.mk_fun_upd(s2, zero, one)
        macro = expr.prove_avalI_macro()

        # Value does not match
        self.assertFalse(macro.can_eval(thy, expr.avalI(s, V(one), to_binary(5))))

        # State cannot be evaluated
        self.assertFalse(macro.can_eval(thy, expr.avalI(s2, V(one), to_binary(5))))
        self.assertFalse(macro.can_eval(thy, expr.avalI(s3, V(one), to_binary(5))))

        # Goal is not avalI
        self.assertFalse(macro.can_eval(thy, Term.mk_equals(V(one), N(zero))))


if __name__ == "__main__":
    unittest.main()
