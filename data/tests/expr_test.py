# Author: Bohua Zhan

import unittest

from kernel.type import TFun, NatType
from kernel.term import Term, Var, Eq, Nat
from kernel.thm import Thm
from kernel import theory
from logic import basic
from data import nat
from data import expr
from data import function
from data.expr import N, V, Plus, Times


zero = nat.zero
one = nat.one

def fun_upd_of_seq(*ns):
    return function.mk_fun_upd(function.mk_const_fun(NatType, zero), *[Nat(n) for n in ns])

class ExprTest(unittest.TestCase):
    def setUp(self):
        basic.load_theory('expr')

    def testProveAvalI(self):
        s = fun_upd_of_seq(1, 7)

        test_data = [
            (Plus(V(one), N(Nat(5))), Nat(12)),
            (Plus(V(zero), N(Nat(5))), Nat(5)),
            (Times(V(one), N(Nat(5))), Nat(35)),
        ]

        macro = expr.prove_avalI_macro()
        for t, n in test_data:
            goal = expr.avalI(s, t, n)

            # Test get_avalI
            self.assertEqual(Nat(macro.get_avalI(s, t)), n)

            # Test can_eval
            self.assertTrue(macro.can_eval(goal))

            # Test eval
            self.assertEqual(macro.eval(goal, []), Thm([], goal))

            # Test get_proof_term
            prf = macro.get_proof_term(goal, []).export()
            self.assertEqual(theory.thy.check_proof(prf), Thm([], goal))

    def testProveAvalIFail(self):
        s = fun_upd_of_seq(1, 7)
        s2 = Var("s2", TFun(NatType, NatType))
        s3 = function.mk_fun_upd(s2, zero, one)
        macro = expr.prove_avalI_macro()

        # Value does not match
        self.assertFalse(macro.can_eval(expr.avalI(s, V(one), Nat(5))))

        # State cannot be evaluated
        self.assertFalse(macro.can_eval(expr.avalI(s2, V(one), Nat(5))))
        self.assertFalse(macro.can_eval(expr.avalI(s3, V(one), Nat(5))))

        # Goal is not avalI
        self.assertFalse(macro.can_eval(Eq(V(one), N(zero))))


if __name__ == "__main__":
    unittest.main()
