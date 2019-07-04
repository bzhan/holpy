# Author: Bohua Zhan

import unittest

from kernel.type import TVar, TFun
from kernel.term import Var
from kernel.thm import Thm
from logic import basic
from data import nat
from data import function
from data.function import mk_fun_upd, strip_fun_upd
from syntax import printer

Ta = TVar("a")
Tb = TVar("b")
f = Var("f", TFun(Ta, Tb))
a1 = Var("a1", Ta)
a2 = Var("a2", Ta)
b1 = Var("b1", Ta)
b2 = Var("b2", Ta)

thy = basic.load_theory('function')

natT = nat.natT
zero = nat.to_binary_nat(0)
one = nat.to_binary_nat(1)
to_binary = nat.to_binary_nat

def fun_upd_of_seq(*ns):
    return mk_fun_upd(function.mk_const_fun(natT, zero), *[to_binary(n) for n in ns])


class FunctionTest(unittest.TestCase):
    def testMkFunUpd(self):
        self.assertEqual(mk_fun_upd(f, a1, b1, a2, b2),
                         mk_fun_upd(mk_fun_upd(f, a1, b1), a2, b2))

    def testStripFunUpd(self):
        self.assertEqual(strip_fun_upd(f), (f, []))
        self.assertEqual(strip_fun_upd(mk_fun_upd(f, a1, b1)), (f, [(a1, b1)]))
        self.assertEqual(strip_fun_upd(mk_fun_upd(f, a1, b1, a2, b2)), (f, [(a1, b1), (a2, b2)]))

    def testEvalFunUpd(self):
        f = fun_upd_of_seq(1, 5)
        cv = function.fun_upd_eval_conv()
        prf = cv.get_proof_term(thy, f(one)).export()
        self.assertEqual(thy.check_proof(prf), Thm.mk_equals(f(one), to_binary(5)))
        prf = cv.get_proof_term(thy, f(zero)).export()
        self.assertEqual(thy.check_proof(prf), Thm.mk_equals(f(zero), zero))

    def testNormFunUpd(self):
        test_data = [
            ((0, 1), (0, 1)),
            ((1, 0, 0, 5), (0, 5, 1, 0)),
            ((0, 1, 1, 5), (0, 1, 1, 5)),
            ((2, 0, 1, 1), (1, 1, 2, 0)),
            ((2, 0, 1, 1, 0, 2), (0, 2, 1, 1, 2, 0)),
            ((0, 1, 0, 2), (0, 2)),
            ((2, 0, 1, 1, 2, 1, 1, 2), (1, 2, 2, 1)),
        ]

        for n_f, n_res in test_data:
            f = fun_upd_of_seq(*n_f)
            res = fun_upd_of_seq(*n_res)

            cv = function.fun_upd_norm_conv()
            prf = cv.get_proof_term(thy, f).export()
            self.assertEqual(thy.check_proof(prf), Thm.mk_equals(f, res))


if __name__ == "__main__":
    unittest.main()
