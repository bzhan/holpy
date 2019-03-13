# Author: Bohua Zhan

import unittest

from kernel.type import TVar, TFun
from kernel.term import Var
from kernel.thm import Thm
from logic import basic
from logic import nat
from logic.function import mk_const_fun, mk_fun_upd, strip_fun_upd, fun_upd_conv
from syntax import printer

Ta = TVar("a")
Tb = TVar("b")
f = Var("f", TFun(Ta, Tb))
a1 = Var("a1", Ta)
a2 = Var("a2", Ta)
b1 = Var("b1", Ta)
b2 = Var("b2", Ta)

thy = basic.loadTheory('function')

natT = nat.natT
zero = nat.zero
one = nat.one
five = nat.to_binary(5)

class FunctionTest(unittest.TestCase):
    def testMkFunUpd(self):
        self.assertEqual(mk_fun_upd(f, a1, b1, a2, b2),
                         mk_fun_upd(mk_fun_upd(f, a1, b1), a2, b2))

    def testStripFunUpd(self):
        self.assertEqual(strip_fun_upd(f), (f, []))
        self.assertEqual(strip_fun_upd(mk_fun_upd(f, a1, b1)), (f, [(a1, b1)]))
        self.assertEqual(strip_fun_upd(mk_fun_upd(f, a1, b1, a2, b2)), (f, [(a1, b1), (a2, b2)]))

    def testEvalFunUpd(self):
        f = mk_fun_upd(mk_const_fun(natT, zero), one, five)
        cv = fun_upd_conv()
        prf = cv.get_proof_term(f(one)).export()
        self.assertEqual(thy.check_proof(prf), Thm.mk_equals(f(one), five))
        prf = cv.get_proof_term(f(zero)).export()
        self.assertEqual(thy.check_proof(prf), Thm.mk_equals(f(zero), zero))


if __name__ == "__main__":
    unittest.main()
