# Author: Bohua Zhan

import unittest

from kernel.type import TFun
from kernel.thm import Thm
from logic import nat
from logic import hoare
from logic.function import mk_const_fun, mk_fun_upd
from logic import basic
from syntax import printer

thy = basic.loadTheory('hoare')

natT = nat.natT
natFun = TFun(natT, natT)
Sem = hoare.Sem(natFun)
Assign = hoare.Assign(natT, natT)
Seq = hoare.Seq(natFun)
zero = nat.zero
one = nat.one

def const_val(x):
    return mk_const_fun(natFun, x)

class HoareTest(unittest.TestCase):
    def testEvalSem(self):
        com = Seq(Assign(zero, const_val(one)), Assign(one, const_val(nat.to_binary(2))))
        st = mk_const_fun(natT, zero)
        st2 = mk_fun_upd(mk_const_fun(natT, zero), zero, one, one, nat.to_binary(2))
        goal = Sem(com, st, st2)
        prf = hoare.eval_Sem_macro().get_proof_term(thy, goal).export()
        self.assertEqual(thy.check_proof(prf), Thm([], goal))


if __name__ == "__main__":
    unittest.main()
