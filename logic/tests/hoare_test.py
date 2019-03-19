# Author: Bohua Zhan

import unittest

from kernel.type import TFun
from kernel.term import Term, Var
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

abs = Term.mk_abs
s = Var("s", natFun)

def fun_upd_of_seq(*ns):
    return mk_fun_upd(mk_const_fun(natT, zero), *[nat.to_binary(n) for n in ns])

class HoareTest(unittest.TestCase):
    def testEvalSem(self):
        com = Seq(Assign(zero, abs(s, one)), Assign(one, abs(s, nat.to_binary(2))))
        st = mk_const_fun(natT, zero)
        st2 = fun_upd_of_seq(0, 1, 1, 2)
        goal = Sem(com, st, st2)
        prf = hoare.eval_Sem_macro().get_proof_term(thy, goal).export()
        self.assertEqual(thy.check_proof(prf), Thm([], goal))

    def testEvalSem2(self):
        incr_one = Assign(zero, abs(s, nat.plus(s(zero), one)))
        com = Seq(incr_one, incr_one)
        st = mk_const_fun(natT, zero)
        st2 = fun_upd_of_seq(0, 2)
        goal = Sem(com, st, st2)
        prf = hoare.eval_Sem_macro().get_proof_term(thy, goal).export()
        self.assertEqual(thy.check_proof(prf), Thm([], goal))


if __name__ == "__main__":
    unittest.main()
