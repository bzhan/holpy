# Author: Bohua Zhan

import unittest

from kernel.type import TFun
from kernel.term import Term, Var
from kernel.thm import Thm
from kernel.report import ProofReport
from logic import nat
from logic import hoare
from logic import logic
from logic.function import mk_const_fun, mk_fun_upd
from logic import basic
from syntax import printer

thy = basic.loadTheory('hoare')

natT = nat.natT
natFunT = TFun(natT, natT)
Sem = hoare.Sem(natFunT)
Skip = hoare.Skip(natFunT)
Assign = hoare.Assign(natT, natT)
Seq = hoare.Seq(natFunT)
Cond = hoare.Cond(natFunT)
While = hoare.While(natFunT)
zero = nat.zero
one = nat.one

eq = Term.mk_equals
abs = Term.mk_abs
s = Var("s", natFunT)
assn_true = abs(s, logic.true)
incr_one = Assign(zero, abs(s, nat.plus(s(zero), one)))

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
        com = Seq(incr_one, incr_one)
        st = mk_const_fun(natT, zero)
        st2 = fun_upd_of_seq(0, 2)
        goal = Sem(com, st, st2)
        prf = hoare.eval_Sem_macro().get_proof_term(thy, goal).export()
        self.assertEqual(thy.check_proof(prf), Thm([], goal))

    def testEvalSem3(self):
        com = Cond(abs(s, eq(s(zero), zero)), incr_one, Skip)
        st = mk_const_fun(natT, zero)
        st2 = fun_upd_of_seq(0, 1)
        goal = Sem(com, st, st2)
        prf = hoare.eval_Sem_macro().get_proof_term(thy, goal).export()
        self.assertEqual(thy.check_proof(prf), Thm([], goal))

        goal = Sem(com, st2, st2)
        prf = hoare.eval_Sem_macro().get_proof_term(thy, goal).export()
        self.assertEqual(thy.check_proof(prf), Thm([], goal))

    def testEvalSem4(self):
        com = Cond(abs(s, logic.neg(eq(s(zero), one))), incr_one, Skip)
        st = mk_const_fun(natT, zero)
        st2 = fun_upd_of_seq(0, 1)
        goal = Sem(com, st, st2)
        prf = hoare.eval_Sem_macro().get_proof_term(thy, goal).export()
        self.assertEqual(thy.check_proof(prf), Thm([], goal))

        goal = Sem(com, st2, st2)
        prf = hoare.eval_Sem_macro().get_proof_term(thy, goal).export()
        self.assertEqual(thy.check_proof(prf), Thm([], goal))

    def testEvalSem5(self):
        com = While(abs(s, logic.neg(eq(s(zero), nat.to_binary(3)))), assn_true, incr_one)
        st = mk_const_fun(natT, zero)
        st2 = fun_upd_of_seq(0, 3)
        goal = Sem(com, st, st2)
        prf = hoare.eval_Sem_macro().get_proof_term(thy, goal).export()
        rpt = ProofReport()
        self.assertEqual(thy.check_proof(prf, rpt), Thm([], goal))


if __name__ == "__main__":
    unittest.main()
