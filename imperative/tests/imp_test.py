# Author: Bohua Zhan

import unittest

from kernel.type import TFun, BoolType, NatType
from kernel.term import Term, Var, Not, Eq, Lambda, true, Nat
from kernel.thm import Thm
from kernel import theory
from kernel.report import ProofReport
from data import nat
from imperative import imp
from logic import logic
from logic import context
from data.function import mk_const_fun, mk_fun_upd
from logic import basic
from syntax import parser

natFunT = TFun(NatType, NatType)
Sem = imp.Sem(natFunT)
Skip = imp.Skip(natFunT)
Assign = imp.Assign(NatType, NatType)
Seq = imp.Seq(natFunT)
Cond = imp.Cond(natFunT)
While = imp.While(natFunT)
Valid = imp.Valid(natFunT)

zero = nat.zero
one = nat.one

s = Var("s", natFunT)
assn_true = Lambda(s, true)
incr_one = Assign(zero, Lambda(s, nat.plus(s(zero), one)))

def fun_upd_of_seq(*ns):
    return mk_fun_upd(mk_const_fun(NatType, zero), *[Nat(n) for n in ns])

class HoareTest(unittest.TestCase):
    def setUp(self):
        basic.load_theory('hoare')

    def testEvalSem(self):
        com = Seq(Assign(zero, Lambda(s, one)), Assign(one, Lambda(s, Nat(2))))
        st = mk_const_fun(NatType, zero)
        st2 = fun_upd_of_seq(0, 1, 1, 2)
        goal = Sem(com, st, st2)
        prf = imp.eval_Sem_macro().get_proof_term(goal, []).export()
        self.assertEqual(theory.thy.check_proof(prf), Thm([], goal))

    def testEvalSem2(self):
        com = Seq(incr_one, incr_one)
        st = mk_const_fun(NatType, zero)
        st2 = fun_upd_of_seq(0, 2)
        goal = Sem(com, st, st2)
        prf = imp.eval_Sem_macro().get_proof_term(goal, []).export()
        self.assertEqual(theory.thy.check_proof(prf), Thm([], goal))

    def testEvalSem3(self):
        com = Cond(Lambda(s, Eq(s(zero), zero)), incr_one, Skip)
        st = mk_const_fun(NatType, zero)
        st2 = fun_upd_of_seq(0, 1)
        goal = Sem(com, st, st2)
        prf = imp.eval_Sem_macro().get_proof_term(goal, []).export()
        self.assertEqual(theory.thy.check_proof(prf), Thm([], goal))

        goal = Sem(com, st2, st2)
        prf = imp.eval_Sem_macro().get_proof_term(goal, []).export()
        self.assertEqual(theory.thy.check_proof(prf), Thm([], goal))

    def testEvalSem4(self):
        com = Cond(Lambda(s, Not(Eq(s(zero), one))), incr_one, Skip)
        st = mk_const_fun(NatType, zero)
        st2 = fun_upd_of_seq(0, 1)
        goal = Sem(com, st, st2)
        prf = imp.eval_Sem_macro().get_proof_term(goal, []).export()
        self.assertEqual(theory.thy.check_proof(prf), Thm([], goal))

        goal = Sem(com, st2, st2)
        prf = imp.eval_Sem_macro().get_proof_term(goal, []).export()
        self.assertEqual(theory.thy.check_proof(prf), Thm([], goal))

    def testEvalSem5(self):
        com = While(Lambda(s, Not(Eq(s(zero), Nat(3)))), assn_true, incr_one)
        st = mk_const_fun(NatType, zero)
        st2 = fun_upd_of_seq(0, 3)
        goal = Sem(com, st, st2)
        prf = imp.eval_Sem_macro().get_proof_term(goal, []).export()
        rpt = ProofReport()
        self.assertEqual(theory.thy.check_proof(prf, rpt), Thm([], goal))

    def testComputeWP(self):
        Q = Var("Q", TFun(natFunT, BoolType))

        test_data = [
            (Assign(zero, Lambda(s, one)),
             Lambda(s, Q(mk_fun_upd(s, zero, one)))),
            (Seq(Assign(zero, Lambda(s, one)), Assign(one, Lambda(s, Nat(2)))),
             Lambda(s, Q(mk_fun_upd(s, zero, one, one, Nat(2))))),
        ]

        for c, P in test_data:
            prf = imp.compute_wp(natFunT, c, Q).export()
            self.assertEqual(theory.thy.check_proof(prf), Thm([], Valid(P, c, Q)))

    def testVCG(self):
        P = Var("P", TFun(natFunT, BoolType))
        Q = Var("Q", TFun(natFunT, BoolType))

        test_data = [
            Assign(zero, Lambda(s, one)),
            Seq(Assign(zero, Lambda(s, one)), Assign(one, Lambda(s, Nat(2)))),
        ]

        for c in test_data:
            goal = Valid(P, c, Q)
            prf = imp.vcg(natFunT, goal).export()
            self.assertEqual(theory.thy.check_proof(prf).concl, goal)

            prf = imp.vcg_tactic().get_proof_term(Thm([], goal), None, []).export()
            self.assertEqual(theory.thy.check_proof(prf).prop, goal)

    def testVCGWhile(self):
        context.set_context(None, vars={"A": 'nat', "B": 'nat'})
        c = parser.parse_term(
            "While (%s. ~s (0::nat) = A) (%s. s 1 = s 0 * B) (Seq (Assign 1 (%s. s 1 + B)) (Assign 0 (%s. s 0 + 1)))")
        P = parser.parse_term("%s. s (0::nat) = (0::nat) & s 1 = 0")
        Q = parser.parse_term("%s. s (1::nat) = A * B")
        goal = Valid(P, c, Q)
        prf = imp.vcg_solve(goal).export()
        self.assertEqual(theory.thy.check_proof(prf), Thm([], goal))

    def testVCGIf(self):
        context.set_context(None, vars={'A': 'nat'})
        c = parser.parse_term("Cond (%s. s (0::nat) = A) Skip (Assign 0 (%s. A))")
        P = parser.parse_term("%s::nat=>nat. true")
        Q = parser.parse_term("%s. s (0::nat) = A")
        goal = Valid(P, c, Q)
        prf = imp.vcg_solve(goal).export()
        self.assertEqual(theory.thy.check_proof(prf), Thm([], goal))


if __name__ == "__main__":
    unittest.main()
