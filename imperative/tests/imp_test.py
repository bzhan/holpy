# Author: Bohua Zhan

import unittest

from kernel.type import TFun, boolT
from kernel.term import Term, Var
from kernel.thm import Thm
from kernel.report import ProofReport
from data import nat
from imperative import imp
from logic import logic
from data.function import mk_const_fun, mk_fun_upd
from logic import basic
from syntax import parser
from syntax import printer

thy = basic.load_theory('hoare')

natT = nat.natT
natFunT = TFun(natT, natT)
Sem = imp.Sem(natFunT)
Skip = imp.Skip(natFunT)
Assign = imp.Assign(natT, natT)
Seq = imp.Seq(natFunT)
Cond = imp.Cond(natFunT)
While = imp.While(natFunT)
Valid = imp.Valid(natFunT)
zero = nat.zero
one = nat.one
to_binary = nat.to_binary_nat

eq = Term.mk_equals
abs = Term.mk_abs
s = Var("s", natFunT)
assn_true = abs(s, logic.true)
incr_one = Assign(zero, abs(s, nat.plus(s(zero), one)))

def fun_upd_of_seq(*ns):
    return mk_fun_upd(mk_const_fun(natT, zero), *[to_binary(n) for n in ns])

class HoareTest(unittest.TestCase):
    def testEvalSem(self):
        com = Seq(Assign(zero, abs(s, one)), Assign(one, abs(s, to_binary(2))))
        st = mk_const_fun(natT, zero)
        st2 = fun_upd_of_seq(0, 1, 1, 2)
        goal = Sem(com, st, st2)
        prf = imp.eval_Sem_macro().get_proof_term(thy, goal, []).export()
        self.assertEqual(thy.check_proof(prf), Thm([], goal))

    def testEvalSem2(self):
        com = Seq(incr_one, incr_one)
        st = mk_const_fun(natT, zero)
        st2 = fun_upd_of_seq(0, 2)
        goal = Sem(com, st, st2)
        prf = imp.eval_Sem_macro().get_proof_term(thy, goal, []).export()
        self.assertEqual(thy.check_proof(prf), Thm([], goal))

    def testEvalSem3(self):
        com = Cond(abs(s, eq(s(zero), zero)), incr_one, Skip)
        st = mk_const_fun(natT, zero)
        st2 = fun_upd_of_seq(0, 1)
        goal = Sem(com, st, st2)
        prf = imp.eval_Sem_macro().get_proof_term(thy, goal, []).export()
        self.assertEqual(thy.check_proof(prf), Thm([], goal))

        goal = Sem(com, st2, st2)
        prf = imp.eval_Sem_macro().get_proof_term(thy, goal, []).export()
        self.assertEqual(thy.check_proof(prf), Thm([], goal))

    def testEvalSem4(self):
        com = Cond(abs(s, logic.neg(eq(s(zero), one))), incr_one, Skip)
        st = mk_const_fun(natT, zero)
        st2 = fun_upd_of_seq(0, 1)
        goal = Sem(com, st, st2)
        prf = imp.eval_Sem_macro().get_proof_term(thy, goal, []).export()
        self.assertEqual(thy.check_proof(prf), Thm([], goal))

        goal = Sem(com, st2, st2)
        prf = imp.eval_Sem_macro().get_proof_term(thy, goal, []).export()
        self.assertEqual(thy.check_proof(prf), Thm([], goal))

    def testEvalSem5(self):
        com = While(abs(s, logic.neg(eq(s(zero), to_binary(3)))), assn_true, incr_one)
        st = mk_const_fun(natT, zero)
        st2 = fun_upd_of_seq(0, 3)
        goal = Sem(com, st, st2)
        prf = imp.eval_Sem_macro().get_proof_term(thy, goal, []).export()
        rpt = ProofReport()
        self.assertEqual(thy.check_proof(prf, rpt), Thm([], goal))

    def testComputeWP(self):
        Q = Var("Q", TFun(natFunT, boolT))

        test_data = [
            (Assign(zero, abs(s, one)),
             abs(s, Q(mk_fun_upd(s, zero, one)))),
            (Seq(Assign(zero, abs(s, one)), Assign(one, abs(s, to_binary(2)))),
             abs(s, Q(mk_fun_upd(s, zero, one, one, to_binary(2))))),
        ]

        for c, P in test_data:
            prf = imp.compute_wp(thy, natFunT, c, Q).export()
            self.assertEqual(thy.check_proof(prf), Thm([], Valid(P, c, Q)))

    def testVCG(self):
        P = Var("P", TFun(natFunT, boolT))
        Q = Var("Q", TFun(natFunT, boolT))

        test_data = [
            Assign(zero, abs(s, one)),
            Seq(Assign(zero, abs(s, one)), Assign(one, abs(s, to_binary(2)))),
        ]

        for c in test_data:
            goal = Valid(P, c, Q)
            prf = imp.vcg(thy, natFunT, goal).export()
            self.assertEqual(thy.check_proof(prf).concl, goal)

            prf = imp.vcg_tactic().get_proof_term(thy, Thm([], goal), None, []).export()
            self.assertEqual(thy.check_proof(prf).prop, goal)

    def testVCGWhile(self):
        A = Var("A", natT)
        B = Var("B", natT)
        ctxt = {'vars': {"A": natT, "B": natT}}
        c = parser.parse_term(thy, ctxt, \
            "While (%s. ~s (0::nat) = A) (%s. s 1 = s 0 * B) (Seq (Assign 1 (%s. s 1 + B)) (Assign 0 (%s. s 0 + 1)))")
        P = parser.parse_term(thy, ctxt, "%s. s (0::nat) = (0::nat) & s 1 = 0")
        Q = parser.parse_term(thy, ctxt, "%s. s (1::nat) = A * B")
        goal = Valid(P, c, Q)
        prf = imp.vcg_solve(thy, goal).export()
        self.assertEqual(thy.check_proof(prf), Thm([], goal))

    def testVCGIf(self):
        ctxt = {'vars': {"A": natT}}
        c = parser.parse_term(thy, ctxt, \
            "Cond (%s. s (0::nat) = A) Skip (Assign 0 (%s. A))")
        P = parser.parse_term(thy, ctxt, "%s::nat=>nat. true")
        Q = parser.parse_term(thy, ctxt, "%s. s (0::nat) = A")
        goal = Valid(P, c, Q)
        prf = imp.vcg_solve(thy, goal).export()
        self.assertEqual(thy.check_proof(prf), Thm([], goal))


if __name__ == "__main__":
    unittest.main()
