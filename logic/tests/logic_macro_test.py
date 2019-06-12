# Author: Chengwei Zhang

import unittest

from kernel.type import TVar, TFun, boolT
from kernel.term import Term, Var
from kernel.thm import Thm, InvalidDerivationException
from kernel.proof import Proof
from kernel.report import ProofReport
from logic import logic
from logic import logic_macro
from logic import basic
from data import nat
from logic.proofterm import ProofTerm
from syntax import printer

thy = basic.load_theory('logic_base')

imp = Term.mk_implies
conj = logic.mk_conj


class LogicMacroTest(unittest.TestCase):
    def testBetaNorm(self):
        Ta = TVar("a")
        x = Var("x", Ta)
        y = Var("y", Ta)
        f = Var("f", TFun(Ta,Ta))

        t = Term.mk_abs(x, f(x))
        prf = Proof(Term.mk_equals(t(x), y))
        prf.add_item(1, "beta_norm", prevs=[0])
        prf.add_item(2, "implies_intr", args=Term.mk_equals(t(x), y), prevs=[1])

        th = Thm.mk_implies(Term.mk_equals(t(x), y), Term.mk_equals(f(x), y))
        rpt = ProofReport()
        self.assertEqual(thy.check_proof(prf, rpt), th)
        self.assertEqual(rpt.prim_steps, 8)

        rpt2 = ProofReport()
        self.assertEqual(thy.check_proof(prf, rpt2, check_level=1), th)
        self.assertEqual(rpt2.prim_steps, 2)
        self.assertEqual(rpt2.macro_steps, 1)

    def testApplyTheorem(self):
        A = Var("A", boolT)
        B = Var("B", boolT)

        th = Thm([logic.mk_conj(A, B)], A)

        prf = Proof(logic.mk_conj(A, B))
        prf.add_item(1, "apply_theorem", args="conjD1", prevs=[0])
        rpt = ProofReport()
        self.assertEqual(thy.check_proof(prf, rpt), th)
        self.assertEqual(rpt.prim_steps, 3)

        # Reset data for the next check
        prf = Proof(logic.mk_conj(A, B))
        prf.add_item(1, "apply_theorem", args="conjD1", prevs=[0])
        rpt = ProofReport()
        self.assertEqual(thy.check_proof(prf, rpt, check_level=1), th)
        self.assertEqual(rpt.prim_steps, 1)
        self.assertEqual(rpt.macro_steps, 1)

    def testRewriteGoal(self):
        thy = basic.load_theory('nat')

        n = Var("n", nat.natT)
        eq = Term.mk_equals
        zero = nat.zero
        plus = nat.mk_plus
        prf = Proof()
        prf.add_item(0, "rewrite_goal", args=("plus_def_1", eq(plus(zero,zero),zero)))

        th = Thm([], eq(plus(zero,zero),zero))
        rpt = ProofReport()
        self.assertEqual(thy.check_proof(prf, rpt), th)
        self.assertEqual(rpt.prim_steps, 8)

        rpt2 = ProofReport()
        self.assertEqual(thy.check_proof(prf, rpt2, check_level=1), th)
        self.assertEqual(rpt2.prim_steps, 0)
        self.assertEqual(rpt2.macro_steps, 1)

    def testTrivialMacro(self):
        macro = logic_macro.trivial_macro()
        A = Var("A", boolT)
        B = Var("B", boolT)
        test_data = [
            imp(A, A),
            imp(A, B, A),
            imp(A, A, B, A),
        ]

        for t in test_data:
            pt = macro.get_proof_term(thy, t, [])
            prf = pt.export()
            self.assertEqual(thy.check_proof(prf), Thm([], t))

    def testApplyFactMacro(self):
        macro = logic_macro.apply_fact_macro()
        Ta = TVar("a")
        P = Var("P", TFun(Ta, boolT))
        Q = Var("Q", TFun(Ta, boolT))
        s = Var("s", Ta)
        pt = ProofTerm.assume(Term.mk_all(s, Term.mk_implies(P(s), Q(s))))
        pt2 = ProofTerm.assume(P(s))
        pt3 = macro.get_proof_term(thy, None, [pt, pt2])
        prf = pt3.export()
        self.assertEqual(thy.check_proof(prf).prop, Q(s))

    def testImpConjMacro(self):
        macro = logic_macro.imp_conj_macro()
        A = Var("A", boolT)
        B = Var("B", boolT)
        C = Var("C", boolT)
        D = Var("D", boolT)
        test_data = [
            (imp(conj(conj(A, conj(D, B), C)), conj(conj(A, D, C), conj(A, B))), True),
            (imp(conj(C, D), A), False),
            (imp(conj(A, B), conj(A, conj(B, C))), False),
            (imp(conj(A, conj(B, C)), conj(A, B)), True),
        ]

        for t, res in test_data:
            if res:
                pt = macro.get_proof_term(thy, t, [])
                self.assertEqual(pt, Thm([], t))
                prf = pt.export()
                thy.check_proof(prf)
            else:
                self.assertRaises(AssertionError, macro.get_proof_term, thy, t, [])

    def testImpConjMacroEval(self):
        macro = logic_macro.imp_conj_macro()
        A = Var("A", boolT)
        B = Var("B", boolT)
        C = Var("C", boolT)
        D = Var("D", boolT)
        test_data = [
            (imp(conj(conj(A, conj(D, B))), conj(conj(A, D), conj(B, A))), True),
            (imp(B, C), False),
            (imp(conj(A, B), conj(A, conj(B, C))), False),
            (imp(conj(A, conj(B, C)), conj(A, B)), True),
        ]

        for t, res in test_data:
            if res:
                self.assertEqual(macro.eval(thy, t, []), Thm([], t))
            else:
                self.assertRaises(AssertionError, macro.eval, thy, t, [])


if __name__ == "__main__":
    unittest.main()
