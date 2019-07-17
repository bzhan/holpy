# Author: Bohua Zhan

import unittest

from kernel.type import TVar, TFun, boolT
from kernel import term
from kernel.term import Term, Var, Abs, Bound
from kernel.thm import Thm
from kernel.proof import Proof
from kernel.report import ProofReport
from logic.proofterm import ProofTerm, ProofTermDeriv
from logic import logic
from logic import basic
from logic import matcher
from data import nat

Ta = TVar("a")
a = Var("a", boolT)
b = Var("b", boolT)
c = Var("c", boolT)
d = Var("d", boolT)
x = Var("x", Ta)
y = Var("y", Ta)

thy = basic.load_theory('logic')


class LogicTest(unittest.TestCase):
    def testConj(self):
        test_data = [
            ([], logic.true),
            ([a], a),
            ([a, b], logic.conj(a, b)),
            ([a, b, a], logic.conj(a, logic.conj(b, a)))
        ]

        for ts, res in test_data:
            self.assertEqual(logic.mk_conj(*ts), res)

    def testConjFail(self):
        self.assertRaises(AssertionError, logic.mk_conj, [a])

    def testStripConj(self):
        test_data = [
            (a, [a]),
            (logic.mk_conj(a, b, a), [a, b, a])
        ]

        for t, res in test_data:
            self.assertEqual(logic.strip_conj(t), res)

    def testDisj(self):
        test_data = [
            ([], logic.false),
            ([a], a),
            ([a, b], logic.disj(a, b)),
            ([a, b, a], logic.disj(a, logic.disj(b, a)))
        ]

        for ts, res in test_data:
            self.assertEqual(logic.mk_disj(*ts), res)

    def testDisjFail(self):
        self.assertRaises(AssertionError, logic.mk_disj, [a])

    def testStripDisj(self):
        test_data = [
            (a, [a]),
            (logic.mk_disj(a, b, a), [a, b, a])
        ]

        for t, res in test_data:
            self.assertEqual(logic.strip_disj(t), res)

    def testGetForallName(self):
        test_data = [
            (Term.mk_all(x, Term.mk_all(y, Term.mk_equals(x, y))), ["x", "y"]),
        ]

        for t, res in test_data:
            self.assertEqual(logic.get_forall_names(t, []), res)

    def testNormBoolExpr(self):
        neg, true, false = logic.neg, logic.true, logic.false
        test_data = [
            (true, true),
            (false, false),
            (neg(true), false),
            (neg(false), true),
        ]

        thy = basic.load_theory('logic')
        for t, res in test_data:
            cv = logic.norm_bool_expr()
            prf = cv.get_proof_term(thy, t).export()
            self.assertEqual(thy.check_proof(prf), Thm.mk_equals(t, res))

    def testNormConjAssoc(self):
        conj = logic.mk_conj
        test_data = [
            (a, a),
            (conj(a, b), conj(a, b)),
            (conj(conj(a, b), conj(c, d)), conj(a, b, c, d)),
            (conj(conj(conj(a, b), c), d), conj(a, b, c, d)),
        ]

        thy = basic.load_theory('logic')
        for t, res in test_data:
            cv = logic.norm_conj_assoc()
            prf = cv.get_proof_term(thy, t).export()
            self.assertEqual(thy.check_proof(prf), Thm.mk_equals(t, res))

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

    def testIntro(self):
        macro = logic.intros_macro()

        Ta = TVar('a')
        x = Var('x', Ta)
        P = Var('P', TFun(Ta, boolT))
        C = Var('C', boolT)
        ex_P = logic.mk_exists(x, P(x))
        pt1 = ProofTerm.assume(ex_P)
        pt2 = ProofTerm.variable('x', Ta)
        pt3 = ProofTerm.assume(P(x))
        pt4 = ProofTerm.sorry(Thm([P(x)], C))
        pt4 = ProofTermDeriv('intros', thy, args=[ex_P], prevs=[pt1, pt2, pt3, pt4])
        prf = pt4.export()
        self.assertEqual(thy.check_proof(prf), Thm([ex_P], C))

    def testRewriteGoal(self):
        thy = basic.load_theory('nat')

        n = Var("n", nat.natT)
        eq = Term.mk_equals
        zero = nat.zero
        plus = nat.mk_plus
        prf = Proof()
        prf.add_item(0, "rewrite_goal", args=("nat_plus_def_1", eq(plus(zero,zero),zero)))

        th = Thm([], eq(plus(zero,zero),zero))
        rpt = ProofReport()
        self.assertEqual(thy.check_proof(prf, rpt), th)
        self.assertEqual(rpt.prim_steps, 8)

        rpt2 = ProofReport()
        self.assertEqual(thy.check_proof(prf, rpt2, check_level=1), th)
        self.assertEqual(rpt2.prim_steps, 0)
        self.assertEqual(rpt2.macro_steps, 1)

    def testTrivialMacro(self):
        macro = logic.trivial_macro()
        A = Var("A", boolT)
        B = Var("B", boolT)
        imp = Term.mk_implies
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
        macro = logic.apply_fact_macro()
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
        macro = logic.imp_conj_macro()
        A = Var("A", boolT)
        B = Var("B", boolT)
        C = Var("C", boolT)
        D = Var("D", boolT)
        imp = Term.mk_implies
        conj = logic.mk_conj
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
        macro = logic.imp_conj_macro()
        A = Var("A", boolT)
        B = Var("B", boolT)
        C = Var("C", boolT)
        D = Var("D", boolT)
        imp = Term.mk_implies
        conj = logic.mk_conj
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
