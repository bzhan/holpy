# Author: Bohua Zhan

import unittest

from kernel.type import boolT, TVar, TFun
from kernel.term import Term, Var
from kernel.thm import Thm
from kernel.proof import ProofItem
from logic.proofterm import ProofTerm, ProofTermAtom
from logic import basic
from logic.logic import conj, disj
from logic.nat import natT, plus, zero
from server import tactic
from syntax import printer

thy = basic.loadTheory('nat')

class TacticTest(unittest.TestCase):
    def testRule(self):
        A = Var('A', boolT)
        B = Var('B', boolT)
        rule_tac = tactic.rule('conjI')
        goal = Thm([], conj(B, A))
        pt = rule_tac.get_proof_term(thy, ProofTerm.sorry(goal))
        prf = pt.export()
        self.assertEqual(thy.check_proof(prf), goal)

    def testRule2(self):
        A = Var('A', boolT)
        B = Var('B', boolT)
        goal = Thm([], disj(B, A))
        prev = ProofTermAtom(0, Thm.assume(disj(A, B)))
        rule_tac = tactic.rule('disjE', prevs=[prev])
        pt = rule_tac.get_proof_term(thy, ProofTerm.sorry(goal))
        prf = pt.export(prefix=(1,), subproof=False)
        self.assertEqual(prf.items[2], ProofItem(3, 'apply_theorem', args='disjE', prevs=[0, 1, 2]))

    def testRule3(self):
        A = Var('A', boolT)
        B = Var('B', boolT)
        goal = Thm([], disj(B, A))
        prev = ProofTermAtom(0, Thm.assume(B))
        rule_tac = tactic.rule('disjI1', prevs=[prev])
        pt = rule_tac.get_proof_term(thy, ProofTerm.sorry(goal))
        prf = pt.export(prefix=(1,), subproof=False)
        self.assertEqual(prf.items[0], ProofItem(1, 'apply_theorem_for', args=('disjI1', {}, {'A': B, 'B': A}), prevs=[0]))

    def testRule4(self):
        n = Var('n', natT)
        goal = Thm([], Term.mk_equals(plus(n, zero), n))
        inst = {'P': Term.mk_abs(n, goal.prop), 'n': n}
        rule_tac = tactic.rule('nat_induct', instsp=({}, inst))
        pt = rule_tac.get_proof_term(thy, ProofTerm.sorry(goal))
        prf = pt.export()
        self.assertEqual(prf.items[2], ProofItem(2, 'apply_theorem_for', args=('nat_induct', {}, inst), prevs=[0, 1]))

    def testIntros(self):
        Ta = TVar('a')
        x = Var('x', Ta)
        P = Var('P', TFun(Ta, boolT))
        Q = Var('Q', TFun(Ta, boolT))
        goal = Thm([], Term.mk_all(x, Term.mk_implies(P(x), Q(x))))
        intros_tac = tactic.intros('x')
        pt = intros_tac.get_proof_term(thy, ProofTerm.sorry(goal))
        prf = pt.export()
        self.assertEqual(thy.check_proof(prf), goal)


if __name__ == "__main__":
    unittest.main()
