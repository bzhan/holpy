# Author: Bohua Zhan

import unittest

from kernel.type import boolT, TVar, TFun
from kernel.term import Term, Var
from kernel.thm import Thm
from logic.proofterm import ProofTerm
from logic import basic
from logic.logic import conj
from server import tactic

thy = basic.loadTheory('logic_base')

class TacticTest(unittest.TestCase):
    def testRule(self):
        A = Var('A', boolT)
        B = Var('B', boolT)
        rule_tac = tactic.rule('conjI')
        goal = Thm([], conj(B, A))
        pt = rule_tac.get_proof_term(thy, ProofTerm.sorry(goal))
        prf = pt.export()
        self.assertEqual(thy.check_proof(prf), goal)

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
