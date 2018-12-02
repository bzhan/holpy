# Author: Bohua Zhan

import unittest

from kernel.type import TVar, TFun, hol_bool
from kernel.term import Term, Var
from kernel.thm import Thm
from kernel.proof import Proof
from kernel.report import ProofReport
from logic.logic import Logic
from logic.basic import BasicTheory
from syntax import printer
from server.tactic import ProofState

A = Var("A", hol_bool)
B = Var("B", hol_bool)
conj = Logic.mk_conj
disj = Logic.mk_disj
imp = Term.mk_implies
neg = Logic.neg
exists = Logic.mk_exists

class TacticTest(unittest.TestCase):
    def testInitProof(self):
        state = ProofState([A, B], [conj(A, B)], conj(B, A))
        self.assertEqual(state.prf.get_num_item(), 3)
        self.assertEqual(state.check_proof(), Thm.mk_implies(conj(A, B), conj(B, A)))

    def testAddLineAfter(self):
        state = ProofState([A, B], [conj(A, B)], conj(B, A))
        
        state.add_line_after("A1")
        self.assertEqual(state.prf.get_num_item(), 4)
        self.assertEqual(state.check_proof(), Thm.mk_implies(conj(A, B), conj(B, A)))
        self.assertEqual(state.prf.proof[1].rule, "")

    def testAddLineAfter2(self):
        state = ProofState([A, B], [conj(A, B)], conj(B, A))

        state.add_line_after("S1")
        self.assertEqual(state.prf.get_num_item(), 4)
        self.assertEqual(state.check_proof(), Thm.mk_implies(conj(A, B), conj(B, A)))
        self.assertEqual(state.prf.proof[2].rule, "")

    def testAddLineBefore(self):
        state = ProofState([A, B], [conj(A, B)], conj(B, A))

        state.add_line_before("S1", 1)
        self.assertEqual(state.prf.get_num_item(), 4)
        self.assertEqual(state.check_proof(), Thm.mk_implies(conj(A, B), conj(B, A)))

        state.add_line_before("S1", 3)
        self.assertEqual(state.prf.get_num_item(), 7)
        self.assertEqual(state.check_proof(), Thm.mk_implies(conj(A, B), conj(B, A)))

    def testRemoveLine(self):
        state = ProofState([A, B], [conj(A, B)], conj(B, A))
        state.add_line_after("A1")
        state.remove_line("S1")
        self.assertEqual(state.prf.get_num_item(), 3)
        self.assertEqual(state.check_proof(), Thm.mk_implies(conj(A, B), conj(B, A)))

    def testSetLine(self):
        state = ProofState([A, B], [conj(A, B)], conj(B, A))
        state.add_line_after("A1")
        state.set_line("S1", "theorem", args = "conjD1")
        self.assertEqual(state.prf.get_num_item(), 4)
        self.assertEqual(state.check_proof(), Thm.mk_implies(conj(A, B), conj(B, A)))

    def testApplyBackwardStep(self):
        state = ProofState([A, B], [conj(A, B)], conj(B, A))
        state.apply_backward_step("S1", "conjI")
        self.assertEqual(state.check_proof(), Thm.mk_implies(conj(A, B), conj(B, A)))
        self.assertEqual(len(state.rpt.gaps), 2)

    def testApplyBackwardStep2(self):
        """Case where one or more assumption also needs to be matched."""
        state = ProofState([A, B], [disj(A, B)], disj(B, A))
        state.apply_backward_step("S1", "disjE", prevs = ["A1"])
        self.assertEqual(state.check_proof(), Thm.mk_implies(disj(A, B), disj(B, A)))
        self.assertEqual(len(state.rpt.gaps), 2)

    def testIntroduction(self):
        state = ProofState([A, B], [], imp(disj(A, B), disj(B, A)))
        state.introduction("S1")
        self.assertEqual(state.check_proof(), Thm.mk_implies(disj(A, B), disj(B, A)))

    def testIntroduction2(self):
        state = ProofState([A, B], [], imp(A, B, conj(A, B)))
        state.introduction("S1")
        self.assertEqual(state.check_proof(), Thm.mk_implies(A, B, conj(A, B)))

    def testIntroduction3(self):
        Ta = TVar("a")
        A = Var("A", TFun(Ta, hol_bool))
        B = Var("B", TFun(Ta, hol_bool))
        x = Var("x", Ta)
        state = ProofState([A, B], [], Term.mk_all(x, imp(A(x), B(x))))
        state.introduction("S1", ["x"])
        self.assertEqual(state.check_proof(), Thm([], Term.mk_all(x, imp(A(x), B(x)))))
        self.assertEqual(state.prf.get_num_item(), 4)

    def testConjComm(self):
        """Proof of A & B --> B & A."""
        state = ProofState([A, B], [conj(A, B)], conj(B, A))
        state.apply_backward_step("S1", "conjI")
        state.set_line("S1", "apply_theorem", args = "conjD2", prevs = ["A1"])
        state.set_line("S2", "apply_theorem", args = "conjD1", prevs = ["A1"])
        self.assertEqual(state.check_proof(no_gaps=True), Thm.mk_implies(conj(A, B), conj(B, A)))

    def testDisjComm(self):
        """Proof of A | B --> B | A."""
        state = ProofState([A, B], [disj(A, B)], disj(B, A))
        state.apply_backward_step("S1", "disjE", prevs = ["A1"])
        state.introduction("S1")
        state.apply_backward_step("S2", "disjI2", prevs = ["S1"])
        state.introduction("S4")
        state.apply_backward_step("S5", "disjI1", prevs = ["S4"])
        self.assertEqual(state.check_proof(no_gaps=True), Thm.mk_implies(disj(A, B), disj(B, A)))

    def testDoubleNegInv(self):
        """Proof of ~~A --> A."""
        state = ProofState([A], [neg(neg(A))], A)
        state.add_line_after("A1")
        state.set_line("S1", "theorem", args = "classical")
        state.apply_backward_step("S2", "disjE", prevs = ["S1"])
        state.introduction("S2")        
        state.introduction("S4")
        state.apply_backward_step("S5", "falseE")
        state.apply_backward_step("S5", "negE", prevs = ["A1"])
        self.assertEqual(state.check_proof(no_gaps=True), Thm.mk_implies(neg(neg(A)), A))

    def testExistsConj(self):
        """Proof of (?x. A x & B x) --> (?x. A x) & (?x. B x)."""
        Ta = TVar("a")
        A = Var("A", TFun(Ta, hol_bool))
        B = Var("B", TFun(Ta, hol_bool))
        x = Var("x", Ta)
        ex_conj = exists(x,conj(A(x),B(x)))
        conj_ex = conj(exists(x,A(x)),exists(x,B(x)))
        state = ProofState([A, B], [ex_conj], conj_ex)
        state.apply_backward_step("S1", "conjI")
        state.apply_backward_step("S1", "exE", prevs = ["A1"])
        state.introduction("S1", "x")
        state.add_line_after("S1")
        state.set_line("S2", "apply_theorem", args = "conjD1", prevs = ["S1"])
        state.apply_backward_step("S3", "exI", prevs = ["S2"])
        state.apply_backward_step("S7", "exE", prevs = ["A1"])
        state.introduction("S7", "x")
        state.add_line_after("S7")
        state.set_line("S8", "apply_theorem", args = "conjD2", prevs = ["S7"])
        state.apply_backward_step("S9", "exI", prevs = ["S8"])
        self.assertEqual(state.check_proof(no_gaps=True), Thm.mk_implies(ex_conj, conj_ex))

if __name__ == "__main__":
    unittest.main()
