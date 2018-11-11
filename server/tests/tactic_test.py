# Author: Bohua Zhan

import unittest

from kernel.type import hol_bool
from kernel.term import Var
from kernel.thm import Thm
from kernel.proof import Proof
from kernel.report import ProofReport
from logic.logic import Logic
from logic.basic import BasicTheory
import server.tactic as tactic

thy = BasicTheory()

A = Var("A", hol_bool)
B = Var("B", hol_bool)
conj = Logic.mk_conj

class TacticTest(unittest.TestCase):
    def testInitProof(self):
        prf = tactic.init_proof([A, B], [conj(A, B)], conj(B, A))
        self.assertEqual(prf.get_num_item(), 3)
        self.assertEqual(thy.check_proof(prf), Thm.mk_implies(conj(A, B), conj(B, A)))

    def testAddLineAfter(self):
        prf = tactic.init_proof([A, B], [conj(A, B)], conj(B, A))
        
        prf2 = tactic.add_line_after(prf, "A1")
        self.assertEqual(prf2.get_num_item(), 4)
        self.assertEqual(thy.check_proof(prf2), Thm.mk_implies(conj(A, B), conj(B, A)))
        self.assertEqual(prf2.proof[1].rule, "")

        prf3 = tactic.add_line_after(prf, "S1")
        self.assertEqual(prf3.get_num_item(), 4)
        self.assertEqual(thy.check_proof(prf3), Thm.mk_implies(conj(A, B), conj(B, A)))
        self.assertEqual(prf3.proof[2].rule, "")

    def testAddLineBefore(self):
        prf = tactic.init_proof([A, B], [conj(A, B)], conj(B, A))

        prf2 = tactic.add_line_before(prf, "S1", 1)
        self.assertEqual(prf2.get_num_item(), 4)
        self.assertEqual(thy.check_proof(prf2), Thm.mk_implies(conj(A, B), conj(B, A)))

        prf3 = tactic.add_line_before(prf, "S1", 3)
        self.assertEqual(prf3.get_num_item(), 6)
        self.assertEqual(thy.check_proof(prf3), Thm.mk_implies(conj(A, B), conj(B, A)))

    def testRemoveLine(self):
        prf = tactic.init_proof([A, B], [conj(A, B)], conj(B, A))
        prf2 = tactic.add_line_after(prf, "A1")
        prf3 = tactic.remove_line(prf2, "S1")
        self.assertEqual(prf, prf3)

    def testSetLine(self):
        prf = tactic.init_proof([A, B], [conj(A, B)], conj(B, A))
        prf2 = tactic.add_line_after(prf, "A1")
        prf2 = tactic.set_line(prf2, "S1", "theorem", args = "conjD1")
        self.assertEqual(prf2.get_num_item(), 4)
        self.assertEqual(thy.check_proof(prf2), Thm.mk_implies(conj(A, B), conj(B, A)))

    def testApplyBackwardStep(self):
        prf = tactic.init_proof([A, B], [conj(A, B)], conj(B, A))
        prf2 = tactic.apply_backward_step(prf, "S1", thy, "conjI")
        rpt = ProofReport()
        self.assertEqual(thy.check_proof(prf2, rpt), Thm.mk_implies(conj(A, B), conj(B, A)))
        self.assertEqual(len(rpt.gaps), 2)

    def testConjComm(self):
        """Proof of A & B --> B & A."""
        prf = tactic.init_proof([A, B], [conj(A, B)], conj(B, A))
        prf = tactic.apply_backward_step(prf, "S1", thy, "conjI")
        prf = tactic.set_line(prf, "S1", "apply_theorem", args = "conjD2", prevs = ["A1"])
        prf = tactic.set_line(prf, "S2", "apply_theorem", args = "conjD1", prevs = ["A1"])
        rpt = ProofReport()
        self.assertEqual(thy.check_proof(prf, rpt), Thm.mk_implies(conj(A, B), conj(B, A)))
        self.assertEqual(len(rpt.gaps), 0)


if __name__ == "__main__":
    unittest.main()
