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
import server.tactic as tactic

thy = BasicTheory()

A = Var("A", hol_bool)
B = Var("B", hol_bool)
conj = Logic.mk_conj
disj = Logic.mk_disj
imp = Term.mk_implies
neg = Logic.neg
exists = Logic.mk_exists

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
        prf = tactic.add_line_after(prf, "A1")
        prf = tactic.set_line(prf, "S1", "theorem", args = "conjD1")
        self.assertEqual(prf.get_num_item(), 4)
        self.assertEqual(thy.check_proof(prf), Thm.mk_implies(conj(A, B), conj(B, A)))

    def testApplyBackwardStep(self):
        prf = tactic.init_proof([A, B], [conj(A, B)], conj(B, A))
        prf = tactic.apply_backward_step(prf, "S1", thy, "conjI")
        rpt = ProofReport()
        self.assertEqual(thy.check_proof(prf, rpt), Thm.mk_implies(conj(A, B), conj(B, A)))
        self.assertEqual(len(rpt.gaps), 2)

    def testApplyBackwardStep2(self):
        """Case where one or more assumption also needs to be matched."""
        prf = tactic.init_proof([A, B], [disj(A, B)], disj(B, A))
        thy.check_proof(prf)
        prf = tactic.apply_backward_step(prf, "S1", thy, "disjE", prevs = ["A1"])
        rpt = ProofReport()
        self.assertEqual(thy.check_proof(prf, rpt), Thm.mk_implies(disj(A, B), disj(B, A)))
        self.assertEqual(len(rpt.gaps), 2)

    def testIntroduction(self):
        prf = tactic.init_proof([A, B], [], imp(disj(A, B), disj(B, A)))
        prf = tactic.introduction(prf, "S1")
        self.assertEqual(thy.check_proof(prf), Thm.mk_implies(disj(A, B), disj(B, A)))

    def testIntroduction2(self):
        prf = tactic.init_proof([A, B], [], imp(A, B, conj(A, B)))
        prf = tactic.introduction(prf, "S1")
        self.assertEqual(thy.check_proof(prf), Thm.mk_implies(A, B, conj(A, B)))

    def testIntroduction3(self):
        Ta = TVar("a")
        A = Var("A", TFun(Ta, hol_bool))
        B = Var("B", TFun(Ta, hol_bool))
        x = Var("x", Ta)
        prf = tactic.init_proof([A, B], [], Term.mk_all(x, imp(A(x), B(x))))
        prf = tactic.introduction(prf, "S1", ["x"])
        self.assertEqual(thy.check_proof(prf), Thm([], Term.mk_all(x, imp(A(x), B(x)))))
        self.assertEqual(prf.get_num_item(), 4)

    def testConjComm(self):
        """Proof of A & B --> B & A."""
        prf = tactic.init_proof([A, B], [conj(A, B)], conj(B, A))
        prf = tactic.apply_backward_step(prf, "S1", thy, "conjI")
        prf = tactic.set_line(prf, "S1", "apply_theorem", args = "conjD2", prevs = ["A1"])
        prf = tactic.set_line(prf, "S2", "apply_theorem", args = "conjD1", prevs = ["A1"])
        rpt = ProofReport()
        self.assertEqual(thy.check_proof(prf, rpt), Thm.mk_implies(conj(A, B), conj(B, A)))
        self.assertEqual(len(rpt.gaps), 0)

    def testDisjComm(self):
        """Proof of A | B --> B | A."""
        prf = tactic.init_proof([A, B], [disj(A, B)], disj(B, A))
        thy.check_proof(prf)
        prf = tactic.apply_backward_step(prf, "S1", thy, "disjE", prevs = ["A1"])
        prf = tactic.introduction(prf, "S1")
        thy.check_proof(prf)
        prf = tactic.apply_backward_step(prf, "S2", thy, "disjI2", prevs = ["S1"])
        prf = tactic.introduction(prf, "S4")
        thy.check_proof(prf)
        prf = tactic.apply_backward_step(prf, "S5", thy, "disjI1", prevs = ["S4"])
        rpt = ProofReport()
        self.assertEqual(thy.check_proof(prf, rpt), Thm.mk_implies(disj(A, B), disj(B, A)))
        self.assertEqual(len(rpt.gaps), 0)

    def testDoubleNegInv(self):
        """Proof of ~~A --> A."""
        prf = tactic.init_proof([A], [neg(neg(A))], A)
        prf = tactic.add_line_after(prf, "A1")
        prf = tactic.set_line(prf, "S1", "theorem", args = "classical")
        thy.check_proof(prf)
        prf = tactic.apply_backward_step(prf, "S2", thy, "disjE", prevs = ["S1"])
        prf = tactic.introduction(prf, "S2")        
        prf = tactic.introduction(prf, "S4")
        prf = tactic.apply_backward_step(prf, "S5", thy, "falseE")
        prf = tactic.apply_backward_step(prf, "S5", thy, "negE", prevs = ["A1"])
        rpt = ProofReport()
        self.assertEqual(thy.check_proof(prf, rpt), Thm.mk_implies(neg(neg(A)), A))
        self.assertEqual(len(rpt.gaps), 0)

    def testExistsConj(self):
        """Proof of (?x. A x & B x) --> (?x. A x) & (?x. B x)."""
        Ta = TVar("a")
        A = Var("A", TFun(Ta, hol_bool))
        B = Var("B", TFun(Ta, hol_bool))
        x = Var("x", Ta)
        ex_conj = exists(x,conj(A(x),B(x)))
        conj_ex = conj(exists(x,A(x)),exists(x,B(x)))
        prf = tactic.init_proof([A, B], [ex_conj], conj_ex)
        prf = tactic.apply_backward_step(prf, "S1", thy, "conjI")
        thy.check_proof(prf)
        prf = tactic.apply_backward_step(prf, "S1", thy, "exE", prevs = ["A1"])
        thy.check_proof(prf)
        prf = tactic.introduction(prf, "S1", "x")
        thy.check_proof(prf)
        prf = tactic.add_line_after(prf, "S1")
        prf = tactic.set_line(prf, "S2", "apply_theorem", args = "conjD1", prevs = ["S1"])
        thy.check_proof(prf)
        prf = tactic.apply_backward_step(prf, "S3", thy, "exI", prevs = ["S2"])
        thy.check_proof(prf)
        prf = tactic.apply_backward_step(prf, "S7", thy, "exE", prevs = ["A1"])
        thy.check_proof(prf)
        prf = tactic.introduction(prf, "S7", "x")
        thy.check_proof(prf)
        prf = tactic.add_line_after(prf, "S7")
        prf = tactic.set_line(prf, "S8", "apply_theorem", args = "conjD2", prevs = ["S7"])
        thy.check_proof(prf)
        prf = tactic.apply_backward_step(prf, "S9", thy, "exI", prevs = ["S8"])
        rpt = ProofReport()
        self.assertEqual(thy.check_proof(prf, rpt), Thm.mk_implies(ex_conj, conj_ex))
        self.assertEqual(len(rpt.gaps), 0)

if __name__ == "__main__":
    unittest.main()
