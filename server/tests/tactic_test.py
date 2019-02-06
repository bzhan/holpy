# Author: Bohua Zhan

import unittest
import io

from kernel.type import TVar, TFun, hol_bool
from kernel.term import Term, Var
from kernel.thm import Thm
from kernel.proof import Proof, print_thm_highlight
from kernel.report import ProofReport
from logic import logic
from logic import basic
from logic import nat
from syntax import printer
from server import tactic
from server.tactic import ProofState

thy = basic.BasicTheory

A = Var("A", hol_bool)
B = Var("B", hol_bool)
conj = logic.mk_conj
disj = logic.mk_disj
imp = Term.mk_implies
neg = logic.neg
exists = logic.mk_exists

class TacticTest(unittest.TestCase):
    def testInitProof(self):
        state = ProofState.init_state(thy, [A, B], [conj(A, B)], conj(B, A))
        self.assertEqual(len(state.prf.items), 3)
        self.assertEqual(state.check_proof(), Thm.mk_implies(conj(A, B), conj(B, A)))

    def testParseInitState(self):
        state = ProofState.parse_init_state(
            thy, {'vars': {'A': 'bool', 'B': 'bool'}, 'prop': "A & B --> B & A"})
        self.assertEqual(len(state.prf.items), 3)
        self.assertEqual(state.check_proof(), Thm.mk_implies(conj(A, B), conj(B, A)))

    def testJsonData(self):
        state = ProofState.parse_init_state(
            thy, {'vars': {'A': 'bool', 'B': 'bool'}, 'prop': "A & B --> B & A"})
        json_data = state.json_data()
        self.assertEqual(len(json_data['vars']), 2)
        self.assertEqual(len(json_data['proof']), 3)
        self.assertIn('report', json_data)

    def testParseProof(self):
        data = {
            'vars': {'A': 'bool', 'B': 'bool'},
            'proof': [
                {'id': 'A1', 'rule': 'assume', 'args': 'A & B', 'prevs': [], 'th': ''},
                {'id': 'S1', 'rule': 'sorry', 'args': '', 'prevs': [], 'th': 'A & B |- B & A'},
                {'id': 'S2', 'rule': 'implies_intr', 'args': 'A & B', 'prevs': ['S1'], 'th': ''}
            ]
        }
        state = ProofState.parse_proof(thy, data)
        self.assertEqual(len(state.vars), 2)
        self.assertEqual(len(state.prf.items), 3)

    def testGetCtxt(self):
        state = ProofState.init_state(thy, [A, B], [conj(A, B)], conj(B, A))
        self.assertEqual(state.get_ctxt(), {'A':hol_bool, 'B':hol_bool})

    def testAddLineAfter(self):
        state = ProofState.init_state(thy, [A, B], [conj(A, B)], conj(B, A))
        
        state.add_line_after("A1")
        self.assertEqual(len(state.prf.items), 4)
        self.assertEqual(state.check_proof(), Thm.mk_implies(conj(A, B), conj(B, A)))
        self.assertEqual(state.prf.items[1].rule, "")

    def testAddLineAfter2(self):
        state = ProofState.init_state(thy, [A, B], [conj(A, B)], conj(B, A))

        state.add_line_after("S1")
        self.assertEqual(len(state.prf.items), 4)
        self.assertEqual(state.check_proof(), Thm.mk_implies(conj(A, B), conj(B, A)))
        self.assertEqual(state.prf.items[2].rule, "")

    def testAddLineBefore(self):
        state = ProofState.init_state(thy, [A, B], [conj(A, B)], conj(B, A))

        state.add_line_before("S1", 1)
        self.assertEqual(len(state.prf.items), 4)
        self.assertEqual(state.check_proof(), Thm.mk_implies(conj(A, B), conj(B, A)))

        state.add_line_before("S1", 3)
        self.assertEqual(len(state.prf.items), 7)
        self.assertEqual(state.check_proof(), Thm.mk_implies(conj(A, B), conj(B, A)))

    def testRemoveLine(self):
        state = ProofState.init_state(thy, [A, B], [conj(A, B)], conj(B, A))
        state.add_line_after("A1")
        state.remove_line("S1")
        self.assertEqual(len(state.prf.items), 3)
        self.assertEqual(state.check_proof(), Thm.mk_implies(conj(A, B), conj(B, A)))

    def testSetLine(self):
        state = ProofState.init_state(thy, [A, B], [conj(A, B)], conj(B, A))
        state.add_line_after("A1")
        state.set_line("S1", "theorem", args="conjD1")
        self.assertEqual(len(state.prf.items), 4)
        self.assertEqual(state.check_proof(), Thm.mk_implies(conj(A, B), conj(B, A)))

    def testApplyBackwardStepThms(self):
        state = ProofState.init_state(thy, [A, B], [conj(A, B)], conj(B, A))
        ths = state.apply_backward_step_thms("S1")
        self.assertEqual([name for name, _ in ths], ["conjI"])

    def testApplyBackwardStepThms2(self):
        state = ProofState.init_state(thy, [A, B], [disj(A, B)], disj(B, A))
        ths = state.apply_backward_step_thms("S1", prevs=["A1"])
        self.assertEqual([name for name, _ in ths], ["disjE"])

    def testApplyBackwardStepThms3(self):
        """Example of two results."""
        state = ProofState.init_state(thy, [A, B], [disj(A, B)], disj(B, A))
        ths = state.apply_backward_step_thms("S1")
        self.assertEqual([name for name, _ in ths], ["disjI1", "disjI2"])

    def testApplyBackwardStep(self):
        state = ProofState.init_state(thy, [A, B], [conj(A, B)], conj(B, A))
        state.apply_backward_step("S1", "conjI")
        self.assertEqual(state.check_proof(), Thm.mk_implies(conj(A, B), conj(B, A)))
        self.assertEqual(len(state.rpt.gaps), 2)

    def testApplyBackwardStep2(self):
        """Case where one or more assumption also needs to be matched."""
        state = ProofState.init_state(thy, [A, B], [disj(A, B)], disj(B, A))
        state.apply_backward_step("S1", "disjE", prevs=["A1"])
        self.assertEqual(state.check_proof(), Thm.mk_implies(disj(A, B), disj(B, A)))
        self.assertEqual(len(state.rpt.gaps), 2)

    def testIntroduction(self):
        state = ProofState.init_state(thy, [A, B], [], imp(disj(A, B), disj(B, A)))
        state.introduction("S1")
        self.assertEqual(state.check_proof(), Thm.mk_implies(disj(A, B), disj(B, A)))

    def testIntroduction2(self):
        state = ProofState.init_state(thy, [A, B], [], imp(A, B, conj(A, B)))
        state.introduction("S1")
        self.assertEqual(state.check_proof(), Thm.mk_implies(A, B, conj(A, B)))

    def testIntroduction3(self):
        Ta = TVar("a")
        A = Var("A", TFun(Ta, hol_bool))
        B = Var("B", TFun(Ta, hol_bool))
        x = Var("x", Ta)
        state = ProofState.init_state(thy, [A, B], [], Term.mk_all(x, imp(A(x), B(x))))
        state.introduction("S1", ["x"])
        self.assertEqual(state.check_proof(), Thm([], Term.mk_all(x, imp(A(x), B(x)))))
        self.assertEqual(len(state.prf.items), 4)

    def testApplyInduction(self):
        thy = basic.NatTheory
        n = Var("n", nat.natT)
        state = ProofState.init_state(thy, [n], [], Term.mk_equals(nat.plus(n, nat.zero), n))
        state.apply_induction("S1", "nat_induct", "n")
        self.assertEqual(state.check_proof(), Thm([], Term.mk_equals(nat.plus(n, nat.zero), n)))
        self.assertEqual(len(state.prf.items), 3)

    def testConjComm(self):
        """Proof of A & B --> B & A."""
        state = ProofState.init_state(thy, [A, B], [conj(A, B)], conj(B, A))
        state.apply_backward_step("S1", "conjI")
        state.set_line("S1", "apply_theorem", args="conjD2", prevs=["A1"])
        state.set_line("S2", "apply_theorem", args="conjD1", prevs=["A1"])
        self.assertEqual(state.check_proof(no_gaps=True), Thm.mk_implies(conj(A, B), conj(B, A)))

    def testDisjComm(self):
        """Proof of A | B --> B | A."""
        state = ProofState.init_state(thy, [A, B], [disj(A, B)], disj(B, A))
        state.apply_backward_step("S1", "disjE", prevs=["A1"])
        state.introduction("S1")
        state.apply_backward_step("S2", "disjI2", prevs=["S1"])
        state.introduction("S4")
        state.apply_backward_step("S5", "disjI1", prevs=["S4"])
        self.assertEqual(state.check_proof(no_gaps=True), Thm.mk_implies(disj(A, B), disj(B, A)))

    def testDoubleNegInv(self):
        """Proof of ~~A --> A."""
        state = ProofState.init_state(thy, [A], [neg(neg(A))], A)
        state.add_line_after("A1")
        state.set_line("S1", "theorem", args="classical")
        state.apply_backward_step("S2", "disjE", prevs=["S1"])
        state.introduction("S2")        
        state.introduction("S4")
        state.apply_backward_step("S5", "falseE")
        state.apply_backward_step("S5", "negE", prevs=["A1"])
        self.assertEqual(state.check_proof(no_gaps=True), Thm.mk_implies(neg(neg(A)), A))

    def testExistsConj(self):
        """Proof of (?x. A x & B x) --> (?x. A x) & (?x. B x)."""
        Ta = TVar("a")
        A = Var("A", TFun(Ta, hol_bool))
        B = Var("B", TFun(Ta, hol_bool))
        x = Var("x", Ta)
        ex_conj = exists(x,conj(A(x),B(x)))
        conj_ex = conj(exists(x,A(x)),exists(x,B(x)))
        state = ProofState.init_state(thy, [A, B], [ex_conj], conj_ex)
        state.apply_backward_step("S1", "conjI")
        state.apply_backward_step("S1", "exE", prevs=["A1"])
        state.introduction("S1", "x")
        state.add_line_after("S1")
        state.set_line("S2", "apply_theorem", args="conjD1", prevs=["S1"])
        state.apply_backward_step("S3", "exI", prevs=["S2"])
        state.apply_backward_step("S7", "exE", prevs=["A1"])
        state.introduction("S7", "x")
        state.add_line_after("S7")
        state.set_line("S8", "apply_theorem", args="conjD2", prevs=["S7"])
        state.apply_backward_step("S9", "exI", prevs=["S8"])
        self.assertEqual(state.check_proof(no_gaps=True), Thm.mk_implies(ex_conj, conj_ex))

    def testAddZeroRight(self):
        """Proof of n + 0 = n by induction."""
        thy = basic.NatTheory
        n = Var("n", nat.natT)
        state = ProofState.init_state(thy, [n], [], Term.mk_equals(nat.plus(n, nat.zero), n))
        state.apply_induction("S1", "nat_induct", "n")
        state.rewrite_goal("S1", "plus_def_1")
        state.set_line("S1", "reflexive", args=nat.zero)
        state.introduction("S3", names=["n"])
        state.rewrite_goal("S4", "plus_def_2")
        state.set_line("S4", "arg_combination", args=nat.Suc, prevs=["S3"])
        self.assertEqual(state.check_proof(no_gaps=True), Thm.mk_equals(nat.plus(n,nat.zero),n))

    def testMultZeroRight(self):
        """Proof of n * 0 = 0 by induction."""
        thy = basic.NatTheory
        n = Var("n", nat.natT)
        state = ProofState.init_state(thy, [n], [], Term.mk_equals(nat.times(n, nat.zero), nat.zero))
        state.apply_induction("S1", "nat_induct", "n")
        state.rewrite_goal("S1", "times_def_1")
        state.set_line("S1", "reflexive", args=nat.zero)
        state.introduction("S3", names=["n"])
        state.rewrite_goal("S4", "times_def_2")
        state.rewrite_goal("S4", "plus_def_1")
        self.assertEqual(state.check_proof(no_gaps=True), Thm.mk_equals(nat.times(n,nat.zero),nat.zero))

    def testRewriteGoal(self):
        thy = basic.NatTheory
        n = Var("n", nat.natT)
        state = ProofState.init_state(thy, [n], [], Term.mk_equals(nat.plus(nat.zero, n), n))
        ths = state.rewrite_goal_thms("S1")
        self.assertEqual([name for name, _ in ths], ["add_comm", "plus_def_1"])

    def testPrintThmHighlight(self):
        A = Var('A', hol_bool)
        B = Var('B', hol_bool)
        A_to_B = Term.mk_implies(A, B)
        th = Thm([A, A_to_B], B)
        p = lambda t: printer.print_term(thy, t)
        res = print_thm_highlight(th, term_printer=p, highlight=True)
        self.assertEqual(res, [('A',2),(', ',0),('A',2),(' --> ',0),('B',2),(' ',0),('|-',0),(' ',0),('B',2)])


if __name__ == "__main__":
    unittest.main()
