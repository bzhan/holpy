# Author: Bohua Zhan

import unittest
import io

from kernel.type import TVar, TFun, hol_bool
from kernel.term import Term, Var
from kernel.thm import Thm
from kernel.proof import Proof
from kernel.report import ProofReport
from logic import logic
from logic.basic import BasicTheory
from logic.nat import Nat
from syntax import printer
from server import tactic
from server.tactic import ProofState

thy = BasicTheory

A = Var("A", hol_bool)
B = Var("B", hol_bool)
conj = logic.mk_conj
disj = logic.mk_disj
imp = Term.mk_implies
neg = logic.neg
exists = logic.mk_exists

def print_proof(prf):
    def term_printer(t):
        return printer.print_term(thy, t)
    return prf.print(term_printer=term_printer, print_vars=True)

class TacticTest(unittest.TestCase):

    def testCheckProof(self):
        """Proof of A & B --> B & A."""
        input = "\n".join([
            "var A :: bool",
            "var B :: bool",
            "A1: assume A & B",
            "S1: theorem conjD1",
            "S2: implies_elim from S1, A1",
            "S3: theorem conjD2",
            "S4: implies_elim from S3, A1",
            "S5: theorem conjI",
            "S6: substitution {A: B, B: A} from S5",
            "S7: implies_elim from S6, S4",
            "S8: implies_elim from S7, S2",
            "S9: implies_intr A & B from S8"])

        output = "\n".join([
            "var A :: bool",
            "var B :: bool",
            "A1: A & B |- A & B by assume A & B",
            "S1: |- A & B --> A by theorem conjD1",
            "S2: A & B |- A by implies_elim from S1, A1",
            "S3: |- A & B --> B by theorem conjD2",
            "S4: A & B |- B by implies_elim from S3, A1",
            "S5: |- A --> B --> A & B by theorem conjI",
            "S6: |- B --> A --> B & A by substitution {A: B, B: A} from S5",
            "S7: A & B |- A --> B & A by implies_elim from S6, S4",
            "S8: A & B |- B & A by implies_elim from S7, S2",
            "S9: |- A & B --> B & A by implies_intr A & B from S8"])

        prf = tactic.parse_proof(thy, io.StringIO(input))
        thy.check_proof(prf)
        self.assertEqual(print_proof(prf), output)

    def testCheckProof2(self):
        """Proof of A & B --> B & A, partial."""
        input = "\n".join([
            "var A :: bool",
            "var B :: bool",
            "A1: assume A & B",
            "S1: A & B |- B & A by sorry",
            "S2: implies_intr A & B from S1"])

        output = "\n".join([
            "var A :: bool",
            "var B :: bool",
            "A1: A & B |- A & B by assume A & B",
            "S1: A & B |- B & A by sorry",
            "S2: |- A & B --> B & A by implies_intr A & B from S1"])

        prf = tactic.parse_proof(thy, io.StringIO(input))
        thy.check_proof(prf)
        self.assertEqual(print_proof(prf), output)

    def testCheckProofMacro(self):
        """Proof of f = g --> x = y --> f x = g y."""
        input = "\n".join([
            "var x :: 'a",
            "var y :: 'a",
            "var f :: 'a => 'a",
            "var g :: 'a => 'a",
            "A1: assume f = g",
            "A2: assume x = y",
            "S1: arg_combination f from A2",
            "S2: fun_combination y from A1",
            "S3: transitive from S1, S2",
            "S4: implies_intr x = y from S3",
            "S5: implies_intr f = g from S4"])

        output = "\n".join([
            "var x :: 'a",
            "var y :: 'a",
            "var f :: 'a => 'a",
            "var g :: 'a => 'a",
            "A1: f = g |- f = g by assume f = g",
            "A2: x = y |- x = y by assume x = y",
            "S1: x = y |- f x = f y by arg_combination f from A2",
            "S2: f = g |- f y = g y by fun_combination y from A1",
            "S3: f = g, x = y |- f x = g y by transitive from S1, S2",
            "S4: f = g |- x = y --> f x = g y by implies_intr x = y from S3",
            "S5: |- f = g --> x = y --> f x = g y by implies_intr f = g from S4"])

        prf = tactic.parse_proof(thy, io.StringIO(input))
        thy.check_proof(prf)
        self.assertEqual(print_proof(prf), output)

    def testCheckProofDoubleNegInv(self):
        """Proof of ~~A --> A."""
        input = "\n".join([
            "var A :: bool",
            "A1: assume ~~A",
            "S1: theorem classical",
            "S2: assume A",
            "S3: assume ~A",
            "S4: apply_theorem negE from A1, S3",
            "S5: apply_theorem falseE from S4",
            "S6: implies_intr A from S2",
            "S7: implies_intr ~A from S5",
            "S8: apply_theorem disjE from S1, S6, S7",
            "S9: implies_intr ~~A from S8"])

        output = "\n".join([
            "var A :: bool",
            "A1: ~~A |- ~~A by assume ~~A",
            "S1: |- A | ~A by theorem classical",
            "S2: A |- A by assume A",
            "S3: ~A |- ~A by assume ~A",
            "S4: ~A, ~~A |- false by apply_theorem negE from A1, S3",
            "S5: ~A, ~~A |- A by apply_theorem falseE from S4",
            "S6: |- A --> A by implies_intr A from S2",
            "S7: ~~A |- ~A --> A by implies_intr ~A from S5",
            "S8: ~~A |- A by apply_theorem disjE from S1, S6, S7",
            "S9: |- ~~A --> A by implies_intr ~~A from S8"])

        prf = tactic.parse_proof(thy, io.StringIO(input))
        thy.check_proof(prf)
        self.assertEqual(print_proof(prf), output)

    def testInitProof(self):
        state = ProofState([A, B], [conj(A, B)], conj(B, A))
        self.assertEqual(state.prf.get_num_item(), 3)
        self.assertEqual(state.check_proof(), Thm.mk_implies(conj(A, B), conj(B, A)))

    def testGetCtxt(self):
        state = ProofState([A, B], [conj(A, B)], conj(B, A))
        self.assertEqual(state.get_ctxt(), {'A':hol_bool, 'B':hol_bool})

    def testAddLineAfter(self):
        state = ProofState([A, B], [conj(A, B)], conj(B, A))
        
        state.add_line_after("A1")
        self.assertEqual(state.prf.get_num_item(), 4)
        self.assertEqual(state.check_proof(), Thm.mk_implies(conj(A, B), conj(B, A)))
        self.assertEqual(state.prf.items[1].rule, "")

    def testAddLineAfter2(self):
        state = ProofState([A, B], [conj(A, B)], conj(B, A))

        state.add_line_after("S1")
        self.assertEqual(state.prf.get_num_item(), 4)
        self.assertEqual(state.check_proof(), Thm.mk_implies(conj(A, B), conj(B, A)))
        self.assertEqual(state.prf.items[2].rule, "")

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
        state.set_line("S1", "theorem", args="conjD1")
        self.assertEqual(state.prf.get_num_item(), 4)
        self.assertEqual(state.check_proof(), Thm.mk_implies(conj(A, B), conj(B, A)))

    def testApplyBackwardStepThms(self):
        state = ProofState([A, B], [conj(A, B)], conj(B, A))
        ths = state.apply_backward_step_thms("S1")
        self.assertEqual([name for name, _ in ths], ["conjI"])

    def testApplyBackwardStepThms2(self):
        state = ProofState([A, B], [disj(A, B)], disj(B, A))
        ths = state.apply_backward_step_thms("S1", prevs=["A1"])
        self.assertEqual([name for name, _ in ths], ["disjE"])

    def testApplyBackwardStep(self):
        state = ProofState([A, B], [conj(A, B)], conj(B, A))
        state.apply_backward_step("S1", "conjI")
        self.assertEqual(state.check_proof(), Thm.mk_implies(conj(A, B), conj(B, A)))
        self.assertEqual(len(state.rpt.gaps), 2)

    def testApplyBackwardStep2(self):
        """Case where one or more assumption also needs to be matched."""
        state = ProofState([A, B], [disj(A, B)], disj(B, A))
        state.apply_backward_step("S1", "disjE", prevs=["A1"])
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

    def testApplyInduction(self):
        n = Var("n", Nat.nat)
        state = ProofState([n], [], Term.mk_equals(Nat.plus(n, Nat.zero), n))
        state.apply_induction("S1", "nat_induct", "n")
        self.assertEqual(state.check_proof(), Thm([], Term.mk_equals(Nat.plus(n, Nat.zero), n)))
        self.assertEqual(state.prf.get_num_item(), 3)

    def testConjComm(self):
        """Proof of A & B --> B & A."""
        state = ProofState([A, B], [conj(A, B)], conj(B, A))
        state.apply_backward_step("S1", "conjI")
        state.set_line("S1", "apply_theorem", args="conjD2", prevs=["A1"])
        state.set_line("S2", "apply_theorem", args="conjD1", prevs=["A1"])
        self.assertEqual(state.check_proof(no_gaps=True), Thm.mk_implies(conj(A, B), conj(B, A)))

    def testDisjComm(self):
        """Proof of A | B --> B | A."""
        state = ProofState([A, B], [disj(A, B)], disj(B, A))
        state.apply_backward_step("S1", "disjE", prevs=["A1"])
        state.introduction("S1")
        state.apply_backward_step("S2", "disjI2", prevs=["S1"])
        state.introduction("S4")
        state.apply_backward_step("S5", "disjI1", prevs=["S4"])
        self.assertEqual(state.check_proof(no_gaps=True), Thm.mk_implies(disj(A, B), disj(B, A)))

    def testDoubleNegInv(self):
        """Proof of ~~A --> A."""
        state = ProofState([A], [neg(neg(A))], A)
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
        state = ProofState([A, B], [ex_conj], conj_ex)
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
        n = Var("n", Nat.nat)
        state = ProofState([n], [], Term.mk_equals(Nat.plus(n, Nat.zero), n))
        state.apply_induction("S1", "nat_induct", "n")
        state.rewrite_goal("S1", "plus_def_1")
        state.set_line("S1", "reflexive", args=Nat.zero)
        state.introduction("S3", names=["n"])
        state.rewrite_goal("S4", "plus_def_2")
        state.set_line("S4", "arg_combination", args=Nat.Suc, prevs=["S3"])
        self.assertEqual(state.check_proof(no_gaps=True), Thm.mk_equals(Nat.plus(n,Nat.zero),n))

    def testMultZeroRight(self):
        """Proof of n * 0 = 0 by induction."""
        n = Var("n", Nat.nat)
        state = ProofState([n], [], Term.mk_equals(Nat.times(n, Nat.zero), Nat.zero))
        state.apply_induction("S1", "nat_induct", "n")
        state.rewrite_goal("S1", "times_def_1")
        state.set_line("S1", "reflexive", args=Nat.zero)
        state.introduction("S3", names=["n"])
        state.rewrite_goal("S4", "times_def_2")
        state.rewrite_goal("S4", "plus_def_1")
        self.assertEqual(state.check_proof(no_gaps=True), Thm.mk_equals(Nat.times(n,Nat.zero),Nat.zero))


if __name__ == "__main__":
    unittest.main()
