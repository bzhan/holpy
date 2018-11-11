# Author: Bohua Zhan

import unittest

from kernel.type import TVar, TFun, hol_bool
from kernel.term import Var, Term
from kernel.thm import Thm
from kernel.proof import Proof
from kernel.report import ProofReport
from kernel.theory import Theory
import logic.basic as basic
from logic.basic import Logic, Nat

Ta = TVar("a")
x = Var("x", Ta)
y = Var("y", Ta)
f = Var("f", TFun(Ta,Ta))
g = Var("g", TFun(Ta,Ta))

class BasicTest(unittest.TestCase):
    def testArgCombination(self):
        th = Thm.mk_equals(x,y)
        res = Thm.mk_equals(f(x),f(y))
        macro = basic.arg_combination_macro()
        self.assertEqual(macro(f, th), res)
        prf = macro.expand(1, f, ((0, "S1"), th))
        
        thy = Theory.EmptyTheory()
        self.assertEqual(prf.get_num_item(), 2)
        self.assertEqual(thy.check_proof_incr(1, {(0, "S1"): th}, prf), res)

    def testFunCombination(self):
        th = Thm.mk_equals(f,g)
        res = Thm.mk_equals(f(x),g(x))
        macro = basic.fun_combination_macro()
        self.assertEqual(macro(x, th), res)
        prf = macro.expand(1, x, ((0, "S1"), th))

        thy = Theory.EmptyTheory()
        self.assertEqual(prf.get_num_item(), 2)
        self.assertEqual(thy.check_proof_incr(1, {(0, "S1"): th}, prf), res)

    def testCombination(self):
        """Test arg and fun combination together using proofs."""
        thy = basic.BasicTheory()

        prf = Proof(Term.mk_equals(f,g), Term.mk_equals(x,y))
        prf.add_item("S1", "arg_combination", args = f, prevs = ["A2"])
        prf.add_item("S2", "fun_combination", args = y, prevs = ["A1"])
        prf.add_item("S3", "transitive", prevs = ["S1", "S2"])
        prf.add_item("S4", "implies_intr", args = Term.mk_equals(x,y), prevs = ["S3"])
        prf.add_item("S5", "implies_intr", args = Term.mk_equals(f,g), prevs = ["S4"])
        th = Thm.mk_implies(Term.mk_equals(f,g), Term.mk_equals(x,y), Term.mk_equals(f(x),g(y)))
        self.assertEqual(thy.check_proof(prf), th)

    def testBetaNorm(self):
        thy = basic.BasicTheory()

        t = Term.mk_abs(x, f(x))
        prf = Proof(Term.mk_equals(t(x), y))
        prf.add_item("S1", "beta_norm", prevs = ["A1"])
        prf.add_item("S2", "implies_intr", args = Term.mk_equals(t(x), y), prevs = ["S1"])

        th = Thm.mk_implies(Term.mk_equals(t(x), y), Term.mk_equals(f(x), y))
        rpt = ProofReport()
        self.assertEqual(thy.check_proof(prf, rpt), th)
        self.assertEqual(rpt.prim_steps, 8)

        thy.check_level = 1
        rpt2 = ProofReport()
        self.assertEqual(thy.check_proof(prf, rpt2), th)
        self.assertEqual(rpt2.prim_steps, 2)
        self.assertEqual(rpt2.macro_steps, 1)

    def testConjComm(self):
        """Proof of commutativity of conjunction."""
        thy = basic.BasicTheory()
        A = Var("A", hol_bool)
        B = Var("B", hol_bool)

        prf = Proof(Logic.mk_conj(A, B))
        prf.add_item("S1", "theorem", args = "conjD1")
        prf.add_item("S2", "implies_elim", prevs = ["S1", "A1"])
        prf.add_item("S3", "theorem", args = "conjD2")
        prf.add_item("S4", "implies_elim", prevs = ["S3", "A1"])
        prf.add_item("S5", "theorem", args = "conjI")
        prf.add_item("S6", "substitution", args = {"A": B, "B": A}, prevs = ["S5"])
        prf.add_item("S7", "implies_elim", prevs = ["S6", "S4"])
        prf.add_item("S8", "implies_elim", prevs = ["S7", "S2"])
        prf.add_item("S9", "implies_intr", args = Logic.mk_conj(A, B), prevs = ["S8"])
        th = Thm.mk_implies(Logic.mk_conj(A, B), Logic.mk_conj(B, A))
        self.assertEqual(thy.check_proof(prf), th)

    def testConjCommWithMacro(self):
        """Proof of commutativity of conjunction, with macros."""
        thy = basic.BasicTheory()
        A = Var("A", hol_bool)
        B = Var("B", hol_bool)

        prf = Proof(Logic.mk_conj(A, B))
        prf.add_item("S1", "apply_theorem", args = "conjD1", prevs = ["A1"])
        prf.add_item("S2", "apply_theorem", args = "conjD2", prevs = ["A1"])
        prf.add_item("S3", "apply_theorem", args = "conjI", prevs = ["S2", "S1"])
        prf.add_item("S4", "implies_intr", args = Logic.mk_conj(A, B), prevs = ["S3"])
        th = Thm.mk_implies(Logic.mk_conj(A, B), Logic.mk_conj(B, A))
        self.assertEqual(thy.check_proof(prf), th)

    def testDisjComm(self):
        """Proof of commutativity of disjunction."""
        thy = basic.BasicTheory()
        A = Var("A", hol_bool)
        B = Var("B", hol_bool)
        disjAB = Logic.mk_disj(A, B)
        disjBA = Logic.mk_disj(B, A)

        prf = Proof(disjAB)
        prf.add_item("S1", "theorem", args = "disjI2")
        prf.add_item("S2", "substitution", args = {"A": B, "B": A}, prevs = ["S1"])
        prf.add_item("S3", "theorem", args = "disjI1")
        prf.add_item("S4", "substitution", args = {"A": B, "B": A}, prevs = ["S3"])
        prf.add_item("S5", "theorem", args = "disjE")
        prf.add_item("S6", "substitution", args = {"C": disjBA}, prevs = ["S5"])
        prf.add_item("S7", "implies_elim", prevs = ["S6", "A1"])
        prf.add_item("S8", "implies_elim", prevs = ["S7", "S2"])
        prf.add_item("S9", "implies_elim", prevs = ["S8", "S4"])
        prf.add_item("S10", "implies_intr", args = disjAB, prevs = ["S9"])
        th = Thm.mk_implies(disjAB, disjBA)
        self.assertEqual(thy.check_proof(prf), th)

    def testAllConj(self):
        """Proof of (!x. A x & B x) --> (!x. A x) & (!x. B x)."""
        thy = basic.BasicTheory()
        Ta = TVar("a")
        A = Var("A", TFun(Ta, hol_bool))
        B = Var("B", TFun(Ta, hol_bool))
        x = Var("x", Ta)
        all_conj = Term.mk_all(x, Logic.mk_conj(A(x), B(x)))
        all_A = Term.mk_all(x, A(x))
        all_B = Term.mk_all(x, B(x))
        conj_all = Logic.mk_conj(all_A, all_B)

        prf = Proof(all_conj)
        prf.add_item("S1", "forall_elim", args = x, prevs = ["A1"])
        prf.add_item("S2", "theorem", args = "conjD1")
        prf.add_item("S3", "substitution", args = {"A": A(x), "B": B(x)}, prevs = ["S2"])
        prf.add_item("S4", "implies_elim", prevs = ["S3", "S1"])
        prf.add_item("S5", "forall_intr", args = x, prevs = ["S4"])
        prf.add_item("S6", "theorem", args = "conjD2")
        prf.add_item("S7", "substitution", args = {"A": A(x), "B": B(x)}, prevs = ["S6"])
        prf.add_item("S8", "implies_elim", prevs = ["S7", "S1"])
        prf.add_item("S9", "forall_intr", args = x, prevs = ["S8"])
        prf.add_item("S10", "theorem", args = "conjI")
        prf.add_item("S11", "substitution", args = {"A": all_A, "B": all_B}, prevs = ["S10"])
        prf.add_item("S12", "implies_elim", prevs = ["S11", "S5"])
        prf.add_item("S13", "implies_elim", prevs = ["S12", "S9"])
        prf.add_item("S14", "implies_intr", args = all_conj, prevs = ["S13"])
        th = Thm.mk_implies(all_conj, conj_all)
        self.assertEqual(thy.check_proof(prf), th)

    def testDoubleNeg(self):
        """Proof of A --> ~~A."""
        thy = basic.BasicTheory()
        A = Var("A", hol_bool)
        neg = Logic.neg

        prf = Proof(A)
        prf.add_item("S1", "assume", args = neg(A))
        prf.add_item("S2", "theorem", args = "negE")
        prf.add_item("S3", "implies_elim", prevs = ["S2", "S1"])
        prf.add_item("S4", "implies_elim", prevs = ["S3", "A1"])
        prf.add_item("S5", "implies_intr", args = neg(A), prevs = ["S4"])
        prf.add_item("S6", "theorem", args = "negI")
        prf.add_item("S7", "substitution", args = {"A": neg(A)}, prevs = ["S6"])
        prf.add_item("S8", "implies_elim", prevs = ["S7", "S5"])
        prf.add_item("S9", "implies_intr", args = A, prevs = ["S8"])
        th = Thm.mk_implies(A, neg(neg(A)))
        self.assertEqual(thy.check_proof(prf), th)

    def testDoubleNegInv(self):
        """Proof of ~~A --> A, requires classical axiom."""
        thy = basic.BasicTheory()
        A = Var("A", hol_bool)
        neg = Logic.neg

        prf = Proof(neg(neg(A)))
        prf.add_item("S1", "theorem", args = "classical")
        prf.add_item("S2", "assume", args = A)
        prf.add_item("S3", "assume", args = neg(A))
        prf.add_item("S4", "theorem", args = "negE")
        prf.add_item("S5", "substitution", args = {"A": neg(A)}, prevs = ["S4"])
        prf.add_item("S6", "implies_elim", prevs = ["S5", "A1"])
        prf.add_item("S7", "implies_elim", prevs = ["S6", "S3"])
        prf.add_item("S8", "theorem", args = "falseE")
        prf.add_item("S9", "implies_elim", prevs = ["S8", "S7"])
        prf.add_item("S10", "implies_intr", args = A, prevs = ["S2"])
        prf.add_item("S11", "implies_intr", args = neg(A), prevs = ["S9"])
        prf.add_item("S12", "theorem", args = "disjE")
        prf.add_item("S13", "substitution", args = {"B": neg(A), "C": A}, prevs = ["S12"])
        prf.add_item("S14", "implies_elim", prevs = ["S13", "S1"])
        prf.add_item("S15", "implies_elim", prevs = ["S14", "S10"])
        prf.add_item("S16", "implies_elim", prevs = ["S15", "S11"])
        prf.add_item("S17", "implies_intr", args = neg(neg(A)), prevs = ["S16"])
        th = Thm.mk_implies(neg(neg(A)), A)
        self.assertEqual(thy.check_proof(prf), th)

    def testDoubleNegInvWithMacro(self):
        """Proof of ~~A --> A, using macros."""
        thy = basic.BasicTheory()
        A = Var("A", hol_bool)
        neg = Logic.neg

        prf = Proof(neg(neg(A)))
        prf.add_item("S1", "theorem", args = "classical")
        prf.add_item("S2", "assume", args = A)
        prf.add_item("S3", "assume", args = neg(A))
        prf.add_item("S4", "apply_theorem", args = "negE", prevs = ["A1", "S3"])
        prf.add_item("S5", "apply_theorem", args = "falseE", prevs = ["S4"])
        prf.add_item("S6", "implies_intr", args = A, prevs = ["S2"])
        prf.add_item("S7", "implies_intr", args = neg(A), prevs = ["S5"])
        prf.add_item("S8", "apply_theorem", args = "disjE", prevs = ["S1", "S6", "S7"])
        prf.add_item("S9", "implies_intr", args = neg(neg(A)), prevs = ["S8"])
        th = Thm.mk_implies(neg(neg(A)), A)
        self.assertEqual(thy.check_proof(prf), th)

    def testTrueAbsorb(self):
        """Proof of A --> true & A."""
        thy = basic.BasicTheory()
        A = Var("A", hol_bool)

        prf = Proof(A)
        prf.add_item("S1", "theorem", args = "trueI")
        prf.add_item("S2", "theorem", args = "conjI")
        prf.add_item("S3", "substitution", args = {"A": Logic.true, "B": A}, prevs = ["S2"])
        prf.add_item("S4", "implies_elim", prevs = ["S3", "S1"])
        prf.add_item("S5", "implies_elim", prevs = ["S4", "A1"])
        prf.add_item("S6", "implies_intr", args = A, prevs = ["S5"])
        th = Thm.mk_implies(A, Logic.mk_conj(Logic.true, A))
        self.assertEqual(thy.check_proof(prf), th)
        
    def testExistsConj(self):
        """Proof of (?x. A x & B x) --> (?x. A x) & (?x. B x)."""
        thy = basic.BasicTheory()
        Ta = TVar("a")
        A = Var("A", TFun(Ta, hol_bool))
        B = Var("B", TFun(Ta, hol_bool))
        x = Var("x", Ta)
        conjAB = Logic.mk_conj(A(x), B(x))
        exists_conj = Logic.mk_exists(x, conjAB)
        exists_A = Logic.mk_exists(x, A(x))
        exists_B = Logic.mk_exists(x, B(x))
        conj_exists = Logic.mk_conj(exists_A, exists_B)

        prf = Proof(exists_conj)
        prf.add_item("S1", "assume", args = conjAB)
        prf.add_item("S2", "theorem", args = "conjD1")
        prf.add_item("S3", "substitution", args = {"A": A(x), "B": B(x)}, prevs = ["S2"])
        prf.add_item("S4", "implies_elim", prevs = ["S3", "S1"])
        prf.add_item("S5", "theorem", args = "conjD2")
        prf.add_item("S6", "substitution", args = {"A": A(x), "B": B(x)}, prevs = ["S5"])
        prf.add_item("S7", "implies_elim", prevs = ["S6", "S1"])
        prf.add_item("S8", "theorem", args = "exI")
        prf.add_item("S9", "substitution", args = {"P": A, "a": x}, prevs = ["S8"])
        prf.add_item("S10", "implies_elim", prevs = ["S9", "S4"])
        prf.add_item("S11", "substitution", args = {"P": B, "a": x}, prevs = ["S8"])
        prf.add_item("S12", "implies_elim", prevs = ["S11", "S7"])
        prf.add_item("S13", "implies_intr", args = conjAB, prevs = ["S10"])
        prf.add_item("S14", "implies_intr", args = conjAB, prevs = ["S12"])
        prf.add_item("S15", "forall_intr", args = x, prevs = ["S13"])
        prf.add_item("S16", "forall_intr", args = x, prevs = ["S14"])
        prf.add_item("S17", "theorem", args = "exE")
        prf.add_item("S18", "substitution", args = {"P": Term.mk_abs(x, conjAB), "C": exists_A}, prevs = ["S17"])
        prf.add_item("S19", "beta_norm", prevs = ["S18"])
        prf.add_item("S20", "implies_elim", prevs = ["S19", "A1"])
        prf.add_item("S21", "implies_elim", prevs = ["S20", "S15"])
        prf.add_item("S22", "substitution", args = {"P": Term.mk_abs(x, conjAB), "C": exists_B}, prevs = ["S17"])
        prf.add_item("S23", "beta_norm", prevs = ["S22"])
        prf.add_item("S24", "implies_elim", prevs = ["S23", "A1"])
        prf.add_item("S25", "implies_elim", prevs = ["S24", "S16"])
        prf.add_item("S26", "theorem", args = "conjI")
        prf.add_item("S27", "substitution", args = {"A": exists_A, "B": exists_B}, prevs = ["S26"])
        prf.add_item("S28", "implies_elim", prevs = ["S27", "S21"])
        prf.add_item("S29", "implies_elim", prevs = ["S28", "S25"])
        prf.add_item("S30", "implies_intr", args = exists_conj, prevs = ["S29"])
        th = Thm.mk_implies(exists_conj, conj_exists)
        self.assertEqual(thy.check_proof(prf), th)

    def testExistsConjMacro(self):
        thy = basic.BasicTheory()
        Ta = TVar("a")
        A = Var("A", TFun(Ta, hol_bool))
        B = Var("B", TFun(Ta, hol_bool))
        x = Var("x", Ta)
        conjAB = Logic.mk_conj(A(x), B(x))
        exists_conj = Logic.mk_exists(x, conjAB)
        exists_A = Logic.mk_exists(x, A(x))
        exists_B = Logic.mk_exists(x, B(x))
        conj_exists = Logic.mk_conj(exists_A, exists_B)

        prf = Proof(exists_conj)
        prf.add_item("S1", "assume", args = conjAB)
        prf.add_item("S2", "apply_theorem", args = "conjD1", prevs = ["S1"])
        prf.add_item("S3", "apply_theorem", args = "conjD2", prevs = ["S1"])
        prf.add_item("S4", "apply_theorem", args = "exI", prevs = ["S2"])
        prf.add_item("S5", "apply_theorem", args = "exI", prevs = ["S3"])
        prf.add_item("S6", "apply_theorem", args = "conjI", prevs = ["S4", "S5"])
        prf.add_item("S7", "implies_intr", args = conjAB, prevs = ["S6"])
        prf.add_item("S8", "forall_intr", args = x, prevs = ["S7"])
        prf.add_item("S9", "apply_theorem", args = "exE", prevs = ["A1", "S8"])
        prf.add_item("S10", "implies_intr", args = exists_conj, prevs = ["S9"])
        th = Thm.mk_implies(exists_conj, conj_exists)
        self.assertEqual(thy.check_proof(prf), th)

    def testAddZeroRight(self):
        """Proof of n + 0 = n by induction."""
        thy = basic.BasicTheory()
        n = Var("n", Nat.nat)
        eq = Term.mk_equals
        prf = Proof()
        prf.add_item("S1", "theorem", args = "nat.induct")
        prf.add_item("S2", "substitution", args = {"P": Term.mk_abs(n, eq(Nat.plus(n,Nat.zero),n))}, prevs = ["S1"])
        prf.add_item("S3", "beta_norm", prevs = ["S2"])
        prf.add_item("S4", "theorem", args = "nat.add_0")
        prf.add_item("S5", "substitution", args = {"n": Nat.zero}, prevs = ["S4"])
        prf.add_item("S6", "implies_elim", prevs = ["S3", "S5"])
        prf.add_item("S7", "assume", args = eq(Nat.plus(n,Nat.zero), n))
        prf.add_item("S8", "theorem", args = "nat.add_Suc")
        prf.add_item("S9", "substitution", args = {"m": n, "n": Nat.zero}, prevs = ["S8"])
        prf.add_item("S10", "arg_combination", args = Nat.Suc, prevs = ["S7"])
        prf.add_item("S11", "transitive", prevs = ["S9", "S10"])
        prf.add_item("S12", "implies_intr", args = eq(Nat.plus(n,Nat.zero), n), prevs = ["S11"])
        prf.add_item("S13", "forall_intr", args = n, prevs = ["S12"])
        prf.add_item("S14", "implies_elim", prevs = ["S6", "S13"])
        th = Thm.mk_equals(Nat.plus(n, Nat.zero), n)
        self.assertEqual(thy.check_proof(prf), th)

    def testMultZeroRight(self):
        """Proof of n * 0 = 0 by induction."""
        thy = basic.BasicTheory()
        n = Var("n", Nat.nat)
        eq = Term.mk_equals
        prf = Proof()
        prf.add_item("S1", "theorem", args = "nat.induct")
        prf.add_item("S2", "substitution", args = {"P": Term.mk_abs(n, eq(Nat.times(n,Nat.zero),Nat.zero))}, prevs = ["S1"])
        prf.add_item("S3", "beta_norm", prevs = ["S2"])
        prf.add_item("S4", "theorem", args = "nat.mult_0")
        prf.add_item("S5", "substitution", args = {"n": Nat.zero}, prevs = ["S4"])
        prf.add_item("S6", "implies_elim", prevs = ["S3", "S5"])
        prf.add_item("S7", "assume", args = eq(Nat.times(n,Nat.zero), Nat.zero))
        prf.add_item("S8", "theorem", args = "nat.mult_Suc")
        prf.add_item("S9", "substitution", args = {"m": n, "n": Nat.zero}, prevs = ["S8"])
        prf.add_item("S10", "theorem", args = "nat.add_0")
        prf.add_item("S11", "substitution", args = {"n": Nat.times(n,Nat.zero)}, prevs = ["S10"])
        prf.add_item("S12", "transitive", prevs = ["S9", "S11"])
        prf.add_item("S13", "transitive", prevs = ["S12", "S7"])
        prf.add_item("S14", "implies_intr", args = eq(Nat.times(n,Nat.zero), Nat.zero), prevs = ["S13"])
        prf.add_item("S15", "forall_intr", args = n, prevs = ["S14"])
        prf.add_item("S16", "implies_elim", prevs = ["S6", "S15"])
        th = Thm.mk_equals(Nat.times(n, Nat.zero), Nat.zero)
        self.assertEqual(thy.check_proof(prf), th)

if __name__ == "__main__":
    unittest.main()
