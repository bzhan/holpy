# Author: Bohua Zhan

import unittest

from kernel.type import TVar, TFun, hol_bool
from kernel.term import Var, Term
from kernel.thm import Thm
from kernel.proof import Proof
from kernel.theory import Theory
import logic.basic as basic
from logic.basic import Logic

Ta = TVar("a")
x = Var("x", Ta)
y = Var("y", Ta)
f = Var("f", TFun(Ta,Ta))
g = Var("g", TFun(Ta,Ta))

class BasicTest(unittest.TestCase):
    def testArgCombination(self):
        th = Thm.mk_equals(x,y)
        res = Thm.mk_equals(f(x),f(y))
        self.assertEqual(basic.arg_combination_macro().eval(th, f), res)
        prf = basic.arg_combination_macro().expand(1, [(0, "S1")], th, f)
        
        thy = Theory.EmptyTheory()
        self.assertEqual(prf.get_num_item(), 2)
        self.assertEqual(thy.check_proof_incr(1, {(0, "S1"): th}, prf), res)

    def testFunCombination(self):
        th = Thm.mk_equals(f,g)
        res = Thm.mk_equals(f(x),g(x))
        self.assertEqual(basic.fun_combination_macro().eval(th, x), res)
        prf = basic.fun_combination_macro().expand(1, [(0, "S1")], th, x)

        thy = Theory.EmptyTheory()
        self.assertEqual(prf.get_num_item(), 2)
        self.assertEqual(thy.check_proof_incr(1, {(0, "S1"): th}, prf), res)

    def testConjComm(self):
        """Proof of commutativity of conjunction."""
        thy = basic.BasicTheory()
        A = Var("A", hol_bool)
        B = Var("B", hol_bool)
        conjAB = Logic.mk_conj(A, B)
        conjBA = Logic.mk_conj(B, A)

        prf = Proof(conjAB)
        prf.add_item("S1", "theorem", args = "conjD1")
        prf.add_item("S2", "implies_elim", prevs = ["S1", "A1"])
        prf.add_item("S3", "theorem", args = "conjD2")
        prf.add_item("S4", "implies_elim", prevs = ["S3", "A1"])
        prf.add_item("S5", "theorem", args = "conjI")
        prf.add_item("S6", "substitution", args = {"A": B, "B": A}, prevs = ["S5"])
        prf.add_item("S7", "implies_elim", prevs = ["S6", "S4"])
        prf.add_item("S8", "implies_elim", prevs = ["S7", "S2"])
        prf.add_item("S9", "implies_intr", args = conjAB, prevs = ["S8"])
        th = Thm([], Term.mk_implies(conjAB, conjBA))
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
        prf.add_item("S7", "implies_elim", prevs = ["S6", "S2"])
        prf.add_item("S8", "implies_elim", prevs = ["S7", "S4"])
        th = Thm([], Term.mk_implies(disjAB, disjBA))
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
        th = Thm([], Term.mk_implies(all_conj, conj_all))
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
        th = Thm([], Term.mk_implies(A, neg(neg(A))))
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
        prf.add_item("S14", "implies_elim", prevs = ["S13", "S10"])
        prf.add_item("S15", "implies_elim", prevs = ["S14", "S11"])
        prf.add_item("S16", "implies_elim", prevs = ["S15", "S1"])
        prf.add_item("S17", "implies_intr", args = neg(neg(A)), prevs = ["S16"])
        th = Thm([], Term.mk_implies(neg(neg(A)), A))
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
        th = Thm([], Term.mk_implies(A, Logic.mk_conj(Logic.true, A)))
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
        # Unfinished proof
        thy.check_proof(prf)


if __name__ == "__main__":
    unittest.main()
