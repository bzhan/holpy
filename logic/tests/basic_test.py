# Author: Bohua Zhan

import unittest

from kernel.type import TVar, TFun, hol_bool
from kernel.term import Var, Term
from kernel.thm import Thm
from kernel.proof import Proof
from kernel.report import ProofReport
from kernel.theory import Theory, TheoryException
from logic import basic
from logic import logic
from logic import nat
from logic import logic_macro
from syntax import printer

Ta = TVar("a")
x = Var("x", Ta)
y = Var("y", Ta)
f = Var("f", TFun(Ta,Ta))
g = Var("g", TFun(Ta,Ta))

class BasicTest(unittest.TestCase):
    def testLoadTheory(self):
        thy1 = basic.loadTheory('logic_base')
        thy2 = basic.loadTheory('logic')

        self.assertEqual(thy1.get_theorem('conjI'), thy2.get_theorem('conjI'))
        self.assertRaises(TheoryException, thy1.get_theorem, 'conj_comm')
        self.assertIsInstance(thy2.get_theorem('conj_comm'), Thm)

    def testLoadTheoryWithLimit(self):
        thy = basic.loadTheory('logic_base')
        thy1 = basic.loadTheory('logic_base', limit=('thm', 'conjD1'))
        self.assertEqual(thy.get_theorem('conjI'), thy1.get_theorem('conjI'))
        self.assertRaises(TheoryException, thy1.get_theorem, 'conjD1')
        self.assertRaises(AssertionError, basic.loadTheory, 'logic_base', limit=('thm', 'conj'))

    def testArgCombination(self):
        thy = basic.loadTheory('logic_base')
        macro = logic_macro.arg_combination_macro()

        x_eq_y = Term.mk_equals(x, y)
        fx_eq_fy = Term.mk_equals(f(x), f(y))
        th = Thm.assume(x_eq_y)
        res = Thm([x_eq_y], fx_eq_fy)
        self.assertEqual(macro(thy, f, [th]), res)

        prf = Proof(x_eq_y)
        prf.add_item(1, "arg_combination", args=f, prevs=[0])
        rpt = ProofReport()
        self.assertEqual(thy.check_proof(prf, rpt), res)
        self.assertEqual(rpt.macros_expand, {"arg_combination"})
        self.assertEqual(rpt.prim_steps, 3)

    def testFunCombination(self):
        thy = basic.loadTheory('logic_base')
        macro = logic_macro.fun_combination_macro()

        f_eq_g = Term.mk_equals(f, g)
        fx_eq_gx = Term.mk_equals(f(x), g(x))
        th = Thm.assume(f_eq_g)
        res = Thm([f_eq_g], fx_eq_gx)
        self.assertEqual(macro(thy, x, [th]), res)

        prf = Proof(f_eq_g)
        prf.add_item(1, "fun_combination", args=x, prevs=[0])
        rpt = ProofReport()
        self.assertEqual(thy.check_proof(prf, rpt), res)
        self.assertEqual(rpt.macros_expand, {"fun_combination"})
        self.assertEqual(rpt.prim_steps, 3)

    def testCombination(self):
        """Test arg and fun combination together using proofs."""
        thy = basic.loadTheory('logic_base')

        prf = Proof(Term.mk_equals(f,g), Term.mk_equals(x,y))
        prf.add_item(2, "arg_combination", args=f, prevs=[1])
        prf.add_item(3, "fun_combination", args=y, prevs=[0])
        prf.add_item(4, "transitive", prevs=[2, 3])
        prf.add_item(5, "implies_intr", args=Term.mk_equals(x,y), prevs=[4])
        prf.add_item(6, "implies_intr", args=Term.mk_equals(f,g), prevs=[5])
        th = Thm.mk_implies(Term.mk_equals(f,g), Term.mk_equals(x,y), Term.mk_equals(f(x),g(y)))
        self.assertEqual(thy.check_proof(prf), th)

    def testBetaNorm(self):
        thy = basic.loadTheory('logic_base')

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
        thy = basic.loadTheory('logic_base')
        A = Var("A", hol_bool)
        B = Var("B", hol_bool)

        th = Thm([logic.mk_conj(A, B)], A)

        prf = Proof(logic.mk_conj(A, B))
        prf.add_item(1, "apply_theorem", args="conjD1", prevs=[0])
        rpt = ProofReport()
        self.assertEqual(thy.check_proof(prf, rpt), th)
        self.assertEqual(rpt.prim_steps, 8)

        # Reset data for the next check
        prf = Proof(logic.mk_conj(A, B))
        prf.add_item(1, "apply_theorem", args="conjD1", prevs=[0])
        rpt = ProofReport()
        self.assertEqual(thy.check_proof(prf, rpt, check_level=1), th)
        self.assertEqual(rpt.prim_steps, 1)
        self.assertEqual(rpt.macro_steps, 1)

    def testRewriteGoal(self):
        thy = basic.loadTheory('nat')

        n = Var("n", nat.natT)
        eq = Term.mk_equals
        zero = nat.zero
        plus = nat.mk_plus
        prf = Proof()
        prf.add_item(0, "reflexive", args=zero)
        prf.add_item(1, "rewrite_goal", args=("plus_def_1", eq(plus(zero,zero),zero)), prevs=[0])

        th = Thm([], eq(plus(zero,zero),zero))
        rpt = ProofReport()
        self.assertEqual(thy.check_proof(prf, rpt), th)
        self.assertEqual(rpt.prim_steps, 9)

        rpt2 = ProofReport()
        self.assertEqual(thy.check_proof(prf, rpt2, check_level=1), th)
        self.assertEqual(rpt2.prim_steps, 1)
        self.assertEqual(rpt2.macro_steps, 1)

    def testConjComm(self):
        """Proof of commutativity of conjunction."""
        thy = basic.loadTheory('logic_base')
        A = Var("A", hol_bool)
        B = Var("B", hol_bool)

        prf = Proof(logic.mk_conj(A, B))
        prf.add_item(1, "theorem", args="conjD1")
        prf.add_item(2, "implies_elim", prevs=[1, 0])
        prf.add_item(3, "theorem", args="conjD2")
        prf.add_item(4, "implies_elim", prevs=[3, 0])
        prf.add_item(5, "theorem", args="conjI")
        prf.add_item(6, "substitution", args={"A": B, "B": A}, prevs=[5])
        prf.add_item(7, "implies_elim", prevs=[6, 4])
        prf.add_item(8, "implies_elim", prevs=[7, 2])
        prf.add_item(9, "implies_intr", args=logic.mk_conj(A, B), prevs=[8])
        th = Thm.mk_implies(logic.mk_conj(A, B), logic.mk_conj(B, A))
        self.assertEqual(thy.check_proof(prf), th)

    def testConjCommWithMacro(self):
        """Proof of commutativity of conjunction, with macros."""
        thy = basic.loadTheory('logic_base')
        A = Var("A", hol_bool)
        B = Var("B", hol_bool)

        prf = Proof(logic.mk_conj(A, B))
        prf.add_item(1, "apply_theorem", args="conjD1", prevs=[0])
        prf.add_item(2, "apply_theorem", args="conjD2", prevs=[0])
        prf.add_item(3, "apply_theorem", args="conjI", prevs=[2, 1])
        prf.add_item(4, "implies_intr", args=logic.mk_conj(A, B), prevs=[3])
        th = Thm.mk_implies(logic.mk_conj(A, B), logic.mk_conj(B, A))
        self.assertEqual(thy.check_proof(prf), th)

    def testDisjComm(self):
        """Proof of commutativity of disjunction."""
        thy = basic.loadTheory('logic_base')
        A = Var("A", hol_bool)
        B = Var("B", hol_bool)
        disjAB = logic.mk_disj(A, B)
        disjBA = logic.mk_disj(B, A)

        prf = Proof(disjAB)
        prf.add_item(1, "theorem", args="disjI2")
        prf.add_item(2, "substitution", args={"A": B, "B": A}, prevs=[1])
        prf.add_item(3, "theorem", args="disjI1")
        prf.add_item(4, "substitution", args={"A": B, "B": A}, prevs=[3])
        prf.add_item(5, "theorem", args="disjE")
        prf.add_item(6, "substitution", args={"C": disjBA}, prevs=[5])
        prf.add_item(7, "implies_elim", prevs=[6, 0])
        prf.add_item(8, "implies_elim", prevs=[7, 2])
        prf.add_item(9, "implies_elim", prevs=[8, 4])
        prf.add_item(10, "implies_intr", args=disjAB, prevs=[9])
        th = Thm.mk_implies(disjAB, disjBA)
        self.assertEqual(thy.check_proof(prf), th)

    def testDisjCommWithMacro(self):
        """Proof of commutativity of disjunction, with macros."""
        thy = basic.loadTheory('logic_base')
        A = Var("A", hol_bool)
        B = Var("B", hol_bool)
        disjAB = logic.mk_disj(A, B)
        disjBA = logic.mk_disj(B, A)

        prf = Proof(disjAB)
        prf.add_item(1, "assume", args=A)
        prf.add_item(2, "apply_theorem_for", args=("disjI2", {}, {"A": B, "B": A}), prevs=[1])
        prf.add_item(3, "implies_intr", args=A, prevs=[2])
        prf.add_item(4, "assume", args=B)
        prf.add_item(5, "apply_theorem_for", args=("disjI1", {}, {"A": B, "B": A}), prevs=[4])
        prf.add_item(6, "implies_intr", args=B, prevs=[5])
        prf.add_item(7, "apply_theorem", args="disjE", prevs=[0, 3, 6])
        prf.add_item(8, "implies_intr", args=disjAB, prevs=[7])
        th = Thm.mk_implies(disjAB, disjBA)
        self.assertEqual(thy.check_proof(prf), th)

    def testAllConj(self):
        """Proof of (!x. A x & B x) --> (!x. A x) & (!x. B x)."""
        thy = basic.loadTheory('logic_base')
        Ta = TVar("a")
        A = Var("A", TFun(Ta, hol_bool))
        B = Var("B", TFun(Ta, hol_bool))
        x = Var("x", Ta)
        all_conj = Term.mk_all(x, logic.mk_conj(A(x), B(x)))
        all_A = Term.mk_all(x, A(x))
        all_B = Term.mk_all(x, B(x))
        conj_all = logic.mk_conj(all_A, all_B)

        prf = Proof(all_conj)
        prf.add_item(1, "forall_elim", args=x, prevs=[0])
        prf.add_item(2, "theorem", args="conjD1")
        prf.add_item(3, "substitution", args={"A": A(x), "B": B(x)}, prevs=[2])
        prf.add_item(4, "implies_elim", prevs=[3, 1])
        prf.add_item(5, "forall_intr", args=x, prevs=[4])
        prf.add_item(6, "theorem", args="conjD2")
        prf.add_item(7, "substitution", args={"A": A(x), "B": B(x)}, prevs=[6])
        prf.add_item(8, "implies_elim", prevs=[7, 1])
        prf.add_item(9, "forall_intr", args=x, prevs=[8])
        prf.add_item(10, "theorem", args="conjI")
        prf.add_item(11, "substitution", args={"A": all_A, "B": all_B}, prevs=[10])
        prf.add_item(12, "implies_elim", prevs=[11, 5])
        prf.add_item(13, "implies_elim", prevs=[12, 9])
        prf.add_item(14, "implies_intr", args=all_conj, prevs=[13])
        th = Thm.mk_implies(all_conj, conj_all)
        self.assertEqual(thy.check_proof(prf), th)

    def testAllConjWithMacro(self):
        """Proof of (!x. A x & B x) --> (!x. A x) & (!x. B x), using macros."""
        thy = basic.loadTheory('logic_base')
        Ta = TVar("a")
        A = Var("A", TFun(Ta, hol_bool))
        B = Var("B", TFun(Ta, hol_bool))
        x = Var("x", Ta)
        all_conj = Term.mk_all(x, logic.mk_conj(A(x), B(x)))
        all_A = Term.mk_all(x, A(x))
        all_B = Term.mk_all(x, B(x))
        conj_all = logic.mk_conj(all_A, all_B)

        prf = Proof(all_conj)
        prf.add_item(1, "forall_elim", args=x, prevs=[0])
        prf.add_item(2, "apply_theorem", args="conjD1", prevs=[1])
        prf.add_item(3, "forall_intr", args=x, prevs=[2])
        prf.add_item(4, "apply_theorem", args="conjD2", prevs=[1])
        prf.add_item(5, "forall_intr", args=x, prevs=[4])
        prf.add_item(6, "apply_theorem", args="conjI", prevs=[3, 5])
        prf.add_item(7, "implies_intr", args=all_conj, prevs=[6])
        th = Thm.mk_implies(all_conj, conj_all)
        self.assertEqual(thy.check_proof(prf), th)

    def testDoubleNeg(self):
        """Proof of A --> ~~A."""
        thy = basic.loadTheory('logic_base')
        A = Var("A", hol_bool)
        neg = logic.neg

        prf = Proof(A)
        prf.add_item(1, "assume", args=neg(A))
        prf.add_item(2, "theorem", args="negE")
        prf.add_item(3, "implies_elim", prevs=[2, 1])
        prf.add_item(4, "implies_elim", prevs=[3, 0])
        prf.add_item(5, "implies_intr", args=neg(A), prevs=[4])
        prf.add_item(6, "theorem", args="negI")
        prf.add_item(7, "substitution", args={"A": neg(A)}, prevs=[6])
        prf.add_item(8, "implies_elim", prevs=[7, 5])
        prf.add_item(9, "implies_intr", args=A, prevs=[8])
        th = Thm.mk_implies(A, neg(neg(A)))
        self.assertEqual(thy.check_proof(prf), th)

    def testDoubleNegInv(self):
        """Proof of ~~A --> A, requires classical axiom."""
        thy = basic.loadTheory('logic_base')
        A = Var("A", hol_bool)
        neg = logic.neg

        prf = Proof(neg(neg(A)))
        prf.add_item(1, "theorem", args="classical")
        prf.add_item(2, "assume", args=A)
        prf.add_item(3, "assume", args=neg(A))
        prf.add_item(4, "theorem", args="negE")
        prf.add_item(5, "substitution", args={"A": neg(A)}, prevs=[4])
        prf.add_item(6, "implies_elim", prevs=[5, 0])
        prf.add_item(7, "implies_elim", prevs=[6, 3])
        prf.add_item(8, "theorem", args="falseE")
        prf.add_item(9, "implies_elim", prevs=[8, 7])
        prf.add_item(10, "implies_intr", args=A, prevs=[2])
        prf.add_item(11, "implies_intr", args=neg(A), prevs=[9])
        prf.add_item(12, "theorem", args="disjE")
        prf.add_item(13, "substitution", args={"B": neg(A), "C": A}, prevs=[12])
        prf.add_item(14, "implies_elim", prevs=[13, 1])
        prf.add_item(15, "implies_elim", prevs=[14, 10])
        prf.add_item(16, "implies_elim", prevs=[15, 11])
        prf.add_item(17, "implies_intr", args=neg(neg(A)), prevs=[16])
        th = Thm.mk_implies(neg(neg(A)), A)
        self.assertEqual(thy.check_proof(prf), th)

    def testDoubleNegInvWithMacro(self):
        """Proof of ~~A --> A, using macros."""
        thy = basic.loadTheory('logic_base')
        A = Var("A", hol_bool)
        neg = logic.neg

        prf = Proof(neg(neg(A)))
        prf.add_item(1, "theorem", args="classical")
        prf.add_item(2, "assume", args=A)
        prf.add_item(3, "assume", args=neg(A))
        prf.add_item(4, "apply_theorem", args="negE", prevs=[0, 3])
        prf.add_item(5, "apply_theorem", args="falseE", prevs=[4])
        prf.add_item(6, "implies_intr", args=A, prevs=[2])
        prf.add_item(7, "implies_intr", args=neg(A), prevs=[5])
        prf.add_item(8, "apply_theorem", args="disjE", prevs=[1, 6, 7])
        prf.add_item(9, "implies_intr", args=neg(neg(A)), prevs=[8])
        th = Thm.mk_implies(neg(neg(A)), A)
        self.assertEqual(thy.check_proof(prf), th)

    def testTrueAbsorb(self):
        """Proof of A --> true & A."""
        thy = basic.loadTheory('logic_base')
        A = Var("A", hol_bool)

        prf = Proof(A)
        prf.add_item(1, "theorem", args="trueI")
        prf.add_item(2, "theorem", args="conjI")
        prf.add_item(3, "substitution", args={"A": logic.true, "B": A}, prevs=[2])
        prf.add_item(4, "implies_elim", prevs=[3, 1])
        prf.add_item(5, "implies_elim", prevs=[4, 0])
        prf.add_item(6, "implies_intr", args=A, prevs=[5])
        th = Thm.mk_implies(A, logic.mk_conj(logic.true, A))
        self.assertEqual(thy.check_proof(prf), th)
        
    def testExistsConj(self):
        """Proof of (?x. A x & B x) --> (?x. A x) & (?x. B x)."""
        thy = basic.loadTheory('logic_base')
        Ta = TVar("a")
        A = Var("A", TFun(Ta, hol_bool))
        B = Var("B", TFun(Ta, hol_bool))
        x = Var("x", Ta)
        conjAB = logic.mk_conj(A(x), B(x))
        exists_conj = logic.mk_exists(x, conjAB)
        exists_A = logic.mk_exists(x, A(x))
        exists_B = logic.mk_exists(x, B(x))
        conj_exists = logic.mk_conj(exists_A, exists_B)

        prf = Proof(exists_conj)
        prf.add_item(1, "assume", args=conjAB)
        prf.add_item(2, "theorem", args="conjD1")
        prf.add_item(3, "substitution", args={"A": A(x), "B": B(x)}, prevs=[2])
        prf.add_item(4, "implies_elim", prevs=[3, 1])
        prf.add_item(5, "theorem", args="conjD2")
        prf.add_item(6, "substitution", args={"A": A(x), "B": B(x)}, prevs=[5])
        prf.add_item(7, "implies_elim", prevs=[6, 1])
        prf.add_item(8, "theorem", args="exI")
        prf.add_item(9, "substitution", args={"P": A, "a": x}, prevs=[8])
        prf.add_item(10, "implies_elim", prevs=[9, 4])
        prf.add_item(11, "substitution", args={"P": B, "a": x}, prevs=[8])
        prf.add_item(12, "implies_elim", prevs=[11, 7])
        prf.add_item(13, "implies_intr", args=conjAB, prevs=[10])
        prf.add_item(14, "implies_intr", args=conjAB, prevs=[12])
        prf.add_item(15, "forall_intr", args=x, prevs=[13])
        prf.add_item(16, "forall_intr", args=x, prevs=[14])
        prf.add_item(17, "theorem", args="exE")
        prf.add_item(18, "substitution", args={"P": Term.mk_abs(x, conjAB), "C": exists_A}, prevs=[17])
        prf.add_item(19, "beta_norm", prevs=[18])
        prf.add_item(20, "implies_elim", prevs=[19, 0])
        prf.add_item(21, "implies_elim", prevs=[20, 15])
        prf.add_item(22, "substitution", args={"P": Term.mk_abs(x, conjAB), "C": exists_B}, prevs=[17])
        prf.add_item(23, "beta_norm", prevs=[22])
        prf.add_item(24, "implies_elim", prevs=[23, 0])
        prf.add_item(25, "implies_elim", prevs=[24, 16])
        prf.add_item(26, "theorem", args="conjI")
        prf.add_item(27, "substitution", args={"A": exists_A, "B": exists_B}, prevs=[26])
        prf.add_item(28, "implies_elim", prevs=[27, 21])
        prf.add_item(29, "implies_elim", prevs=[28, 25])
        prf.add_item(30, "implies_intr", args=exists_conj, prevs=[29])
        th = Thm.mk_implies(exists_conj, conj_exists)
        self.assertEqual(thy.check_proof(prf), th)

    def testExistsConjWithMacro(self):
        """Proof of (?x. A x & B x) --> (?x. A x) & (?x. B x), using macros."""
        thy = basic.loadTheory('logic_base')
        Ta = TVar("a")
        A = Var("A", TFun(Ta, hol_bool))
        B = Var("B", TFun(Ta, hol_bool))
        x = Var("x", Ta)
        conjAB = logic.mk_conj(A(x), B(x))
        exists_conj = logic.mk_exists(x, conjAB)
        exists_A = logic.mk_exists(x, A(x))
        exists_B = logic.mk_exists(x, B(x))
        conj_exists = logic.mk_conj(exists_A, exists_B)

        prf = Proof(exists_conj)
        prf.add_item(1, "assume", args=conjAB)
        prf.add_item(2, "apply_theorem", args="conjD1", prevs=[1])
        prf.add_item(3, "apply_theorem", args="conjD2", prevs=[1])
        prf.add_item(4, "apply_theorem", args="exI", prevs=[2])
        prf.add_item(5, "apply_theorem", args="exI", prevs=[3])
        prf.add_item(6, "apply_theorem", args="conjI", prevs=[4, 5])
        prf.add_item(7, "implies_intr", args=conjAB, prevs=[6])
        prf.add_item(8, "forall_intr", args=x, prevs=[7])
        prf.add_item(9, "apply_theorem", args="exE", prevs=[0, 8])
        prf.add_item(10, "implies_intr", args=exists_conj, prevs=[9])
        th = Thm.mk_implies(exists_conj, conj_exists)
        self.assertEqual(thy.check_proof(prf), th)

    def testAddZeroRight(self):
        """Proof of n + 0 = n by induction."""
        thy = basic.loadTheory('nat')
        n = Var("n", nat.natT)
        eq = Term.mk_equals
        prf = Proof()
        prf.add_item(0, "theorem", args="nat_induct")
        prf.add_item(1, "substitution", args={"P": Term.mk_abs(n, eq(nat.plus(n,nat.zero),n)), "x": n}, prevs=[0])
        prf.add_item(2, "beta_norm", prevs=[1])
        prf.add_item(3, "theorem", args="plus_def_1")
        prf.add_item(4, "substitution", args={"n": nat.zero}, prevs=[3])
        prf.add_item(5, "implies_elim", prevs=[2, 4])
        prf.add_item(6, "assume", args=eq(nat.plus(n,nat.zero), n))
        prf.add_item(7, "theorem", args="plus_def_2")
        prf.add_item(8, "substitution", args={"m": n, "n": nat.zero}, prevs=[7])
        prf.add_item(9, "arg_combination", args=nat.Suc, prevs=[6])
        prf.add_item(10, "transitive", prevs=[8, 9])
        prf.add_item(11, "implies_intr", args=eq(nat.plus(n,nat.zero), n), prevs=[10])
        prf.add_item(12, "forall_intr", args=n, prevs=[11])
        prf.add_item(13, "implies_elim", prevs=[5, 12])
        th = Thm.mk_equals(nat.plus(n, nat.zero), n)
        self.assertEqual(thy.check_proof(prf), th)

    def testAddZeroRightWithMacro(self):
        """Proof of n + 0 = n by induction, using macros."""
        thy = basic.loadTheory('nat')
        n = Var("n", nat.natT)
        eq = Term.mk_equals
        plus = nat.plus
        zero = nat.zero
        S = nat.Suc
        prf = Proof()
        prf.add_item(0, "reflexive", args=zero)
        prf.add_item(1, "rewrite_goal", args=("plus_def_1", eq(plus(zero,zero),zero)), prevs=[0])
        prf.add_item(2, "assume", args=eq(plus(n,zero),n))
        prf.add_item(3, "arg_combination", args=S, prevs=[2])
        prf.add_item(4, "rewrite_goal", args=("plus_def_2", eq(plus(S(n),zero),S(n))), prevs=[3])
        prf.add_item(5, "implies_intr", args=eq(plus(n,zero),n), prevs=[4])
        prf.add_item(6, "forall_intr", args=n, prevs=[5])
        prf.add_item(7, "apply_theorem_for", args=("nat_induct", {}, {"P": Term.mk_abs(n, eq(plus(n,zero),n)), "x": n}), prevs=[1, 6])
        th = Thm.mk_equals(plus(n, zero), n)
        self.assertEqual(thy.check_proof(prf), th)

    def testMultZeroRight(self):
        """Proof of n * 0 = 0 by induction."""
        thy = basic.loadTheory('nat')
        n = Var("n", nat.natT)
        eq = Term.mk_equals
        prf = Proof()
        prf.add_item(0, "theorem", args="nat_induct")
        prf.add_item(1, "substitution", args={"P": Term.mk_abs(n, eq(nat.times(n,nat.zero),nat.zero)), "x": n}, prevs=[0])
        prf.add_item(2, "beta_norm", prevs=[1])
        prf.add_item(3, "theorem", args="times_def_1")
        prf.add_item(4, "substitution", args={"n": nat.zero}, prevs=[3])
        prf.add_item(5, "implies_elim", prevs=[2, 4])
        prf.add_item(6, "assume", args=eq(nat.times(n,nat.zero), nat.zero))
        prf.add_item(7, "theorem", args="times_def_2")
        prf.add_item(8, "substitution", args={"m": n, "n": nat.zero}, prevs=[7])
        prf.add_item(9, "theorem", args="plus_def_1")
        prf.add_item(10, "substitution", args={"n": nat.times(n,nat.zero)}, prevs=[9])
        prf.add_item(11, "transitive", prevs=[8, 10])
        prf.add_item(12, "transitive", prevs=[11, 6])
        prf.add_item(13, "implies_intr", args=eq(nat.times(n,nat.zero), nat.zero), prevs=[12])
        prf.add_item(14, "forall_intr", args=n, prevs=[13])
        prf.add_item(15, "implies_elim", prevs=[5, 14])
        th = Thm.mk_equals(nat.times(n, nat.zero), nat.zero)
        self.assertEqual(thy.check_proof(prf), th)

    def testMultZeroRightWithMacro(self):
        """Proof of n * 0 = 0 by induction, using macros."""
        thy = basic.loadTheory('nat')
        n = Var("n", nat.natT)
        eq = Term.mk_equals
        zero = nat.zero
        plus = nat.mk_plus
        times = nat.mk_times
        S = nat.Suc
        prf = Proof()
        prf.add_item(0, "reflexive", args=zero)
        prf.add_item(1, "rewrite_goal", args=("times_def_1", eq(times(zero,zero),zero)), prevs=[0])
        prf.add_item(2, "assume", args=eq(times(n,zero),zero))
        prf.add_item(3, "reflexive", args=times(n,zero))
        prf.add_item(4, "rewrite_goal", args=("plus_def_1", eq(plus(zero,times(n,zero)),times(n,zero))), prevs=[3])
        prf.add_item(5, "transitive", prevs=[4, 2])
        prf.add_item(6, "rewrite_goal", args=("times_def_2", eq(times(S(n),zero),zero)), prevs=[5])
        prf.add_item(7, "implies_intr", args=eq(times(n,zero),zero), prevs=[6])
        prf.add_item(8, "forall_intr", args=n, prevs=[7])
        prf.add_item(9, "apply_theorem_for", args=("nat_induct", {}, {"P": Term.mk_abs(n, eq(times(n,zero),zero)), "x": n}), prevs=[1, 8])
        th = Thm.mk_equals(times(n, zero), zero)
        self.assertEqual(thy.check_proof(prf), th)


if __name__ == "__main__":
    unittest.main()
