# Author: Bohua Zhan

import unittest

from kernel.type import TVar, TFun, BoolType, NatType, TyInst
from kernel.term import Var, Term, Not, And, Or, Eq, Implies, Forall, Exists, Lambda, true, Nat, Inst
from kernel.thm import Thm
from kernel.proof import Proof
from kernel.theory import TheoryException
from kernel import theory
from logic import basic
from logic import logic
from data import nat
from data import set


class BasicTest(unittest.TestCase):
    def testLoadTheory(self):
        basic.load_theory('logic_base')
        self.assertIsInstance(theory.get_theorem('conjI'), Thm)
        self.assertRaises(TheoryException, theory.get_theorem, 'conj_comm')

        basic.load_theory('logic')
        self.assertIsInstance(theory.get_theorem('conjI'), Thm)
        self.assertIsInstance(theory.get_theorem('conj_comm'), Thm)

    def testLoadTheoryWithLimit(self):
        basic.load_theory('logic_base', limit=('thm.ax', 'conjD1'))
        self.assertIsInstance(theory.get_theorem('conjI'), Thm)
        self.assertRaises(TheoryException, theory.get_theorem, 'conjD1')

    def testLoadTheoryWithLimitFail(self):
        self.assertRaises(TheoryException, basic.load_theory, 'logic_base', limit=('thm.ax', 'conj'))

    def testConjComm(self):
        """Proof of commutativity of conjunction."""
        basic.load_theory('logic_base')
        A = Var("A", BoolType)
        B = Var("B", BoolType)

        prf = Proof(And(A, B))
        prf.add_item(1, "apply_theorem_for", args=("conjD1", Inst(A=A, B=B)))
        prf.add_item(2, "implies_elim", prevs=[1, 0])
        prf.add_item(3, "apply_theorem_for", args=("conjD2", Inst(A=A, B=B)))
        prf.add_item(4, "implies_elim", prevs=[3, 0])
        prf.add_item(5, "theorem", args="conjI")
        prf.add_item(6, "substitution", args=Inst(A=B, B=A), prevs=[5])
        prf.add_item(7, "implies_elim", prevs=[6, 4])
        prf.add_item(8, "implies_elim", prevs=[7, 2])
        prf.add_item(9, "implies_intr", args=And(A, B), prevs=[8])
        th = Thm(Implies(And(A, B), And(B, A)))
        self.assertEqual(theory.check_proof(prf), th)

    def testConjCommWithMacro(self):
        """Proof of commutativity of conjunction, with macros."""
        basic.load_theory('logic_base')
        A = Var("A", BoolType)
        B = Var("B", BoolType)

        prf = Proof(And(A, B))
        prf.add_item(1, "apply_theorem", args="conjD1", prevs=[0])
        prf.add_item(2, "apply_theorem", args="conjD2", prevs=[0])
        prf.add_item(3, "apply_theorem", args="conjI", prevs=[2, 1])
        prf.add_item(4, "implies_intr", args=And(A, B), prevs=[3])
        th = Thm(Implies(And(A, B), And(B, A)))
        self.assertEqual(theory.check_proof(prf), th)

    def testDisjComm(self):
        """Proof of commutativity of disjunction."""
        basic.load_theory('logic_base')
        A = Var("A", BoolType)
        B = Var("B", BoolType)

        prf = Proof(Or(A, B))
        prf.add_item(1, "theorem", args="disjI2")
        prf.add_item(2, "substitution", args=Inst(A=B, B=A), prevs=[1])
        prf.add_item(3, "theorem", args="disjI1")
        prf.add_item(4, "substitution", args=Inst(A=B, B=A), prevs=[3])
        prf.add_item(5, "theorem", args="disjE")
        prf.add_item(6, "substitution", args=Inst(A=A, B=B, C=Or(B, A)), prevs=[5])
        prf.add_item(7, "implies_elim", prevs=[6, 0])
        prf.add_item(8, "implies_elim", prevs=[7, 2])
        prf.add_item(9, "implies_elim", prevs=[8, 4])
        prf.add_item(10, "implies_intr", args=Or(A, B), prevs=[9])
        th = Thm(Implies(Or(A, B), Or(B, A)))
        self.assertEqual(theory.check_proof(prf), th)

    def testDisjCommWithMacro(self):
        """Proof of commutativity of disjunction, with macros."""
        basic.load_theory('logic_base')
        A = Var("A", BoolType)
        B = Var("B", BoolType)

        prf = Proof(Or(A, B))
        prf.add_item(1, "assume", args=A)
        prf.add_item(2, "apply_theorem_for", args=("disjI2", Inst(A=B, B=A)), prevs=[1])
        prf.add_item(3, "implies_intr", args=A, prevs=[2])
        prf.add_item(4, "assume", args=B)
        prf.add_item(5, "apply_theorem_for", args=("disjI1", Inst(A=B, B=A)), prevs=[4])
        prf.add_item(6, "implies_intr", args=B, prevs=[5])
        prf.add_item(7, "apply_theorem", args="disjE", prevs=[0, 3, 6])
        prf.add_item(8, "implies_intr", args=Or(A, B), prevs=[7])
        th = Thm(Implies(Or(A, B), Or(B, A)))
        self.assertEqual(theory.check_proof(prf), th)

    def testAllConj(self):
        """Proof of (!x. A x & B x) --> (!x. A x) & (!x. B x)."""
        basic.load_theory('logic_base')
        Ta = TVar("a")
        A = Var("A", TFun(Ta, BoolType))
        B = Var("B", TFun(Ta, BoolType))
        x = Var("x", Ta)
        all_conj = Forall(x, And(A(x), B(x)))
        conj_all = And(Forall(x, A(x)), Forall(x, B(x)))

        prf = Proof(all_conj)
        prf.add_item(1, "forall_elim", args=x, prevs=[0])
        prf.add_item(2, "theorem", args="conjD1")
        prf.add_item(3, "substitution", args=Inst(A=A(x), B=B(x)), prevs=[2])
        prf.add_item(4, "implies_elim", prevs=[3, 1])
        prf.add_item(5, "forall_intr", args=x, prevs=[4])
        prf.add_item(6, "theorem", args="conjD2")
        prf.add_item(7, "substitution", args=Inst(A=A(x), B=B(x)), prevs=[6])
        prf.add_item(8, "implies_elim", prevs=[7, 1])
        prf.add_item(9, "forall_intr", args=x, prevs=[8])
        prf.add_item(10, "theorem", args="conjI")
        prf.add_item(11, "substitution", args=Inst(A=Forall(x, A(x)), B=Forall(x, B(x))), prevs=[10])
        prf.add_item(12, "implies_elim", prevs=[11, 5])
        prf.add_item(13, "implies_elim", prevs=[12, 9])
        prf.add_item(14, "implies_intr", args=all_conj, prevs=[13])
        th = Thm(Implies(all_conj, conj_all))
        self.assertEqual(theory.check_proof(prf), th)

    def testAllConjWithMacro(self):
        """Proof of (!x. A x & B x) --> (!x. A x) & (!x. B x), using macros."""
        basic.load_theory('logic_base')
        Ta = TVar("a")
        A = Var("A", TFun(Ta, BoolType))
        B = Var("B", TFun(Ta, BoolType))
        x = Var("x", Ta)
        all_conj = Forall(x, And(A(x), B(x)))
        conj_all = And(Forall(x, A(x)), Forall(x, B(x)))

        prf = Proof(all_conj)
        prf.add_item(1, "forall_elim", args=x, prevs=[0])
        prf.add_item(2, "apply_theorem", args="conjD1", prevs=[1])
        prf.add_item(3, "forall_intr", args=x, prevs=[2])
        prf.add_item(4, "apply_theorem", args="conjD2", prevs=[1])
        prf.add_item(5, "forall_intr", args=x, prevs=[4])
        prf.add_item(6, "apply_theorem", args="conjI", prevs=[3, 5])
        prf.add_item(7, "implies_intr", args=all_conj, prevs=[6])
        th = Thm(Implies(all_conj, conj_all))
        self.assertEqual(theory.check_proof(prf), th)

    def testDoubleNeg(self):
        """Proof of A --> ~~A."""
        basic.load_theory('logic_base')
        A = Var("A", BoolType)

        prf = Proof(A)
        prf.add_item(1, "assume", args=Not(A))
        prf.add_item(2, "apply_theorem_for", args=("negE", Inst(A=A)))
        prf.add_item(3, "implies_elim", prevs=[2, 1])
        prf.add_item(4, "implies_elim", prevs=[3, 0])
        prf.add_item(5, "implies_intr", args=Not(A), prevs=[4])
        prf.add_item(6, "theorem", args="negI")
        prf.add_item(7, "substitution", args=Inst(A=Not(A)), prevs=[6])
        prf.add_item(8, "implies_elim", prevs=[7, 5])
        prf.add_item(9, "implies_intr", args=A, prevs=[8])
        th = Thm(Implies(A, Not(Not(A))))
        self.assertEqual(theory.check_proof(prf), th)

    def testDoubleNegInvWithMacro(self):
        """Proof of ~~A --> A, using macros."""
        basic.load_theory('logic_base')
        A = Var("A", BoolType)

        prf = Proof(Not(Not(A)))
        prf.add_item(1, "apply_theorem_for", args=("classical", Inst(A=A)))
        prf.add_item(2, "assume", args=A)
        prf.add_item(3, "assume", args=Not(A))
        prf.add_item(4, "apply_theorem", args="negE", prevs=[0, 3])
        prf.add_item(5, "apply_theorem_for", args=("falseE", Inst(A=A)), prevs=[4])
        prf.add_item(6, "implies_intr", args=A, prevs=[2])
        prf.add_item(7, "implies_intr", args=Not(A), prevs=[5])
        prf.add_item(8, "apply_theorem", args="disjE", prevs=[1, 6, 7])
        prf.add_item(9, "implies_intr", args=Not(Not(A)), prevs=[8])
        th = Thm(Implies(Not(Not(A)), A))
        self.assertEqual(theory.check_proof(prf), th)

    def testTrueAbsorb(self):
        """Proof of A --> true & A."""
        basic.load_theory('logic_base')
        A = Var("A", BoolType)

        prf = Proof(A)
        prf.add_item(1, "theorem", args="trueI")
        prf.add_item(2, "theorem", args="conjI")
        prf.add_item(3, "substitution", args=Inst(A=true, B=A), prevs=[2])
        prf.add_item(4, "implies_elim", prevs=[3, 1])
        prf.add_item(5, "implies_elim", prevs=[4, 0])
        prf.add_item(6, "implies_intr", args=A, prevs=[5])
        th = Thm(Implies(A, And(true, A)))
        self.assertEqual(theory.check_proof(prf), th)

    def testExistsConjWithMacro(self):
        """Proof of (?x. A x & B x) --> (?x. A x) & (?x. B x), using macros."""
        basic.load_theory('logic_base')
        Ta = TVar("a")
        A = Var("A", TFun(Ta, BoolType))
        B = Var("B", TFun(Ta, BoolType))
        x = Var("x", Ta)
        exists_conj = Exists(x, And(A(x), B(x)))
        conj_exists = And(Exists(x, A(x)), Exists(x, B(x)))

        prf = Proof(exists_conj)
        prf.add_item(1, "assume", args=And(A(x), B(x)))
        prf.add_item(2, "apply_theorem", args="conjD1", prevs=[1])
        prf.add_item(3, "apply_theorem", args="conjD2", prevs=[1])
        prf.add_item(4, "apply_theorem_for", args=("exI", Inst(P=A, a=x)), prevs=[2])
        prf.add_item(5, "apply_theorem_for", args=("exI", Inst(P=B, a=x)), prevs=[3])
        prf.add_item(6, "apply_theorem", args="conjI", prevs=[4, 5])
        prf.add_item(7, "implies_intr", args=And(A(x), B(x)), prevs=[6])
        prf.add_item(8, "forall_intr", args=x, prevs=[7])
        prf.add_item(9, "apply_theorem", args="exE", prevs=[0, 8])
        prf.add_item(10, "implies_intr", args=exists_conj, prevs=[9])
        th = Thm(Implies(exists_conj, conj_exists))
        self.assertEqual(theory.check_proof(prf), th)

    def testAddZeroRight(self):
        """Proof of n + 0 = n by induction."""
        basic.load_theory('nat')
        n = Var("n", NatType)
        prf = Proof()
        prf.add_item(0, "theorem", args="nat_induct")
        prf.add_item(1, "substitution", args=Inst(P=Lambda(n, Eq(n + 0, n)), x=n), prevs=[0])
        prf.add_item(2, "beta_norm", prevs=[1])
        prf.add_item(3, "theorem", args="nat_plus_def_1")
        prf.add_item(4, "substitution", args=Inst(n=Nat(0)), prevs=[3])
        prf.add_item(5, "implies_elim", prevs=[2, 4])
        prf.add_item(6, "assume", args=Eq(n + 0, n))
        prf.add_item(7, "theorem", args="nat_plus_def_2")
        prf.add_item(8, "substitution", args=Inst(m=n, n=Nat(0)), prevs=[7])
        prf.add_item(9, "reflexive", args=nat.Suc)
        prf.add_item(10, "combination", prevs=[9, 6])
        prf.add_item(11, "transitive", prevs=[8, 10])
        prf.add_item(12, "implies_intr", args=Eq(n + 0, n), prevs=[11])
        prf.add_item(13, "forall_intr", args=n, prevs=[12])
        prf.add_item(14, "implies_elim", prevs=[5, 13])
        th = Thm(Eq(n + 0, n))
        self.assertEqual(theory.check_proof(prf), th)

    def testAddZeroRightWithMacro(self):
        """Proof of n + 0 = n by induction, using macros."""
        basic.load_theory('nat')
        n = Var("n", NatType)
        S = nat.Suc
        prf = Proof()
        prf.add_item(0, "reflexive", args=Nat(0))
        prf.add_item(1, "rewrite_goal", args=("nat_plus_def_1", Eq(Nat(0) + 0, 0)), prevs=[0])
        prf.add_item(2, "assume", args=Eq(n + 0, n))
        prf.add_item(3, "reflexive", args=S)
        prf.add_item(4, "combination", prevs=[3, 2])
        prf.add_item(5, "rewrite_goal", args=("nat_plus_def_2", Eq(S(n) + 0, S(n))), prevs=[4])
        prf.add_item(6, "implies_intr", args=Eq(n + 0, n), prevs=[5])
        prf.add_item(7, "forall_intr", args=n, prevs=[6])
        prf.add_item(8, "apply_theorem_for", args=("nat_induct", Inst(P=Lambda(n, Eq(n + 0, n)), x=n)), prevs=[1, 7])
        th = Thm(Eq(n + 0, n))
        self.assertEqual(theory.check_proof(prf), th)

    def testMultZeroRight(self):
        """Proof of n * 0 = 0 by induction."""
        basic.load_theory('nat')
        n = Var("n", NatType)
        prf = Proof()
        prf.add_item(0, "theorem", args="nat_induct")
        prf.add_item(1, "substitution", args=Inst(P=Lambda(n, Eq(n * 0, 0)), x=n), prevs=[0])
        prf.add_item(2, "beta_norm", prevs=[1])
        prf.add_item(3, "theorem", args="nat_times_def_1")
        prf.add_item(4, "substitution", args=Inst(n=Nat(0)), prevs=[3])
        prf.add_item(5, "implies_elim", prevs=[2, 4])
        prf.add_item(6, "assume", args=Eq(n * 0, 0))
        prf.add_item(7, "theorem", args="nat_times_def_2")
        prf.add_item(8, "substitution", args=Inst(m=n, n=Nat(0)), prevs=[7])
        prf.add_item(9, "theorem", args="nat_plus_def_1")
        prf.add_item(10, "substitution", args=Inst(n=n * 0), prevs=[9])
        prf.add_item(11, "transitive", prevs=[8, 10])
        prf.add_item(12, "transitive", prevs=[11, 6])
        prf.add_item(13, "implies_intr", args=Eq(n * 0, 0), prevs=[12])
        prf.add_item(14, "forall_intr", args=n, prevs=[13])
        prf.add_item(15, "implies_elim", prevs=[5, 14])
        th = Thm(Eq(n * 0, 0))
        self.assertEqual(theory.check_proof(prf), th)

    def testMultZeroRightWithMacro(self):
        """Proof of n * 0 = 0 by induction, using macros."""
        basic.load_theory('nat')
        n = Var("n", NatType)
        S = nat.Suc
        prf = Proof()
        prf.add_item(0, "reflexive", args=Nat(0))
        prf.add_item(1, "rewrite_goal", args=("nat_times_def_1", Eq(Nat(0) * 0, 0)), prevs=[0])
        prf.add_item(2, "assume", args=Eq(n * 0, 0))
        prf.add_item(3, "reflexive", args=n * 0)
        prf.add_item(4, "rewrite_goal", args=("nat_plus_def_1", Eq(0 + n * 0, n * 0)), prevs=[3])
        prf.add_item(5, "transitive", prevs=[4, 2])
        prf.add_item(6, "rewrite_goal", args=("nat_times_def_2", Eq(S(n) * 0, 0)), prevs=[5])
        prf.add_item(7, "implies_intr", args=Eq(n * 0, 0), prevs=[6])
        prf.add_item(8, "forall_intr", args=n, prevs=[7])
        prf.add_item(9, "apply_theorem_for", args=("nat_induct", Inst(P=Lambda(n, Eq(n * 0, 0)), x=n)), prevs=[1, 8])
        th = Thm(Eq(n * 0, 0))
        self.assertEqual(theory.check_proof(prf), th)

    def testIntersection(self):
        """Proof of x : A INTER B --> x : A."""
        basic.load_theory('set')
        Ta = TVar('a')
        x = Var('x', Ta)
        A = Var('A', set.setT(Ta))
        B = Var('B', set.setT(Ta))
        x_in_AB = set.mk_mem(x, set.mk_inter(A, B))
        x_in_A = set.mk_mem(x, A)
        prf = Proof(x_in_AB)
        prf.add_item(1, "rewrite_fact", args="member_inter_iff", prevs=[0])
        prf.add_item(2, "apply_theorem", args="conjD1", prevs=[1])
        prf.add_item(3, "implies_intr", args=x_in_AB, prevs=[2])
        self.assertEqual(theory.check_proof(prf), Thm(Implies(x_in_AB, x_in_A)))


if __name__ == "__main__":
    unittest.main()
