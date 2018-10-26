# Author: Bohua Zhan

import unittest

from kernel.type import TVar, TFun, hol_bool
from kernel.term import Var, Term
from kernel.thm import Thm
from kernel.proof import Proof
from kernel.theory import Theory
import logic.basic as basic

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
        conjAB = basic.Logic.mk_conj(A, B)
        conjBA = basic.Logic.mk_conj(B, A)
        th1 = thy.get_theorem("conjD1")
        th2 = Thm.implies_elim(th1, Thm.assume(conjAB))
        th3 = thy.get_theorem("conjD2")
        th4 = Thm.implies_elim(th3, Thm.assume(conjAB))
        th5 = thy.get_theorem("conjI")
        th6 = Thm.substitution(th5, {"A" : B, "B" : A})
        th7 = Thm.implies_elim(th6, th4)
        th8 = Thm.implies_elim(th7, th2)
        th9 = Thm.implies_intr(th8, conjAB)

        prf = Proof(conjAB)
        prf.add_item("S1", th1, "theorem", args = "conjD1")
        prf.add_item("S2", th2, "implies_elim", prevs = ["S1", "A1"])
        prf.add_item("S3", th3, "theorem", args = "conjD2")
        prf.add_item("S4", th4, "implies_elim", prevs = ["S3", "A1"])
        prf.add_item("S5", th5, "theorem", args = "conjI")
        prf.add_item("S6", th6, "substitution", args = {"A" : B, "B" : A}, prevs = ["S5"])
        prf.add_item("S7", th7, "implies_elim", prevs = ["S6", "S4"])
        prf.add_item("S8", th8, "implies_elim", prevs = ["S7", "S2"])
        prf.add_item("S9", th9, "implies_intr", args = conjAB, prevs = ["S8"])
        self.assertEqual(th9, Thm([], Term.mk_implies(conjAB, conjBA)))
        self.assertEqual(thy.check_proof(prf), th9)

if __name__ == "__main__":
    unittest.main()
