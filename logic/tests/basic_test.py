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

        prf = Proof(conjAB)
        prf.add_item("S1", "theorem", args = "conjD1")
        prf.add_item("S2", "implies_elim", prevs = ["S1", "A1"])
        prf.add_item("S3", "theorem", args = "conjD2")
        prf.add_item("S4", "implies_elim", prevs = ["S3", "A1"])
        prf.add_item("S5", "theorem", args = "conjI")
        prf.add_item("S6", "substitution", args = {"A" : B, "B" : A}, prevs = ["S5"])
        prf.add_item("S7", "implies_elim", prevs = ["S6", "S4"])
        prf.add_item("S8", "implies_elim", prevs = ["S7", "S2"])
        prf.add_item("S9", "implies_intr", args = conjAB, prevs = ["S8"])
        th = Thm([], Term.mk_implies(conjAB, conjBA))
        self.assertEqual(thy.check_proof(prf), th)

if __name__ == "__main__":
    unittest.main()
