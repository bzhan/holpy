# Author: Bohua Zhan

import unittest
from kernel.theory import *
from logic.basic import *

Ta = TVar("a")
x = Var("x", Ta)
y = Var("y", Ta)
f = Var("f", TFun(Ta,Ta))
g = Var("g", TFun(Ta,Ta))

class BasicTest(unittest.TestCase):
    def testArgCombination(self):
        th = Thm.mk_equals(x,y)
        res = Thm.mk_equals(Comb(f,x), Comb(f,y))
        self.assertEqual(arg_combination_macro.eval(th, f), res)
        prf = arg_combination_macro.expand(1, [(0, "S1")], th, f)
        
        thy = Theory.EmptyTheory()
        self.assertEqual(len(prf), 2)
        self.assertEqual(thy._check_proof_items(1, {(0, "S1"): th}, prf), None)

    def testFunCombination(self):
        th = Thm.mk_equals(f,g)
        res = Thm.mk_equals(Comb(f,x), Comb(g,x))
        self.assertEqual(fun_combination_macro.eval(th, x), res)
        prf = fun_combination_macro.expand(1, [(0, "S1")], th, x)

        thy = Theory.EmptyTheory()
        self.assertEqual(len(prf), 2)
        self.assertEqual(thy._check_proof_items(1, {(0, "S1"): th}, prf), None)

if __name__ == "__main__":
    unittest.main()
