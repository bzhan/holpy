# Author: Bohua Zhan

import unittest

from kernel.type import TVar, hol_bool
from kernel.term import Var, Const, Comb, Abs, Bound, Term
from logic.basic import BasicTheory
from syntax.printer import print_term

thy = BasicTheory()

A = Var("A", hol_bool)
B = Var("B", hol_bool)
C = Var("C", hol_bool)
Ta = TVar("a")
a = Var("a", Ta)
b = Var("b", Ta)
eq = Term.mk_equals
imp = Term.mk_implies

class PrinterTest(unittest.TestCase):
    def testPrintAbsType(self):
        test_data = [
            (Abs("x", Ta, b), "%x::'a. b"),
            (Abs("x", Ta, "y", Ta, b), "%x::'a. %y::'a. b"),
        ]

        for (t, repr_t) in test_data:
            self.assertEqual(t.repr_with_abs_type(), repr_t)

    def testPrintLogical(self):
        test_data = [
            (eq(a, b), "a = b"),
            (imp(A, B), "A --> B"),
            (imp(A, imp(B, C)), "A --> B --> C"),
            (imp(imp(A, B), C), "(A --> B) --> C"),
            (imp(A, eq(a, b)), "A --> a = b"),
            (eq(imp(A, B), imp(B, C)), "(A --> B) = (B --> C)"),
            (eq(A, eq(B, C)), "A = (B = C)"),
            (eq(eq(A, B), C), "A = B = C"),
        ]

        for t, s in test_data:
            self.assertEqual(print_term(thy, t), s)

if __name__ == "__main__":
    unittest.main()
