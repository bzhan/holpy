# Author: Bohua Zhan

import unittest

from kernel.type import TVar, TFun, hol_bool
from kernel.term import Var, Const, Comb, Abs, Bound, Term
from logic.basic import BasicTheory, Logic
from syntax.printer import print_term

thy = BasicTheory()

A = Var("A", hol_bool)
B = Var("B", hol_bool)
C = Var("C", hol_bool)
Ta = TVar("a")
a = Var("a", Ta)
b = Var("b", Ta)
P = Var("P", TFun(Ta, hol_bool))
Q = Var("Q", TFun(Ta, hol_bool))
R = Var("R", TFun(Ta, Ta, hol_bool))
f = Var("f", TFun(Ta, Ta))
n = Var("n", TFun(hol_bool, hol_bool))
eq = Term.mk_equals
imp = Term.mk_implies
conj = Logic.mk_conj
disj = Logic.mk_disj
all = Term.mk_all

class PrinterTest(unittest.TestCase):
    def testPrintLogical(self):
        test_data = [
            # Equality and implies
            (eq(a, b), "a = b"),
            (imp(A, B), "A --> B"),
            (imp(A, B, C), "A --> B --> C"),
            (imp(imp(A, B), C), "(A --> B) --> C"),
            (imp(A, eq(a, b)), "A --> a = b"),
            (eq(imp(A, B), imp(B, C)), "(A --> B) = (B --> C)"),
            (eq(A, eq(B, C)), "A = (B = C)"),
            (eq(eq(A, B), C), "A = B = C"),

            # Conjunction and disjunction
            (conj(A, B), "A & B"),
            (disj(A, B), "A | B"),
            (conj(A, conj(B, C)), "A & B & C"),
            (conj(conj(A, B), C), "(A & B) & C"),
            (disj(A, disj(B, C)), "A | B | C"),
            (disj(disj(A, B), C), "(A | B) | C"),
            (disj(conj(A, B), C), "A & B | C"),
            (conj(disj(A, B), C), "(A | B) & C"),
            (disj(A, conj(B, C)), "A | B & C"),
            (conj(A, disj(B, C)), "A & (B | C)"),
            (disj(conj(A, B), conj(B, C)), "A & B | B & C"),
            (conj(disj(A, B), disj(B, C)), "(A | B) & (B | C)"),

            # Mixed
            (imp(conj(A, B), C), "A & B --> C"),
            (imp(A, disj(B, C)), "A --> B | C"),
            (conj(A, imp(B, C)), "A & (B --> C)"),
            (disj(imp(A, B), C), "(A --> B) | C"),

            # Abstraction
            (Abs("x", Ta, conj(P(a), Q(a))), "%x. P a & Q a"),

            # Quantifiers
            (all(a, P(a)), "!a. P a"),
            (all(a, all(b, conj(P(a),P(b)))), "!a. !b. P a & P b"),
            (all(a, conj(P(a), Q(a))), "!a. P a & Q a"),
            (conj(all(a, P(a)), Q(a)), "(!a. P a) & Q a"),
            (all(a, imp(P(a), Q(a))), "!a. P a --> Q a"),
            (imp(all(a, P(a)), Q(a)), "(!a. P a) --> Q a"),
            (eq(A, all(a, P(a))), "A = (!a. P a)"),
        ]

        for t, s in test_data:
            self.assertEqual(print_term(thy, t), s)

    def testPrintFunction(self):
        test_data = [
            (P(a), "P a"),
            (P(f(a)), "P (f a)"),
            (R(a,a), "R a a"),
            (n(conj(A,B)), "n (A & B)"),
            (conj(n(A), B), "n A & B"),
        ]

        for t, s in test_data:
            self.assertEqual(print_term(thy, t), s)

    def testPrintAbsType(self):
        test_data = [
            (Abs("x", Ta, b), "%x::'a. b"),
            (Abs("x", Ta, "y", Ta, b), "%x::'a. %y::'a. b"),
            (all(a, P(a)), "!a::'a. P a"),
            (all(a, all(b, conj(P(a),P(b)))), "!a::'a. !b::'a. P a & P b"),
        ]

        for t, repr_t in test_data:
            self.assertEqual(print_term(thy, t, print_abs_type = True), repr_t)

    def testPrintUnicode(self):
        test_data = [
            (conj(A, B), "A ∧ B"),
            (disj(A, B), "A ∨ B"),
            (imp(A, B), "A ⟶ B"),
            (Abs("x", Ta, b), "λx. b"),
            (all(a, P(a)), "∀a. P a"),
        ]

        for t, s in test_data:
            self.assertEqual(print_term(thy, t, unicode = True), s)

if __name__ == "__main__":
    unittest.main()
