# Author: Bohua Zhan

import unittest

from kernel.type import TVar, TFun, hol_bool
from kernel.term import Var, Const, Comb, Abs, Bound, Term
from logic import logic
from logic.nat import Nat
from logic.basic import BasicTheory
from syntax import printer

thy = BasicTheory

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
nn = Var("n", TFun(hol_bool, hol_bool))
m = Var("m", Nat.nat)
n = Var("n", Nat.nat)
p = Var("p", Nat.nat)
eq = Term.mk_equals
imp = Term.mk_implies
conj = logic.mk_conj
disj = logic.mk_disj
all = Term.mk_all
neg = logic.neg
exists = logic.mk_exists

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

            # Negation
            (neg(A), "~A"),
            (neg(neg(A)), "~~A"),

            # Constants
            (logic.true, "true"),
            (logic.false, "false"),

            # Mixed
            (imp(conj(A, B), C), "A & B --> C"),
            (imp(A, disj(B, C)), "A --> B | C"),
            (conj(A, imp(B, C)), "A & (B --> C)"),
            (disj(imp(A, B), C), "(A --> B) | C"),
            (neg(conj(A, B)), "~(A & B)"),
            (neg(imp(A, B)), "~(A --> B)"),
            (neg(eq(A, B)), "~A = B"),
            (eq(neg(A), B), "(~A) = B"),
            (eq(neg(A), neg(B)), "(~A) = (~B)"),

            # Abstraction
            (Abs("x", Ta, conj(P(a), Q(a))), "%x. P a & Q a"),

            # Quantifiers
            (all(a, P(a)), "!a. P a"),
            (all(a, all(b, conj(P(a),P(b)))), "!a. !b. P a & P b"),
            (all(a, conj(P(a), Q(a))), "!a. P a & Q a"),
            (conj(all(a, P(a)), Q(a)), "(!a. P a) & Q a"),
            (all(a, imp(P(a), Q(a))), "!a. P a --> Q a"),
            (imp(all(a, P(a)), Q(a)), "(!a. P a) --> Q a"),
            (imp(all(a, P(a)), all(a, Q(a))), "(!a. P a) --> (!a. Q a)"),
            (imp(exists(a, P(a)), exists(a, Q(a))), "(?a. P a) --> (?a. Q a)"),
            (eq(A, all(a, P(a))), "A = (!a. P a)"),
            (exists(a, P(a)), "?a. P a"),
            (exists(a, all(b, R(a, b))), "?a. !b. R a b"),
            (all(a, exists(b, R(a, b))), "!a. ?b. R a b"),
        ]

        for t, s in test_data:
            self.assertEqual(printer.print_term(thy, t), s)

    def testPrintFunction(self):
        test_data = [
            (P(a), "P a"),
            (P(f(a)), "P (f a)"),
            (R(a,a), "R a a"),
            (nn(conj(A,B)), "n (A & B)"),
            (conj(nn(A), B), "n A & B"),
        ]

        for t, s in test_data:
            self.assertEqual(printer.print_term(thy, t), s)

    def testPrintArithmetic(self):
        test_data = [
            (Nat.plus(m, n), "m + n"),
            (Nat.plus(Nat.plus(m, n), p), "m + n + p"),
            (Nat.plus(m, Nat.plus(n, p)), "m + (n + p)"),
            (Nat.times(m, n), "m * n"),
            (Nat.times(Nat.times(m, n), p), "m * n * p"),
            (Nat.times(m, Nat.times(n, p)), "m * (n * p)"),
            (Nat.plus(m, Nat.times(n, p)), "m + n * p"),
            (Nat.times(m, Nat.plus(n, p)), "m * (n + p)"),
            (Nat.zero, "0"),
            (Nat.plus(Nat.zero, Nat.zero), "0 + 0"),
            (Nat.times(m, Nat.zero), "m * 0"),
        ]

        for t, s in test_data:
            self.assertEqual(printer.print_term(thy, t), s)

    def testPrintAbsType(self):
        test_data = [
            (Abs("x", Ta, b), "%x::'a. b"),
            (Abs("x", Ta, "y", Ta, b), "%x::'a. %y::'a. b"),
            (all(a, P(a)), "!a::'a. P a"),
            (all(a, all(b, conj(P(a),P(b)))), "!a::'a. !b::'a. P a & P b"),
        ]

        for t, repr_t in test_data:
            self.assertEqual(printer.print_term(thy, t, print_abs_type=True), repr_t)

    def testPrintUnicode(self):
        test_data = [
            (conj(A, B), "A ∧ B"),
            (disj(A, B), "A ∨ B"),
            (imp(A, B), "A ⟶ B"),
            (Abs("x", Ta, b), "λx. b"),
            (all(a, P(a)), "∀a. P a"),
            (exists(a, P(a)), "∃a. P a"),
            (neg(A), "¬A"),
            (Nat.plus(m, n), "m + n"),
            (Nat.times(m, n), "m * n"),
        ]

        for t, s in test_data:
            self.assertEqual(printer.print_term(thy, t, unicode=True), s)

    def testPrintHighlight(self):
        """Test highlight, with print_abs_type=False."""
        NORMAL, BOUND, VAR = printer.NORMAL, printer.BOUND, printer.VAR
        test_data = [
            (Abs("x", Ta, b), [('%', NORMAL), ('x', BOUND), ('. ', NORMAL), ('b', VAR)]),
            (Abs("x", Ta, "y", Ta, b), [('%', NORMAL),('x', BOUND),('. ',NORMAL),('%',NORMAL),('y',BOUND),('. ',NORMAL),('b',VAR)]),
            (all(a, P(a)), [('!', NORMAL), ('a', VAR), ('. ', NORMAL),('P', VAR),(' ',NORMAL),("a", VAR)]),
            (all(a, all(b, conj(P(a),P(b)))), [('!', NORMAL), ('a', VAR), ('. ', NORMAL), ('!',NORMAL), ('b', VAR), ('. ', NORMAL), ('P', VAR), (' ', NORMAL), ('a', VAR), (' ', NORMAL), ('&', NORMAL), (' ',NORMAL), ('P', VAR), (' ',NORMAL), ('b',VAR)]),
            (exists(a, all(b, R(a, b))), [('?', NORMAL), ("a", VAR), ('. ', NORMAL), ('!', NORMAL), ('b', VAR), ('. ', NORMAL), ('R', VAR), (' ', NORMAL), ('a', VAR), (' ', NORMAL), ('b',VAR)]),
            (exists(a, P(a)), [('?', NORMAL), ('a', VAR), ('. ', NORMAL), ('P', VAR), (' ', NORMAL), ('a', VAR)]),
            (disj(disj(A, B), C), [('(', NORMAL), ('A', VAR), (' ', NORMAL), ('|', NORMAL), (' ', NORMAL), ('B', VAR), (')', NORMAL), (' ', NORMAL), ('|', NORMAL), (' ', NORMAL), ('C', VAR)]),
            (imp(imp(A, B), C), [('(', NORMAL), ('A', VAR), (' ', NORMAL), ('-->', NORMAL), (' ', NORMAL), ('B', VAR), (')', NORMAL), (' ', NORMAL), ('-->', NORMAL), (' ',NORMAL), ('C', VAR)])
        ]

        for t, s in test_data:
            self.assertEqual(printer.print_term(thy, t, highlight=True), s)

    def testPrintHighlightAbs(self):
        """Test highlight, with print_abs_type=False."""
        NORMAL, BOUND, VAR = printer.NORMAL, printer.BOUND, printer.VAR        
        test_data = [
            (Abs("x", Ta, b), [('%', NORMAL), ('x', BOUND), ('::', NORMAL), ("'a", NORMAL), ('. ', NORMAL), ('b', VAR)]),
            (Abs("x", Ta, "y", Ta, b),
            [('%', NORMAL), ('x', BOUND), ('::',NORMAL), ("'a",NORMAL), ('. ',NORMAL), ('%',NORMAL), ('y',BOUND), ('::',NORMAL), ("'a",NORMAL), ('. ',NORMAL), ('b',VAR)]),
            (all(a, P(a)), [('!', NORMAL), ('a', VAR), ('::', NORMAL), ("'a", NORMAL), ('. ', NORMAL),('P', VAR),(' ',NORMAL),("a", VAR)]),
            (all(a, all(b, conj(P(a), P(b)))),
            [('!', NORMAL), ('a', VAR), ('::', NORMAL) ,("'a", NORMAL), ('. ', NORMAL), ('!',NORMAL), ('b', VAR), ('::', NORMAL), ("'a", NORMAL), ('. ', NORMAL), ('P', VAR), (' ', NORMAL), ('a', VAR), (' ', NORMAL), ('&', NORMAL), (' ',NORMAL), ('P', VAR), (' ',NORMAL), ('b',VAR)]),
            (exists(a, all(b, R(a, b))),
            [('?', NORMAL), ("a", VAR), ('::', NORMAL), ("'a", NORMAL), ('. ', NORMAL), ('!', NORMAL), ('b', VAR), ('::', NORMAL), ("'a", NORMAL), ('. ', NORMAL), ('R', VAR), (' ', NORMAL), ('a', VAR), (' ', NORMAL), ('b',VAR)]),
            (exists(a, P(a)), [('?', NORMAL), ('a', VAR), ('::', NORMAL), ("'a", NORMAL), ('. ', NORMAL), ('P', VAR), (' ', NORMAL), ('a', VAR)]),
            (disj(disj(A, B), C),
            [('(', NORMAL), ('A', VAR), (' ', NORMAL), ('|', NORMAL), (' ', NORMAL), ('B', VAR), (')', NORMAL), (' ', NORMAL), ('|', NORMAL), (' ', NORMAL), ('C', VAR)]),
            (imp(imp(A, B), C),
            [('(', NORMAL), ('A', VAR), (' ', NORMAL), ('-->', NORMAL), (' ', NORMAL), ('B', VAR), (')', NORMAL), (' ', NORMAL), ('-->', NORMAL), (' ',NORMAL), ('C', VAR)])
        ]

        for t, s in test_data:
            self.assertEqual(printer.print_term(thy, t, print_abs_type=True, highlight=True), s)

if __name__ == "__main__":
    unittest.main()
