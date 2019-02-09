# Author: Bohua Zhan

import unittest

from kernel.type import TVar, Type, TFun, hol_bool
from kernel.term import Var, Const, Comb, Abs, Bound, Term
from kernel.thm import Thm
from logic import logic
from logic import nat
from logic import list
from logic import basic
from syntax import printer

thy = basic.loadTheory('list')

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
m = Var("m", nat.natT)
n = Var("n", nat.natT)
p = Var("p", nat.natT)
xs = Var("xs", Type("list", Ta))
ys = Var("ys", Type("list", Ta))
zs = Var("zs", Type("list", Ta))
eq = Term.mk_equals
imp = Term.mk_implies
conj = logic.mk_conj
disj = logic.mk_disj
abs = Term.mk_abs
all = Term.mk_all
neg = logic.neg
exists = logic.mk_exists
mk_if = logic.mk_if
nil = list.nil
cons = list.mk_cons
append = list.mk_append

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
            (abs(a, conj(P(a),Q(a))), "%a. P a & Q a"),

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

            # If
            (mk_if(A, a, b), "if A then a else b"),
            (eq(mk_if(A, a, b), a), "(if A then a else b) = a"),
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
            (nat.plus(m, n), "m + n"),
            (nat.plus(nat.plus(m, n), p), "m + n + p"),
            (nat.plus(m, nat.plus(n, p)), "m + (n + p)"),
            (nat.times(m, n), "m * n"),
            (nat.times(nat.times(m, n), p), "m * n * p"),
            (nat.times(m, nat.times(n, p)), "m * (n * p)"),
            (nat.plus(m, nat.times(n, p)), "m + n * p"),
            (nat.times(m, nat.plus(n, p)), "m * (n + p)"),
            (nat.zero, "0"),
            (nat.plus(nat.zero, nat.zero), "0 + 0"),
            (nat.times(m, nat.zero), "m * 0"),
        ]

        for t, s in test_data:
            self.assertEqual(printer.print_term(thy, t), s)

    def testBinary(self):
        test_data = [
            (nat.one, "1"),
            (nat.bit0(nat.one), "2"),
            (nat.bit1(nat.one), "3"),
            (nat.Suc(nat.one), "Suc 1"),
        ]

        for t, s in test_data:
            self.assertEqual(printer.print_term(thy, t), s)

    def testPrintList(self):
        test_data = [
            (append(xs, ys), "xs @ ys"),
            (append(append(xs, ys), zs), "(xs @ ys) @ zs"),
            (append(xs, append(ys, zs)), "xs @ ys @ zs"),
            (cons(a, nil(Ta)), "[a]"),
            (cons(a, cons(b, nil(Ta))), "[a, b]"),
            (cons(a, xs), "a # xs"),
            (append(cons(a, nil(Ta)), cons(b, nil(Ta))), "[a] @ [b]"),
            (cons(a, append(xs, ys)), "a # xs @ ys"),
            (append(cons(a, xs), ys), "(a # xs) @ ys"),
            (list.cons(Ta)(a), "cons a"),
        ]

        for t, s in test_data:
            self.assertEqual(printer.print_term(thy, t), s)

    def testPrintWithType(self):
        test_data = [
            (nil(Ta), "([]::'a list)"),
            (eq(nil(Ta),nil(Ta)), "([]::'a list) = []"),
            (all(a, eq(a, a)), "!a::'a. a = a"),
        ]

        for t, s in test_data:
            self.assertEqual(printer.print_term(thy, t), s)

    def testPrintUnicode(self):
        test_data = [
            (conj(A, B), "A ∧ B"),
            (disj(A, B), "A ∨ B"),
            (imp(A, B), "A ⟶ B"),
            (abs(a, P(a)), "λa. P a"),
            (all(a, P(a)), "∀a. P a"),
            (exists(a, P(a)), "∃a. P a"),
            (neg(A), "¬A"),
            (nat.plus(m, n), "m + n"),
            (nat.times(m, n), "m * n"),
        ]

        for t, s in test_data:
            self.assertEqual(printer.print_term(thy, t, unicode=True), s)

    def testPrintHighlight(self):
        """Test highlight"""
        # 0, 1, 2 = NORMAL, BOUND, VAR
        test_data = [
            (abs(a,P(a)), [('%',0),('a',1),('. ',0),('P',2),(' ',0),('a',1)]),
            (all(a,P(a)), [('!',0),('a',1),('. ',0),('P',2),(' ',0),("a",1)]),
            (all(a,all(b,conj(P(a),P(b)))), [('!',0),('a',1),('. ',0),('!',0),('b',1),('. ',0),('P',2),(' ',0),('a',1),(' & ',0),('P',2),(' ',0),('b',1)]),
            (exists(a,all(b,R(a,b))), [('?',0),("a",1),('. ',0),('!',0),('b',1),('. ',0),('R',2),(' ',0),('a',1),(' ',0),('b',1)]),
            (exists(a,P(a)), [('?',0),('a',1),('. ',0),('P',2),(' ',0),('a',1)]),
            (disj(disj(A,B),C), [('(',0),('A',2),(' | ',0),('B',2),(')',0),(' | ',0),('C',2)]),
            (imp(imp(A,B),C), [('(',0),('A',2),(' --> ',0),('B',2),(')',0),(' --> ',0),('C',2)]),
            (abs(a,a), [('%',0),('a',1),('::',0),("'a",0),('. ',0),('a',1)]),
        ]

        for t, s in test_data:
            self.assertEqual(printer.print_term(thy, t, highlight=True), s)

    def testPrintThmHighlight(self):
        """Test printing of theorems with highlight."""
        # 0, 1, 2 = NORMAL, BOUND, VAR
        A = Var('A', hol_bool)
        B = Var('B', hol_bool)
        A_to_B = Term.mk_implies(A, B)
        th = Thm([A, A_to_B], B)
        res = printer.print_thm(thy, th, highlight=True)
        self.assertEqual(res, [('A',2),(', ',0),('A',2),(' --> ',0),('B',2),(' ',0),('|-',0),(' ',0),('B',2)])


if __name__ == "__main__":
    unittest.main()
