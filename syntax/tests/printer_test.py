# Author: Bohua Zhan

import unittest

from kernel.type import TVar, Type, TFun, boolT
from kernel.term import Var, Const, Comb, Abs, Bound, Term
from kernel.thm import Thm
from logic import basic
from logic import logic
from data import nat
from data import list
from data import set
from data import function
from data import interval
from syntax import printer

thy = basic.load_theory('list')

A = Var("A", boolT)
B = Var("B", boolT)
C = Var("C", boolT)
Ta = TVar("a")
a = Var("a", Ta)
b = Var("b", Ta)
P = Var("P", TFun(Ta, boolT))
Q = Var("Q", TFun(Ta, boolT))
R = Var("R", TFun(Ta, Ta, boolT))
f = Var("f", TFun(Ta, Ta))
nn = Var("n", TFun(boolT, boolT))
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

class PrinterTest(unittest.TestCase):
    def testPrintLogical(self):
        test_data = [
            # Equality and implies
            (eq(a, b), "a = b"),
            (imp(A, B), "A --> B"),
            (imp(A, B, C), "A --> B --> C"),
            (imp(imp(A, B), C), "(A --> B) --> C"),
            (imp(A, eq(a, b)), "A --> a = b"),
            (eq(imp(A, B), imp(B, C)), "(A --> B) <--> B --> C"),
            (eq(A, eq(B, C)), "A <--> B <--> C"),
            (eq(eq(A, B), C), "(A <--> B) <--> C"),

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
            (neg(eq(A, B)), "~(A <--> B)"),
            (eq(neg(A), B), "~A <--> B"),
            (eq(neg(A), neg(B)), "~A <--> ~B"),

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
            (eq(A, all(a, P(a))), "A <--> (!a. P a)"),
            (exists(a, P(a)), "?a. P a"),
            (exists(a, all(b, R(a, b))), "?a. !b. R a b"),
            (all(a, exists(b, R(a, b))), "!a. ?b. R a b"),

            # If
            (mk_if(A, a, b), "if A then a else b"),
            (eq(mk_if(A, a, b), a), "(if A then a else b) = a"),
            (mk_if(A, P, Q), "if A then P else Q"),
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
            (nat.less_eq(m, n), "m <= n"),
            (nat.less(m, n), "m < n"),
            (nat.less_eq(nat.plus(m, n), p), "m + n <= p"),
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
        nil = list.nil
        cons = list.mk_cons
        append = list.mk_append
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

    def testPrintSet(self):
        A = Var("A", set.setT(Ta))
        B = Var("B", set.setT(Ta))
        x = Var("x", Ta)
        y = Var("y", Ta)
        P = Var("P", TFun(Ta, boolT))
        S = Var("S", set.setT(set.setT(Ta)))
        test_data = [
            (set.empty_set(Ta), "({}::'a set)", "(∅::'a set)"),
            (set.mk_mem(x, A), "x Mem A", "x ∈ A"),
            (set.mk_subset(A, B), "A Sub B", "A ⊆ B"),
            (set.mk_inter(A, B), "A Int B", "A ∩ B"),
            (set.mk_union(A, B), "A Un B", "A ∪ B"),
            (set.mk_insert(x, set.empty_set(Ta)), "{x}", "{x}"),
            (set.mk_insert(x, set.mk_insert(y, set.empty_set(Ta))), "{x, y}", "{x, y}"),
            (set.mk_insert(x, A), "insert x A", "insert x A"),
            (set.mk_collect(x, P(x)), "{x. P x}", "{x. P x}"),
            (set.collect(Ta)(P), "collect P", "collect P"),
            (set.mk_Union(S), "UN S", "⋃S"),
            (set.mk_Inter(S), "INT S", "⋂S"),
        ]

        for t, s1, s2 in test_data:
            self.assertEqual(printer.print_term(thy, t), s1)
            self.assertEqual(printer.print_term(thy, t, unicode=True), s2)

    def testPrintInterval(self):
        m = Var("m", nat.natT)
        n = Var("n", nat.natT)
        test_data = [
            (interval.mk_interval(m, n), "{m..n}"),
            (interval.mk_interval(nat.one, m), "{1..m}"),
        ]

        for t, s in test_data:
            self.assertEqual(printer.print_term(thy, t), s)

    def testPrintFunction(self):
        test_data = [
            (function.mk_fun_upd(f, a, b), "(f)(a := b)"),
            (function.mk_fun_upd(f, a, b, b, a), "(f)(a := b, b := a)"),
        ]

        thy = basic.load_theory('function')
        for t, s in test_data:
            self.assertEqual(printer.print_term(thy, t), s)

    def testPrintWithType(self):
        test_data = [
            (list.nil(Ta), "([]::'a list)"),
            (eq(list.nil(Ta), list.nil(Ta)), "([]::'a list) = []"),
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
        # 0, 1, 2, 3 = NORMAL, BOUND, VAR, TVAR
        test_data = [
            (abs(a,P(a)), [('%',0),('a',1),('. ',0),('P ',2),('a',1)]),
            (all(a,P(a)), [('!',0),('a',1),('. ',0),('P ',2),("a",1)]),
            (all(a,all(b,conj(P(a),P(b)))), [('!',0),('a',1),('. !',0),('b',1),('. ',0),('P ',2),('a',1),(' & ',0),('P ',2),('b',1)]),
            (exists(a,all(b,R(a,b))), [('?',0),("a",1),('. !',0),('b',1),('. ',0),('R ',2),('a b',1)]),
            (exists(a,P(a)), [('?',0),('a',1),('. ',0),('P ',2),('a',1)]),
            (disj(disj(A,B),C), [('(',0),('A',2),(' | ',0),('B',2),(') | ',0),('C',2)]),
            (imp(imp(A,B),C), [('(',0),('A',2),(' --> ',0),('B',2),(') --> ',0),('C',2)]),
            (abs(a,a), [('%',0),('a',1),('::',0),("'a",3),('. ',0),('a',1)]),
        ]

        for t, s in test_data:
            self.assertEqual(printer.print_term(thy, t, highlight=True), s)

    def testPrintThmHighlight(self):
        """Test printing of theorems with highlight."""
        # 0, 1, 2, 3 = NORMAL, BOUND, VAR, TVAR
        A = Var('A', boolT)
        B = Var('B', boolT)
        A_to_B = Term.mk_implies(A, B)
        th = Thm([A, A_to_B], B)
        res = printer.print_thm(thy, th, highlight=True)
        self.assertEqual(res, [('A',2),(', ',0),('A',2),(' --> ',0),('B',2),(' ',0),('|-',0),(' ',0),('B',2)])


if __name__ == "__main__":
    unittest.main()
