# Author: Bohua Zhan

import unittest

from kernel.type import TVar, TConst, TFun, BoolType, NatType, IntType, RealType
from kernel.term import SVar, Var, Const, Comb, Abs, Bound, Term, And, Or, Implies, \
    Not, Eq, Forall, Lambda, Exists, true, false, Nat, Int, Real
from kernel.thm import Thm
from logic import basic
from logic import logic
from data import nat
from data import real
from data import list
from data import set
from data import string
from data import function
from data import interval
from syntax import printer
from syntax.settings import settings, global_setting

basic.load_theory('list')

A = Var("A", BoolType)
B = Var("B", BoolType)
C = Var("C", BoolType)
Ta = TVar("a")
a = Var("a", Ta)
b = Var("b", Ta)
P = Var("P", TFun(Ta, BoolType))
Q = Var("Q", TFun(Ta, BoolType))
R = Var("R", TFun(Ta, Ta, BoolType))
nn = Var("n", TFun(BoolType, BoolType))
m = Var("m", NatType)
n = Var("n", NatType)
p = Var("p", NatType)
xs = Var("xs", TConst("list", Ta))
ys = Var("ys", TConst("list", Ta))
zs = Var("zs", TConst("list", Ta))
mk_if = logic.mk_if

class PrinterTest(unittest.TestCase):
    def testPrintLogical(self):
        test_data = [
            # Variables
            (SVar("P", BoolType), "?P"),
            (a, "a"),

            # Equality and implies
            (Eq(a, b), "a = b"),
            (Implies(A, B), "A --> B"),
            (Implies(A, B, C), "A --> B --> C"),
            (Implies(Implies(A, B), C), "(A --> B) --> C"),
            (Implies(A, Eq(a, b)), "A --> a = b"),
            (Eq(Implies(A, B), Implies(B, C)), "(A --> B) <--> (B --> C)"),
            (Eq(A, Eq(B, C)), "A <--> B <--> C"),
            (Eq(Eq(A, B), C), "(A <--> B) <--> C"),

            # Conjunction and disjunction
            (And(A, B), "A & B"),
            (Or(A, B), "A | B"),
            (And(A, And(B, C)), "A & B & C"),
            (And(And(A, B), C), "(A & B) & C"),
            (Or(A, Or(B, C)), "A | B | C"),
            (Or(Or(A, B), C), "(A | B) | C"),
            (Or(And(A, B), C), "A & B | C"),
            (And(Or(A, B), C), "(A | B) & C"),
            (Or(A, And(B, C)), "A | B & C"),
            (And(A, Or(B, C)), "A & (B | C)"),
            (Or(And(A, B), And(B, C)), "A & B | B & C"),
            (And(Or(A, B), Or(B, C)), "(A | B) & (B | C)"),

            # Negation
            (Not(A), "~A"),
            (Not(Not(A)), "~~A"),

            # Constants
            (true, "true"),
            (false, "false"),

            # Mixed
            (Implies(And(A, B), C), "A & B --> C"),
            (Implies(A, Or(B, C)), "A --> B | C"),
            (And(A, Implies(B, C)), "A & (B --> C)"),
            (Or(Implies(A, B), C), "(A --> B) | C"),
            (Not(And(A, B)), "~(A & B)"),
            (Not(Implies(A, B)), "~(A --> B)"),
            (Not(Eq(A, B)), "~(A <--> B)"),
            (Eq(Not(A), B), "~A <--> B"),
            (Eq(Not(A), Not(B)), "~A <--> ~B"),
            (Implies(A, Eq(B, C)), "A --> B <--> C"),
            (Eq(Implies(A, B), C), "(A --> B) <--> C"),

            # Abstraction
            (Lambda(a, And(P(a),Q(a))), "%a. P a & Q a"),

            # Quantifiers
            (Forall(a, P(a)), "!a. P a"),
            (Forall(a, Forall(b, And(P(a),P(b)))), "!a. !b. P a & P b"),
            (Forall(a, And(P(a), Q(a))), "!a. P a & Q a"),
            (And(Forall(a, P(a)), Q(a)), "(!a1. P a1) & Q a"),
            (Forall(a, Implies(P(a), Q(a))), "!a. P a --> Q a"),
            (Implies(Forall(a, P(a)), Q(a)), "(!a1. P a1) --> Q a"),
            (Implies(Forall(a, P(a)), Forall(a, Q(a))), "(!a. P a) --> (!a. Q a)"),
            (Implies(Exists(a, P(a)), Exists(a, Q(a))), "(?a. P a) --> (?a. Q a)"),
            (Eq(A, Forall(a, P(a))), "A <--> (!a. P a)"),
            (Exists(a, P(a)), "?a. P a"),
            (Exists(a, Forall(b, R(a, b))), "?a. !b. R a b"),
            (logic.mk_exists1(a, P(a)), "?!a. P a"),
            (logic.mk_the(a, P(a)), "THE a. P a"),
            (Forall(a, Exists(b, R(a, b))), "!a. ?b. R a b"),

            # If
            (mk_if(A, a, b), "if A then a else b"),
            (Eq(mk_if(A, a, b), a), "(if A then a else b) = a"),
            (mk_if(A, P, Q), "if A then P else Q"),
        ]

        for t, s in test_data:
            self.assertEqual(printer.print_term(t), s)

    def testPrintRename(self):
        test_data = [
            (Const("exists", TFun(TFun(NatType, BoolType), BoolType))(
                Abs("x", NatType, nat.less(Bound(0), Var("x", NatType)))), "?x1. x1 < x"),
            (Abs("x", NatType, nat.less(Bound(0), Var("x", NatType))), "%x1. x1 < x"),
        ]

        for t, s in test_data:
            self.assertEqual(printer.print_term(t), s)

    def testPrintComb(self):
        f = Var("f", TFun(Ta, Ta))
        test_data = [
            (P(a), "P a"),
            (P(f(a)), "P (f a)"),
            (R(a,a), "R a a"),
            (nn(And(A,B)), "n (A & B)"),
            (And(nn(A), B), "n A & B"),
        ]

        for t, s in test_data:
            self.assertEqual(printer.print_term(t), s)

    def testPrintArithmetic(self):
        test_data = [
            (nat.plus(m, n), "m + n"),
            (nat.plus(nat.plus(m, n), p), "m + n + p"),
            (nat.plus(m, nat.plus(n, p)), "m + (n + p)"),
            (nat.plus(nat.minus(m, n), p), "m - n + p"),
            (nat.minus(m, nat.plus(n, p)), "m - (n + p)"),
            (nat.times(m, n), "m * n"),
            (nat.times(nat.times(m, n), p), "m * n * p"),
            (nat.times(m, nat.times(n, p)), "m * (n * p)"),
            (nat.plus(m, nat.times(n, p)), "m + n * p"),
            (nat.times(m, nat.plus(n, p)), "m * (n + p)"),
            (nat.zero, "(0::nat)"),
            (nat.plus(nat.zero, nat.zero), "(0::nat) + 0"),
            (nat.times(m, nat.zero), "m * 0"),
            (nat.less_eq(m, n), "m <= n"),
            (nat.less(m, n), "m < n"),
            (nat.less_eq(nat.plus(m, n), p), "m + n <= p"),
        ]

        for t, s in test_data:
            self.assertEqual(printer.print_term(t), s)

    def testReal(self):
        basic.load_theory('real')

        x = Var('x', RealType)
        y = Var('y', RealType)
        n = Var('n', NatType)
        test_data = [
            (real.plus(x, y), "x + y"),
            (real.times(x, y), "x * y"),
            (real.minus(x, y), "x - y"),
            (real.uminus(x), "-x"),
            (real.minus(x, real.uminus(y)), "x - -y"),
            (real.uminus(real.uminus(x)), "--x"),
            (real.uminus(real.minus(x, y)), "-(x - y)"),
            (real.uminus(real.nat_power(x, n)), "-(x ^ n)"),
            (real.nat_power(real.uminus(x), n), "-x ^ n"),
            (real.plus(x, real.of_nat(Nat(2))), "x + of_nat 2"),
        ]

        for t, s in test_data:
            self.assertEqual(printer.print_term(t), s)

    def testPrintBinary(self):
        m = Var("m", NatType)
        test_data = [
            (nat.one, "(1::nat)"),
            (Nat(2), "(2::nat)"),
            (Nat(3), "(3::nat)"),
            (m + 1, "m + 1"),
        ]

        for t, s in test_data:
            self.assertEqual(printer.print_term(t), s)

    def testPrintInt(self):
        basic.load_theory('int')

        m = Var("m", IntType)
        test_data = [
            (Int(0), "(0::int)"),
            (Int(1), "(1::int)"),
            (Int(2), "(2::int)"),
            (Int(3), "(3::int)"),
            (m + 1, "m + 1"),
            (Int(1) + 2, "(1::int) + 2"),
        ]

        for t, s in test_data:
            self.assertEqual(printer.print_term(t), s)

    def testPrintReal(self):
        basic.load_theory('real')

        m = Var("m", RealType)
        test_data = [
            (real.zero, "(0::real)"),
            (real.one, "(1::real)"),
            (Real(2), "(2::real)"),
            (Real(3), "(3::real)"),
            (real.plus(m, real.one), "m + 1"),
            (real.plus(real.one, Real(2)), "(1::real) + 2"),
        ]

        for t, s in test_data:
            self.assertEqual(printer.print_term(t), s)

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
            self.assertEqual(printer.print_term(t), s)

    def testPrintSet(self):
        A = Var("A", set.setT(Ta))
        B = Var("B", set.setT(Ta))
        x = Var("x", Ta)
        y = Var("y", Ta)
        P = Var("P", TFun(Ta, BoolType))
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
            self.assertEqual(printer.print_term(t), s1)
            with global_setting(unicode=True):
                self.assertEqual(printer.print_term(t), s2)

    def testPrintInterval(self):
        m = Var("m", NatType)
        n = Var("n", NatType)
        test_data = [
            (interval.mk_interval(m, n), "{m..n}"),
            (interval.mk_interval(nat.one, m), "{1..m}"),
        ]

        basic.load_theory('iterate')
        for t, s in test_data:
            self.assertEqual(printer.print_term(t), s)

    def testPrintFunction(self):
        f = Var("f", TFun(Ta, Ta))
        Tb = TVar('b')
        Tc = TVar('c')
        g = Var('g', TFun(Tb, Tc))
        h = Var('h', TFun(Ta, Tb))
        test_data = [
            (function.mk_fun_upd(f, a, b), "(f)(a := b)"),
            (function.mk_fun_upd(f, a, b, b, a), "(f)(a := b, b := a)"),
            (function.mk_comp(g, h), "g O h"),
            (function.mk_comp(g, h)(a), "(g O h) a"),
            (function.mk_const_fun(NatType, nat.zero), "%x::nat. (0::nat)"),
        ]

        basic.load_theory('function')
        for t, s in test_data:
            self.assertEqual(printer.print_term(t), s)

    def testPrintString(self):
        test_data = [
            (string.mk_char('c'), "'c'"),
            (string.mk_string("ab"), '"ab"'),
        ]

        basic.load_theory('string')
        for t, s in test_data:
            self.assertEqual(printer.print_term(t), s)

    def testPrintWithType(self):
        test_data = [
            (list.nil(Ta), "([]::'a list)"),
            (Eq(list.nil(Ta), list.nil(Ta)), "([]::'a list) = []"),
            (Forall(a, Eq(a, a)), "!a::'a. a = a"),
        ]

        for t, s in test_data:
            self.assertEqual(printer.print_term(t), s)

    def testPrintUnicode(self):
        test_data = [
            (And(A, B), "A ∧ B"),
            (Or(A, B), "A ∨ B"),
            (Implies(A, B), "A ⟶ B"),
            (Lambda(a, P(a)), "λa. P a"),
            (Forall(a, P(a)), "∀a. P a"),
            (Exists(a, P(a)), "∃a. P a"),
            (Not(A), "¬A"),
            (Lambda(m, m + 2), "λm::nat. m + 2"),
            (Lambda(m, m + n), "λm. m + n"),
        ]

        with global_setting(unicode=True):
            for t, s in test_data:
                self.assertEqual(printer.print_term(t), s)

    def testPrintHighlight(self):
        """Test highlight"""
        t = Exists(a,Forall(b,R(a,b)))
        with global_setting(highlight=True):
            res = printer.print_term(t)
        self.assertEqual(res, [
            {'color': 0, 'text': '?'},
            {'color': 1, 'text': 'a'},
            {'color': 0, 'text': '. '},
            {'color': 0, 'text': '!'},
            {'color': 1, 'text': 'b'},
            {'color': 0, 'text': '. '},
            {'color': 2, 'text': 'R'},
            {'color': 0, 'text': ' '},
            {'color': 1, 'text': 'a'},
            {'color': 0, 'text': ' '},
            {'color': 1, 'text': 'b'}
        ])

    def testPrintThmHighlight(self):
        """Test printing of theorems with highlight."""
        A = Var('A', BoolType)
        B = Var('B', BoolType)
        A_to_B = Implies(A, B)
        th = Thm([A, A_to_B], B)
        with global_setting(highlight=True):
            res = printer.print_thm(th)
        self.assertEqual(res, [
            {'color': 2, 'text': 'A'},
            {'color': 0, 'text': ', '},
            {'color': 2, 'text': 'A'},
            {'color': 0, 'text': ' '},
            {'color': 0, 'text': '-->', 'link_name': 'implies', 'link_ty': 1},
            {'color': 0, 'text': ' '},
            {'color': 2, 'text': 'B'},
            {'color': 0, 'text': ' '},
            {'color': 0, 'text': '|-'},
            {'color': 0, 'text': ' '},
            {'color': 2, 'text': 'B'}
        ])


if __name__ == "__main__":
    unittest.main()
