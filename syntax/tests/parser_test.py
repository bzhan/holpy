# Author: Bohua Zhan

import unittest

from kernel.type import TVar, Type, TFun, HOLType, hol_bool
from kernel.term import Var, Term
from kernel.thm import Thm
from kernel.proof import ProofItem
from logic import logic
from logic import nat
from logic import basic
from syntax.printer import print_term
import syntax.parser as parser

thy = basic.loadTheory('list')

Ta = TVar("a")
ctxt = {
    "A" : hol_bool,
    "B" : hol_bool,
    "C" : hol_bool,
    "P" : TFun(Ta, hol_bool),
    "Q" : TFun(Ta, hol_bool),
    "R" : TFun(Ta, Ta, hol_bool),
    "a" : Ta,
    "b" : Ta,
    "c" : Ta,
    "f" : TFun(Ta, Ta),
    "nn" : TFun(hol_bool, hol_bool),
    "m" : nat.natT,
    "n" : nat.natT,
    "p" : nat.natT,
    "xs" : Type("list", Ta),
    "ys" : Type("list", Ta),
    "zs" : Type("list", Ta),
}

A = Var("A", hol_bool)
B = Var("B", hol_bool)
C = Var("C", hol_bool)

class ParserTest(unittest.TestCase):
    def testParseType(self):
        test_data = [
            "'b",
            "nat",
            "'a list",
            "nat list",
            "('a, 'b) prod",
            "nat list list",
            "(nat, 'a) prod",
            "'a => 'b",
            "'a => 'b => 'c",
            "('a => 'b) => 'c",
            "('a => 'b) => 'c => 'd",
            "(('a => 'b) => 'c) => 'd",
            "'a => 'b list",
            "('a => 'b) list",
            "'a list list",
            "'a list => 'b list",
            "('a list => 'b) list",
            "('a => 'b, 'c) prod",
            "('a list, 'b => 'c) prod",
        ]

        for s in test_data:
            T = parser.parse_type(thy, s)
            self.assertIsInstance(T, HOLType)
            self.assertEqual(str(T), s)

    def testParseTypeIsString(self):
        a = parser.parse_type(thy, 'bool')
        self.assertEqual(type(a.name), str)

    def testParseTerm(self):
        test_data = [
            # Atoms
            ("A", "bool"),
            ("P", "'a => bool"),
            ("a", "'a"),

            # Function application
            ("P a", "bool"),
            ("R a", "'a => bool"),
            ("R a b", "bool"),
            ("f a", "'a"),
            ("P (f a)", "bool"),
            ("P (f (f a))", "bool"),
            ("R (f a) b", "bool"),
            ("R a (f b)", "bool"),

            # Abstraction
            ("%x::'a. x", "'a => 'a"),
            ("%x. P x", "'a => bool"),
            ("%x. %y. R x y", "'a => 'a => bool"),

            # Equality and implies
            ("a = b", "bool"),
            ("A --> B", "bool"),
            ("f a = b", "bool"),
            ("A --> B --> C", "bool"),
            ("(A --> B) --> C", "bool"),
            ("a = b --> C", "bool"),
            ("A = (B --> C)", "bool"),
            ("P a --> Q b", "bool"),
            ("A = B = C", "bool"),
            ("A = (B = C)", "bool"),

            # Conjunction and disjunction
            ("A & B", "bool"),
            ("A & B & C", "bool"),
            ("(A & B) & C", "bool"),
            ("A | B", "bool"),
            ("A | B | C", "bool"),
            ("(A | B) | C", "bool"),
            ("A & B | B & C", "bool"),
            ("(A | B) & (B | C)", "bool"),
            
            # Negation
            ("~A", "bool"),
            ("~~A", "bool"),

            # Constants
            ("true", "bool"),
            ("false", "bool"),

            # Mixed
            ("A --> B & C", "bool"),
            ("A | B --> C", "bool"),
            ("(A --> B) & C", "bool"),
            ("A | (B --> C)", "bool"),
            ("~A & B", "bool"),
            ("~(A & B)", "bool"),
            ("~A = B", "bool"),
            ("(~A) = B", "bool"),
            ("(~A) = (~B)", "bool"),
            ("nn (A & B)", "bool"),
            ("nn A & B", "bool"),

            # Quantifiers
            ("!x. P x", "bool"),
            ("!x. !y. R x y", "bool"),
            ("!x. P x & Q x", "bool"),
            ("(!x. P x) & Q a", "bool"),
            ("!x. P x --> Q x", "bool"),
            ("(!x. P x) --> Q a", "bool"),
            ("A = (!x. P x)", "bool"),
            ("?x. P x", "bool"),
            ("?x. !y. R x y", "bool"),
            ("!x. ?y. R x y", "bool"),
            ("!a. P a", "bool"),

            # If expression
            ("if A then a else b", "'a"),
            ("(if A then a else b) = a", "bool"),

            # Arithmetic
            ("m + n", "nat"),
            ("m * n", "nat"),
            ("m + n + p", "nat"),
            ("m + (n + p)", "nat"),
            ("m + n * p", "nat"),
            ("m * (n + p)", "nat"),
            ("0", "nat"),
            ("0 + 0", "nat"),
            ("m * 0", "nat"),

            # Binary numbers
            ("1", "nat"),
            ("2", "nat"),
            ("3", "nat"),
            ("4", "nat"),
            ("5", "nat"),
            ("101", "nat"),
            ("101 + 102", "nat"),
            ("bit0", "nat => nat"),
            ("bit1", "nat => nat"),

            # Lists
            ("xs @ ys", "'a list"),
            ("(xs @ ys) @ zs", "'a list"),
            ("xs @ ys @ zs", "'a list"),
            ("[a]", "'a list"),
            ("[a, b]", "'a list"),
            ("[a] @ [b]", "'a list"),
            ("a # xs", "'a list"),
            ("a # xs @ ys", "'a list"),
            ("(a # xs) @ ys", "'a list"),
            ("[[], [a]]", "'a list list"),
        ]

        for s, Ts in test_data:
            t = parser.parse_term(thy, ctxt, s)
            T = parser.parse_type(thy, Ts)
            self.assertIsInstance(t, Term)
            self.assertEqual(t.checked_get_type(), T)
            self.assertEqual(print_term(thy, t), s)

    def testInferType2(self):
        thy = basic.loadTheory('function')
        test_data = [
            ("fun_upd (%x. 0) 1 7", "nat => nat")
        ]

        for s, Ts in test_data:
            t = parser.parse_term(thy, ctxt, s)
            T = parser.parse_type(thy, Ts)
            self.assertIsInstance(t, Term)
            self.assertEqual(t.checked_get_type(), T)
            self.assertEqual(print_term(thy, t), s)

    def testParseTermNoAbs(self):
        test_data = [
            ("!x. P x", "bool"),
            ("!x. !y. R x y", "bool"),
            ("!x. P x & Q x", "bool"),
            ("(!x. P x) & Q a", "bool"),
            ("!x. P x --> Q x", "bool"),
            ("(!x. P x) --> Q a", "bool"),
            ("A = (!x. P x)", "bool"),
            ("?x. P x", "bool"),
            ("?x. !y. R x y", "bool"),
            ("!x. ?y. R x y", "bool"),
            ("!a. P a", "bool"),
        ]

        for s, Ts in test_data:
            t = parser.parse_term(thy, ctxt, s)
            T = parser.parse_type(thy, Ts)
            self.assertIsInstance(t, Term)
            self.assertEqual(t.checked_get_type(), T)
            self.assertEqual(print_term(thy, t), s)

    def testParseTypedTerm(self):
        test_data = [
            ("([]::'a list)", "'a list"),
            ("([]::nat list)", "nat list"),
            ("([]::'a list) = []", "bool"),
            ("!a::'a. a = a", "bool"),
        ]

        for s, Ts in test_data:
            t = parser.parse_term(thy, ctxt, s)
            T = parser.parse_type(thy, Ts)
            self.assertIsInstance(t, Term)
            self.assertEqual(t.checked_get_type(), T)
            self.assertEqual(print_term(thy, t), s)

    def testParseTermIsString(self):
        a = parser.parse_term(thy, ctxt, 'a')
        self.assertEqual(type(a.name), str)

    def testParseUnicode(self):
        test_data = [
            ("A ∧ B", "A & B"),
            ("A ∨ B", "A | B"),
            ("A ⟶ B ⟶ C", "A --> B --> C"),
            ("A ∧ B | C", "A & B | C"),
            ("¬A", "~A"),
            ("λx::'a. x", "%x::'a. x"),
            ("∀x::'a. P x", "!x. P x"),
            ("∃x::'a. P x", "?x. P x"),
            ("∀x::'a. P x ∧ Q x", "!x. P x & Q x"),
            ("(∀x::'a. P x) & Q x", "(!x. P x) & Q x"),
        ]

        for s, ascii_s in test_data:
            t = parser.parse_term(thy, ctxt, s)
            self.assertIsInstance(t, Term)
            self.assertEqual(print_term(thy, t), ascii_s)

    def testParseThm(self):
        test_data = [
            ("|- A", Thm([], A)),
            ("|- A & B", Thm([], logic.mk_conj(A, B))),
            ("A |- B", Thm([A], B)),
            ("A, B |- C", Thm([A, B], C)),
        ]

        for s, th in test_data:
            self.assertEqual(parser.parse_thm(thy, ctxt, s), th)

    def testParseProofRule(self):
        test_data = [
            ({'id': "0", 'rule': "theorem", 'args': "conjD1", 'prevs': [], 'th': ""},
             ProofItem(0, "theorem", args="conjD1", prevs=[])),
            ({'id': "2", 'rule': "implies_elim", 'args': "", 'prevs': ["1", "0"], 'th': ""},
             ProofItem(2, "implies_elim", prevs=[1, 0])),
            ({'id': "5", 'rule': "substitution", 'args': "{A: B, B: A}", 'prevs': ["4"], 'th': ""},
             ProofItem(5, "substitution", args={'A': B, 'B': A}, prevs=[4])),
            ({'id': "8", 'rule': "implies_intr", 'args': "conj A B", 'prevs': ["7"], 'th': ""},
             ProofItem(8, "implies_intr", args=logic.mk_conj(A, B), prevs=[7])),
            ({'id': "0", 'rule': "sorry", 'args': "", 'prevs': [], 'th': "conj A B |- conj B A"},
             ProofItem(0, "sorry", th=Thm([logic.mk_conj(A, B)], logic.mk_conj(B, A)))),
            ({'id': "1", 'rule': "", 'args': "", 'prevs': [], 'th': ""},
             ProofItem(1, "")),
            ({'id': "5", 'rule': "apply_theorem_for", 'args': "disjI1, {}, {A: B, B: A}", 'prevs': [4], 'th': ""},
             ProofItem(5, "apply_theorem_for", args=("disjI1", {}, {'A': B, 'B': A}), prevs=[4])),
        ]

        for s, res in test_data:
            self.assertEqual(parser.parse_proof_rule(thy, ctxt, s), res)


if __name__ == "__main__":
    unittest.main()
