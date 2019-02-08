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
            ("%x::'a. P x", "'a => bool"),
            ("%x::'a. %y::'a. R x y", "'a => 'a => bool"),

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
            ("!x::'a. P x", "bool"),
            ("!x::'a. !y::'a. R x y", "bool"),
            ("!x::'a. P x & Q x", "bool"),
            ("(!x::'a. P x) & Q a", "bool"),
            ("!x::'a. P x --> Q x", "bool"),
            ("(!x::'a. P x) --> Q a", "bool"),
            ("A = (!x::'a. P x)", "bool"),
            ("?x::'a. P x", "bool"),
            ("?x::'a. !y::'a. R x y", "bool"),
            ("!x::'a. ?y::'a. R x y", "bool"),
            ("!a::'a. P a", "bool"),

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
            # ("[]", "'a list"),
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
            self.assertEqual(print_term(thy, t, print_abs_type=True), s)

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
            ("λx::'a. x", "%x. x"),
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

    def testSplitProofRule(self):
        test_data = [
            ("S1: theorem conjD1",
             {'id': "S1", 'rule': "theorem", 'args': "conjD1", 'prevs': [], 'th': ""}),
            ("S2: implies_elim from S1, A1",
             {'id': "S2", 'rule': "implies_elim", 'args': "", 'prevs': ["S1", "A1"], 'th': ""}),
            ("S6: substitution {'A': B, 'B': A} from S5",
             {'id': "S6", 'rule': "substitution", 'args': "{'A': B, 'B': A}", 'prevs': ["S5"], 'th': ""}),
            ("S9: implies_intr conj A B from S8",
             {'id': "S9", 'rule': "implies_intr", 'args': "conj A B", 'prevs': ["S8"], 'th': ""}),
            ("S1: conj A B |- conj B A by sorry",
             {'id': "S1", 'rule': "sorry", 'args': "", 'prevs': [], 'th': "conj A B |- conj B A"}),
            ("S2: ",
             {'id': "S2", 'rule': "", 'args': "", 'prevs': [], 'th': ""}),
        ]

        for s, res in test_data:
            self.assertEqual(parser.split_proof_rule(s), res)

    def testParseProofRule(self):
        test_data = [
            ("S1: theorem conjD1", ProofItem("S1", "theorem", args="conjD1", prevs=[])),
            ("S2: implies_elim from S1, A1", ProofItem("S2", "implies_elim", prevs=["S1", "A1"])),
            ("S6: substitution {A: B, B: A} from S5", ProofItem(
                "S6", "substitution", args={'A': B, 'B': A}, prevs=["S5"])),
            ("S9: implies_intr conj A B from S8", ProofItem(
                "S9", "implies_intr", args=logic.mk_conj(A, B), prevs=["S8"])),
            ("S1: conj A B |- conj B A by sorry", ProofItem(
                "S1", "sorry", th = Thm([logic.mk_conj(A, B)], logic.mk_conj(B, A)))),
            ("S2: ", ProofItem("S2", "")),
            ("S1: apply_theorem_for conjI, {A: B, B: A} from S1, S2", ProofItem(
                "S1", "apply_theorem_for", args=("conjI", {'A': B, 'B': A}), prevs=["S1", "S2"])),
        ]

        for s, res in test_data:
            self.assertEqual(parser.parse_proof_rule(thy, ctxt, s), res)

    def testParseProofFail(self):
        test_data = [
            ("", "id not found"),
            ("S1: assume A &", "When parsing A &, unexpected token"),
        ]

        for s, err in test_data:
            self.assertRaisesRegex(parser.ParserException, err, parser.parse_proof_rule, thy, ctxt, s)

if __name__ == "__main__":
    unittest.main()
