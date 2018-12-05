# Author: Bohua Zhan

import unittest

from kernel.type import TVar, TFun, HOLType, hol_bool
from kernel.term import Var, Term
from kernel.thm import Thm
from kernel.proof import ProofItem
from logic.logic import Logic
from logic.nat import Nat
from logic.basic import BasicTheory
from syntax.printer import print_term
import syntax.parser as parser

thy = BasicTheory()

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
    "m" : Nat.nat,
    "n" : Nat.nat,
    "p" : Nat.nat,
}

A = Var("A", hol_bool)
B = Var("B", hol_bool)
C = Var("C", hol_bool)

class ParserTest(unittest.TestCase):
    def testParseType(self):
        parse = parser.type_parser(thy).parse

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
            T = parse(s)
            self.assertIsInstance(T, HOLType)
            self.assertEqual(str(T), s)

    def testParseTerm(self):
        parse = parser.term_parser(thy, ctxt).parse
        parseT = parser.type_parser(thy).parse

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

            # Arithmetic
            ("m + n", "nat"),
            ("m * n", "nat"),
            ("m + n + p", "nat"),
            ("m + (n + p)", "nat"),
            ("m + n * p", "nat"),
            ("m * (n + p)", "nat"),
        ]

        for s, Ts in test_data:
            t = parse(s)
            T = parseT(Ts)
            self.assertIsInstance(t, Term)
            self.assertEqual(t.checked_get_type(), T)
            self.assertEqual(print_term(thy, t, print_abs_type=True), s)

    def testParseUnicode(self):
        parse = parser.term_parser(thy, ctxt).parse
        test_data = [
            ("A ∧ B", "A & B"),
            ("A ∨ B", "A | B"),
            ("A ⟶ B ⟶ C", "A --> B --> C"),
            ("A ∧ B | C", "A & B | C"),
            ("¬A", "~A"),
            ("λx::'a. x", "%x. x"),
            ("∀x::'a. x", "!x. x"),
            ("∀x::'a. P x ∧ Q x", "!x. P x & Q x"),
            ("(∀x::'a. P x) & Q x", "(!x. P x) & Q x"),
            ("∃x::'a. x", "?x. x"),
        ]

        for s, ascii_s in test_data:
            t = parse(s)
            self.assertIsInstance(t, Term)
            self.assertEqual(print_term(thy, t), ascii_s)

    def testParseThm(self):
        parse_thm = parser.thm_parser(thy, ctxt).parse

        test_data = [
            ("|- A", Thm([], A)),
            ("|- A & B", Thm([], Logic.mk_conj(A, B))),
            ("A |- B", Thm([A], B)),
            ("A, B |- C", Thm([A, B], C)),
        ]

        for s, th in test_data:
            self.assertEqual(parse_thm(s), th)

    def testSplitProofRule(self):
        test_data = [
            ("S1: theorem conjD1", ("S1", "theorem", "conjD1", [], "")),
            ("S2: implies_elim from S1, A1", ("S2", "implies_elim", "", ["S1", "A1"], "")),
            ("S6: substitution {'A': B, 'B': A} from S5", ("S6", "substitution", "{'A': B, 'B': A}", ["S5"], "")),
            ("S9: implies_intr conj A B from S8", ("S9", "implies_intr", "conj A B", ["S8"], "")),
            ("S1: conj A B |- conj B A by sorry", ("S1", "sorry", "", [], "conj A B |- conj B A")),
            ("S2: ", ("S2", "", "", [], "")),
        ]

        for s, res in test_data:
            self.assertEqual(parser.split_proof_rule(s), res)

    def testParseProofRule(self):
        test_data = [
            ("S1: theorem conjD1", ProofItem("S1", "theorem", args = "conjD1", prevs = [])),
            ("S2: implies_elim from S1, A1", ProofItem("S2", "implies_elim", prevs = ["S1", "A1"])),
            ("S6: substitution {A: B, B: A} from S5", ProofItem(
                "S6", "substitution", args = {'A': B, 'B': A}, prevs = ["S5"])),
            ("S9: implies_intr conj A B from S8", ProofItem(
                "S9", "implies_intr", args = Logic.mk_conj(A, B), prevs = ["S8"])),
            ("S1: conj A B |- conj B A by sorry", ProofItem(
                "S1", "sorry", th = Thm([Logic.mk_conj(A, B)], Logic.mk_conj(B, A)))),
            ("S2: ", ProofItem("S2", "")),
            ("S1: apply_theorem_for conjI, {A: B, B: A} from S1, S2", ProofItem(
                "S1", "apply_theorem_for", args = ("conjI", {'A': B, 'B': A}), prevs = ["S1", "S2"])),
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
