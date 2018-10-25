# Author: Bohua Zhan

import unittest

from kernel.type import TVar, TFun, HOLType, hol_bool
from kernel.term import Term
from logic.basic import BasicTheory
from syntax.printer import print_term
from syntax.parser import type_parser, term_parser

thy = BasicTheory()

ctxt = {
    "A" : hol_bool,
    "B" : hol_bool,
    "C" : hol_bool,
    "P" : TFun(TVar("a"), hol_bool),
    "Q" : TFun(TVar("a"), hol_bool),
    "P2" : TFun(TVar("a"), TVar("a"), hol_bool),
    "a" : TVar("a"),
    "b" : TVar("a"),
    "c" : TVar("a"),
    "f" : TFun(TVar("a"), TVar("a"))
}

class ParserTest(unittest.TestCase):
    def testParseType(self):
        parse = type_parser(thy).parse

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
        parse = term_parser(thy, ctxt).parse
        parseT = type_parser(thy).parse

        test_data = [
            # Atoms
            ("A", "bool"),
            ("P", "'a => bool"),
            ("a", "'a"),

            # Function application
            ("P a", "bool"),
            ("P2 a", "'a => bool"),
            ("P2 a b", "bool"),
            ("f a", "'a"),
            ("P (f a)", "bool"),
            ("P (f (f a))", "bool"),
            ("P2 (f a) b", "bool"),
            ("P2 a (f b)", "bool"),

            # Abstraction
            ("%x::'a. x", "'a => 'a"),
            ("%x::'a. P x", "'a => bool"),
            ("%x::'a. %y::'a. P2 x y", "'a => 'a => bool"),

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
            
            # Mixed
            ("A --> B & C", "bool"),
            ("A | B --> C", "bool"),
            ("(A --> B) & C", "bool"),
            ("A | (B --> C)", "bool"),
        ]

        for (s, Ts) in test_data:
            t = parse(s)
            T = parseT(Ts)
            self.assertIsInstance(t, Term)
            self.assertEqual(t.checked_get_type(), T)
            self.assertEqual(print_term(thy, t, print_abs_type=True), s)

if __name__ == "__main__":
    unittest.main()
