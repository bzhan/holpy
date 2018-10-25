# Author: Bohua Zhan

import unittest

from kernel.type import TVar, TFun, HOLType, hol_bool
from kernel.term import Term
from kernel.theory import Theory
from syntax.parser import type_parser, term_parser

thy = Theory.EmptyTheory()
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
            ("A", "bool"),
            ("P", "'a => bool"),
            ("a", "'a"),
            ("P a", "bool"),
            ("P2 a", "'a => bool"),
            ("P2 a b", "bool"),
            ("f a", "'a"),
            ("P (f a)", "bool"),
            ("P (f (f a))", "bool"),
            ("P2 (f a) b", "bool"),
            ("P2 a (f b)", "bool"),
            ("%x::'a. x", "'a => 'a"),
            ("%x::'a. P x", "'a => bool"),
            ("%x::'a. %y::'a. P2 x y", "'a => 'a => bool"),
        ]

        test_data2 = [
            ("a = b", "bool", "equals a b"),
            ("A --> B", "bool", "implies A B"),
            ("f a = b", "bool", "equals (f a) b"),
            ("A --> B --> C", "bool", "implies A (implies B C)"),
            ("(A --> B) --> C", "bool", "implies (implies A B) C"),
            ("a = b --> C", "bool", "implies (equals a b) C"),
            ("A = (B --> C)", "bool", "equals A (implies B C)"),
            ("P a --> Q b", "bool", "implies (P a) (Q b)"),
        ]

        for (s, Ts) in test_data:
            t = parse(s)
            T = parseT(Ts)
            self.assertIsInstance(t, Term)
            self.assertEqual(t.checked_get_type(), T)
            self.assertEqual(t.repr_with_abs_type(), s)

        for (s, Ts, repr_s) in test_data2:
            t = parse(s)
            T = parseT(Ts)
            self.assertIsInstance(t, Term)
            self.assertEqual(t.checked_get_type(), T)
            self.assertEqual(t.repr_with_abs_type(), repr_s)

if __name__ == "__main__":
    unittest.main()
