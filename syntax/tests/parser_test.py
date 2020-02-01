# Author: Bohua Zhan

import unittest

from kernel.type import TVar, Type, TFun, HOLType, boolT
from kernel.term import Var, Term, And
from kernel.thm import Thm
from kernel.proof import ProofItem
from logic import logic
from data import nat
from data import int
from data import real
from logic import basic
from data import set
from syntax.printer import print_term, print_type
from syntax import parser
from logic import context


class ParserTest(unittest.TestCase):
    def testParseType(self):
        test_data = [
            "'b",
            "'?b",
            "nat",
            "'a list",
            "nat list",
            "nat list list",
            "'a => 'b",
            "'a => 'b => 'c",
            "('a => 'b) => 'c",
            "('a => 'b) => 'c => 'd",
            "(('a => 'b) => 'c) => 'd",
            "'?a => '?b",
            "'a => 'b list",
            "('a => 'b) list",
            "'a list list",
            "'a list => 'b list",
            "('a list => 'b) list",
        ]

        basic.load_theory('list')
        for s in test_data:
            T = parser.parse_type(s)
            self.assertIsInstance(T, HOLType)
            self.assertEqual(str(T), s)

    def testParseUnicodeType(self):
        test_data = [
            "'a ⇒ 'b"
        ]

        basic.load_theory('list')
        for s in test_data:
            T = parser.parse_type(s)
            self.assertIsInstance(T, HOLType)
            self.assertEqual(print_type(T, unicode=True), s)

    def testParseTypeIsString(self):
        basic.load_theory('logic_base')
        a = parser.parse_type('bool')
        self.assertEqual(type(a.name), str)

    def run_test(self, thy_name, *, vars=None, svars=None, s, Ts, unicode=False):
        context.set_context(thy_name, vars=vars, svars=svars)

        t = parser.parse_term(s)
        T = parser.parse_type(Ts)
        self.assertIsInstance(t, Term)
        self.assertEqual(t.checked_get_type(), T)
        self.assertEqual(print_term(t, unicode=unicode), s)

    def testParseTerm(self):
        test_data = [
            # Atoms
            ("A", "bool"),
            ("P", "'a => bool"),
            ("a", "'a"),
            ("?P", "bool"),

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
            ("A <--> B --> C", "bool"),
            ("P a --> Q b", "bool"),
            ("(A <--> B) <--> C", "bool"),
            ("A <--> B <--> C", "bool"),

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
            ("~(A <--> B)", "bool"),
            ("~A <--> B", "bool"),
            ("~A <--> ~B", "bool"),
            ("nn (A & B)", "bool"),
            ("nn A & B", "bool"),

            # Quantifiers
            ("!x. P x", "bool"),
            ("!x. !y. R x y", "bool"),
            ("!x. P x & Q x", "bool"),
            ("(!x. P x) & Q a", "bool"),
            ("!x. P x --> Q x", "bool"),
            ("(!x. P x) --> Q a", "bool"),
            ("A <--> (!x. P x)", "bool"),
            ("?x. P x", "bool"),
            ("?x. !y. R x y", "bool"),
            ("!x. ?y. R x y", "bool"),
            ("!a. P a", "bool"),
            ("?!a. P a", "bool"),
            ("THE a. P a", "'a"),
            ("A --> B <--> C", "bool"),
            ("(A --> B) <--> C", "bool"),

            # If expression
            ("if A then a else b", "'a"),
            ("(if A then a else b) = a", "bool"),

            # Arithmetic
            ("m + n", "nat"),
            ("m * n", "nat"),
            ("m + n + p", "nat"),
            ("m + (n + p)", "nat"),
            ("m - n + p", "nat"),
            ("m - (n + p)", "nat"),
            ("m + n * p", "nat"),
            ("m * (n + p)", "nat"),
            ("(0::nat)", "nat"),
            ("(0::nat) + 0", "nat"),
            ("m * 0", "nat"),

            # Ordering on natural numbers
            ("m <= n", "bool"),
            ("m < n", "bool"),
            ("m + n <= p", "bool"),

            # Binary numbers
            ("(1::nat)", "nat"),
            ("(2::nat)", "nat"),
            ("(3::nat)", "nat"),
            ("(4::nat)", "nat"),
            ("(5::nat)", "nat"),
            ("(101::nat)", "nat"),
            ("(101::nat) + 102", "nat"),
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

        vars = {'A': 'bool', 'B': 'bool', 'C': 'bool', 'P': "'a => bool", 'Q': "'a => bool",
                'R': "'a => 'a => bool", 'a': "'a", 'b': "'a", 'c': "'a",
                'f': "'a => 'a", 'nn': "bool => bool", 'm': "nat", 'n': "nat", 'p': "nat",
                'xs': "'a list", 'ys': "'a list", 'zs': "'a list"}
        svars = {'P': 'bool'}

        for s, Ts in test_data:
            self.run_test('list', vars=vars, svars=svars, s=s, Ts=Ts)

    def testParseInt(self):
        test_data = [
            ("x + y", "int"),
            ("x * y", "int"),
            ("x - y", "int"),
            ("-x", "int"),
            ("x - -y", "int"),
            ("--x", "int"),
            ("-(x - y)", "int"),
            ("(0::int)", "int"),
            ("(1::int)", "int"),
            ("(2::int)", "int"),
            ("x + 1", "int"),
            ("(1::int) + 2", "int"),
        ]

        vars = {'x': 'int', 'y': 'int'}
        for s, Ts in test_data:
            self.run_test('int', vars=vars, s=s, Ts=Ts)

    def testParseReal(self):
        test_data = [
            ("x + y", "real"),
            ("x * y", "real"),
            ("x - y", "real"),
            ("-x", "real"),
            ("x - -y", "real"),
            ("--x", "real"),
            ("-(x - y)", "real"),
            ("(0::real)", "real"),
            ("(1::real)", "real"),
            ("(2::real)", "real"),
            ("x + 1", "real"),
            ("x ^ n", "real"),
            ("-(x ^ n)", "real"),
            ("-x ^ n", "real"),
            ("(1::real) + 2", "real"),
            ("(2::real) + 1", "real"),
            ("[(2::real), 3]", "real list"),
            ("{(2::real), 3}", "real set"),
            ("{(2::real), 3} Un {4, 5}", "real set"),
            ("{t::real. abs t <= 1}", "real set"),
        ]

        vars = {'x': 'real', 'y': 'real', 'n': 'nat'}
        for s, Ts in test_data:
            self.run_test('real', vars=vars, s=s, Ts=Ts)

    def testParseFunction(self):
        test_data = [
            ("(f)(a := b)", "'a => 'a"),
            ("(f)(a := b, b := a)", "'a => 'a"),
            ("g O h", "'a => 'c"),
            ("(g O h) a", "'c"),
        ]

        vars = {'a': "'a", 'b': "'a", 'f': "'a => 'a", 'g': "'b => 'c", 'h': "'a => 'b"}
        for s, Ts in test_data:
            self.run_test('function', vars=vars, s=s, Ts=Ts)

    def testParseSet(self):
        test_data = [
            ("({}::'a set)", "(∅::'a set)", "'a set"),
            ("x Mem A", "x ∈ A", "bool"),
            ("A Sub B", "A ⊆ B", "bool"),
            ("A Int B", "A ∩ B", "'a set"),
            ("A Un B", "A ∪ B", "'a set"),
            ("{x}", "{x}", "'a set"),
            ("{x, y}", "{x, y}", "'a set"),
            ("insert x A", "insert x A", "'a set"),
            ("{x. P x}", "{x. P x}", "'a set"),
            ("collect P", "collect P", "'a set"),
            ("UN S", "⋃S", "'a set"),
            ("INT S", "⋂S", "'a set"),
            ("INT (image f S)", "⋂(image f S)", "'a set"),
            ("f (INT S)", "f (⋃S)", "'a set")
        ]

        vars = {"x": "'a", "y": "'a", "A": "'a set", "B": "'a set",
                "P": "'a => bool", "S": "'a set set", "f": "'a set => 'a set"}
        for s1, s2, Ts in test_data:
            self.run_test('set', vars=vars, s=s1, Ts=Ts)
            self.run_test('set', vars=vars, s=s2, Ts=Ts, unicode=True)

    def testParseString(self):
        test_data = [
            ("'a'", "char"),
            ('"ab"', "string"),
        ]

        for s, Ts in test_data:
            self.run_test('string', s=s, Ts=Ts)

    def testParseInterval(self):
        test_data = [
            ("{m..n}", "nat set"),
            ("{1..m}", "nat set"),
        ]

        vars = {'m': 'nat', 'n': 'nat'}
        for s, Ts in test_data:
            self.run_test('iterate', vars=vars, s=s, Ts=Ts)

    def testInferType2(self):
        test_data = [
            ("%x::nat. (0::nat)", "nat => nat"),
            ("(%x::nat. (0::nat))(1 := 7)", "nat => nat")
        ]

        for s, Ts in test_data:
            self.run_test('function', s=s, Ts=Ts)

    def testParseTermNoAbs(self):
        test_data = [
            ("!x. P x", "bool"),
            ("!x. !y. R x y", "bool"),
            ("!x. P x & Q x", "bool"),
            ("(!x. P x) & Q a", "bool"),
            ("!x. P x --> Q x", "bool"),
            ("(!x. P x) --> Q a", "bool"),
            ("A <--> (!x. P x)", "bool"),
            ("?x. P x", "bool"),
            ("?x. !y. R x y", "bool"),
            ("!x. ?y. R x y", "bool"),
            ("!a. P a", "bool"),
        ]

        vars = {'P': "'a => bool", 'Q': "'a => bool", 'R': "'a => 'a => bool"}
        for s, Ts in test_data:
            self.run_test('logic_base', vars=vars, s=s, Ts=Ts)

    def testParseTypedTerm(self):
        test_data = [
            ("([]::'a list)", "'a list"),
            ("([]::nat list)", "nat list"),
            ("([]::'a list) = []", "bool"),
            ("!a::'a. a = a", "bool"),
        ]

        for s, Ts in test_data:
            self.run_test('list', s=s, Ts=Ts)

    def testParseTermIsString(self):
        context.set_context('logic_base', vars={'a': "'a"})
        a = parser.parse_term('a')
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
            ("(∀x::'a. P x) & Q y", "(!x. P x) & Q y"),
        ]

        context.set_context('logic_base',
            vars={'A': 'bool', 'B': 'bool', 'C': 'bool', 'P': "'a => bool", 'Q': "'a => bool"})
        for s, ascii_s in test_data:
            t = parser.parse_term(s)
            self.assertIsInstance(t, Term)
            self.assertEqual(print_term(t), ascii_s)

    def testParseThm(self):
        A = Var('A', boolT)
        B = Var('B', boolT)
        C = Var('C', boolT)
        test_data = [
            ("|- A", Thm([], A)),
            ("|- A & B", Thm([], And(A, B))),
            ("A |- B", Thm([A], B)),
            ("A, B |- C", Thm([A, B], C)),
        ]

        context.set_context('logic', vars={'A': 'bool', 'B': 'bool', 'C': 'bool'})
        for s, th in test_data:
            self.assertEqual(parser.parse_thm(s), th)

    def testParseProofRule(self):
        A = Var('A', boolT)
        B = Var('B', boolT)
        test_data = [
            ({'id': "0", 'rule': "theorem", 'args': "conjD1", 'prevs': [], 'th': ""},
             ProofItem(0, "theorem", args="conjD1", prevs=[])),
            ({'id': "2", 'rule': "implies_elim", 'args': "", 'prevs': ["1", "0"], 'th': ""},
             ProofItem(2, "implies_elim", prevs=[1, 0])),
            ({'id': "5", 'rule': "substitution", 'args': "{A: B, B: A}", 'prevs': ["4"], 'th': ""},
             ProofItem(5, "substitution", args={'A': B, 'B': A}, prevs=[4])),
            ({'id': "8", 'rule': "implies_intr", 'args': "conj A B", 'prevs': ["7"], 'th': ""},
             ProofItem(8, "implies_intr", args=And(A, B), prevs=[7])),
            ({'id': "0", 'rule': "sorry", 'args': "", 'prevs': [], 'th': "conj A B |- conj B A"},
             ProofItem(0, "sorry", th=Thm([And(A, B)], And(B, A)))),
            ({'id': "1", 'rule': "", 'args': "", 'prevs': [], 'th': ""},
             ProofItem(1, "")),
            ({'id': "5", 'rule': "apply_theorem_for", 'args': "disjI1, {}, {A: B, B: A}", 'prevs': [4], 'th': ""},
             ProofItem(5, "apply_theorem_for", args=("disjI1", {}, {'A': B, 'B': A}), prevs=[4])),
        ]

        context.set_context('logic_base', vars={'A': 'bool', 'B': 'bool'})
        for s, res in test_data:
            self.assertEqual(parser.parse_proof_rule(s), res)

    def testParseTypeInd(self):
        test_data = [
            ("cons (x ::'a) (xs ::'a list)",
             {'name': 'cons', 'type': [TVar('a'), Type('list', TVar('a'))], 'args': ['x', 'xs']}),
        ]

        basic.load_theory('list')
        for s, res in test_data:
            self.assertEqual(parser.parse_ind_constr(s), res)

    def testParseNamedThm(self):
        A = Var('A', boolT)
        B = Var('B', boolT)
        test_data = [
            ("conjI: A = B", ('conjI', Term.mk_equals(A, B))),
            ("A = B", (None, Term.mk_equals(A, B)))
        ]

        context.set_context('logic_base', vars={'A': 'bool', 'B': 'bool'})
        for s, res in test_data:
            self.assertEqual(parser.parse_named_thm(s), res)


if __name__ == "__main__":
    unittest.main()
