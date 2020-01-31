"""Unit test for items module."""

import unittest

from kernel import theory
from logic import basic
from server import items
from syntax import printer


class ItemsTest(unittest.TestCase):
    def testDatatypeNat(self):
        basic.load_theory('logic_base')
        nat_item = items.parse_item({
            "args": [],
            "constrs": [
                {"args": [], "name": "zero", "type": "nat"},
                {"args": ["n"], "name": "Suc", "type": "nat => nat"}
            ],
            "name": "nat",
            "ty": "type.ind"
        })
        self.assertIsNone(nat_item.error)
        ext = nat_item.get_extension()
        theory.thy.unchecked_extend(ext)
        ext_output = [
            "Type nat 0",
            "Constant zero :: nat",
            "Constant Suc :: nat => nat",
            "Theorem nat_zero_Suc_neq: ~(0 = Suc n)",
            "Theorem nat_Suc_inject: Suc n = Suc n1 --> n = n1",
            "Theorem nat_induct: P 0 --> (!n. P n --> P (Suc n)) --> P x",
            "Attribute nat_induct [var_induct]"
        ]
        self.assertEqual(printer.print_extensions(ext), '\n'.join(ext_output))

    def testDatatypeList(self):
        basic.load_theory('logic_base')
        list_item = items.parse_item({
            "args": ["a"],
            "constrs": [
                {"args": [], "name": "nil", "type": "'a list"},
                {"args": ["x", "xs"], "name": "cons", "type": "'a => 'a list => 'a list"}
            ],
            "name": "list",
            "ty": "type.ind"
        })
        self.assertIsNone(list_item.error)
        ext = list_item.get_extension()
        theory.thy.unchecked_extend(ext)
        ext_output = [
            "Type list 1",
            "Constant nil :: 'a list",
            "Constant cons :: 'a => 'a list => 'a list",
            "Theorem list_nil_cons_neq: ~([] = x # xs)",
            "Theorem list_cons_inject: x # xs = x1 # xs1 --> x = x1 & xs = xs1",
            "Theorem list_induct: P [] --> (!x1. !xs. P xs --> P (x1 # xs)) --> P x",
            "Attribute list_induct [var_induct]"
        ]
        self.assertEqual(printer.print_extensions(ext), '\n'.join(ext_output))

    def testDatatypeProd(self):
        basic.load_theory('logic_base')
        prod_item = items.parse_item({
            "args": ["a", "b"],
            "constrs": [
                {"args": ["a", "b"], "name": "Pair", "type": "'a => 'b => ('a, 'b) prod"}
            ],
            "name": "prod",
            "ty": "type.ind"
        })
        self.assertIsNone(prod_item.error)
        ext = prod_item.get_extension()
        theory.thy.unchecked_extend(ext)
        ext_output = [
            "Type prod 2",
            "Constant Pair :: 'a => 'b => ('a, 'b) prod",
            "Theorem prod_Pair_inject: Pair a b = Pair a1 b1 --> a = a1 & b = b1",
            "Theorem prod_induct: (!a. !b. P (Pair a b)) --> P x",
            "Attribute prod_induct [var_induct]"
        ]
        self.assertEqual(printer.print_extensions(ext), '\n'.join(ext_output))

    def testFunPlus(self):
        basic.load_theory('nat', limit=('def', 'one'))
        plus_item = items.parse_item({
            "name": "plus",
            "rules": [
                {"prop": "0 + n = n"},
                {"prop": "Suc m + n = Suc (m + n)"}
            ],
            "ty": "def.ind",
            "type": "nat ⇒ nat ⇒ nat"
        })
        self.assertIsNone(plus_item.error)
        ext = plus_item.get_extension()
        theory.thy.unchecked_extend(ext)
        ext_output = [
            "Constant plus :: nat => nat => nat",
            "Theorem plus_def_1: 0 + n = n",
            "Attribute plus_def_1 [hint_rewrite]",
            "Theorem plus_def_2: Suc m + n = Suc (m + n)",
            "Attribute plus_def_2 [hint_rewrite]"
        ]
        self.assertEqual(printer.print_extensions(ext), '\n'.join(ext_output))

    def testPredEven(self):
        basic.load_theory('nat', limit=('def', 'one'))
        even_item = items.parse_item({
            "name": "even",
            "rules": [
                {"name": "even_zero", "prop": "even 0"},
                {"name": "even_Suc", "prop": "even n --> even (Suc (Suc n))"}
            ],
            "ty": "def.pred",
            "type": "nat => bool"
        })
        self.assertIsNone(even_item.error)
        ext = even_item.get_extension()
        theory.thy.unchecked_extend(ext)
        ext_output = [
            "Constant even :: nat => bool",
            "Theorem even_zero: even 0",
            "Attribute even_zero [hint_backward]",
            "Theorem even_Suc: even n --> even (Suc (Suc n))",
            "Attribute even_Suc [hint_backward]",
            "Theorem even_cases: even _a1 --> (_a1 = 0 --> P) --> (!n. _a1 = Suc (Suc n) --> even n --> P) --> P"
        ]
        self.assertEqual(printer.print_extensions(ext), '\n'.join(ext_output))


if __name__ == "__main__":
    unittest.main()
