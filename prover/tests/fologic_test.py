"""Unit test for fologic."""

import unittest

from kernel.type import BoolType, TFun, TVar
from logic import basic
from syntax import parser
from logic import context
from prover import fologic


class FOLogicTest(unittest.TestCase):
    def testHasBound0(self):
        test_data = [
            ("%y::'a. !x::'a. y = y", True),
            ("%x::'a. y = y", False)
        ]

        context.set_context('logic', vars={'y': "'a"})
        for fm, res in test_data:
            fm = parser.parse_term(fm)
            self.assertEqual(fologic.has_bound0(fm.body), res)

    def testSimplify(self):
        test_data = [
            # Three test cases Section 3.5 of HPLAR.
            ("true --> (p <--> (p <--> false))", "p <--> ~p"),
            ("?x. ?y::'a. ?z. P x --> Q z --> false", "?x. ?z. P x --> ~Q z"),
            ("(!x. !y. P x | (P y & false)) --> ?z::'a. q", "(!x. P x) --> q")
        ]

        context.set_context('logic', vars={'p': 'bool', 'q': 'bool', 'P': "'a => bool", 'Q': "'a => bool"})
        for fm, res in test_data:
            fm = parser.parse_term(fm)
            res = parser.parse_term(res)
            self.assertEqual(fologic.simplify(fm), res)

    def testNNF(self):
        test_data = [
            # Test case from Section 3.5 of HPLAR.
            ("(!x. P x) --> ((?y. Q y) <--> ?z. P z & Q z)",
             "(?x. ~P x) | (?y. Q y) & (?z. P z & Q z) | (!y. ~Q y) & (!z. ~P z | ~Q z)")
        ]

        context.set_context('logic', vars={'P': "'a => bool", 'Q': "'a => bool"})
        for fm, res in test_data:
            fm = parser.parse_term(fm)
            res = parser.parse_term(res)
            self.assertEqual(fologic.nnf(fm), res)

    def testASKolem(self):
        test_data = [
            # Test case from Section 3.6 of HPLAR.
            ("?y::nat. x < y --> !u. ?v. x * u < y * v",
             "~x < f_y x | (!u::nat. x * u < f_y x * f_v u x)"),
            ("!x. P x --> (?y. ?z::'a. Q y | ~(?z. P z & Q z))",
             "!x. ~P x | Q c_y | (!z. ~P z | ~Q z)")
        ]

        context.set_context('nat', vars={'P': "'a => bool", 'Q': "'a => bool"})
        for fm, res in test_data:
            fm = parser.parse_term(fm)
            res = parser.parse_term(res)
            self.assertEqual(fologic.askolemize(fm), res)


if __name__ == "__main__":
    unittest.main()
