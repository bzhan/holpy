import unittest
from syntax.parser import parse_term
from logic import context
from prover import simplex_strict
from kernel.term import false

class StrictSimplexTest(unittest.TestCase):
    def testStrict(self):
        test_data = [
            ("x_1 < 9", "x_1 >= 10"),
            ("x_1 >= 10", "x_1 + -1 * x_2 <= 0", "x_2 < 9"),
            ("x_1 + -1 * x_2 <= 0", "x_3 + -1 * x_1 <= 0", "x_4 >= 10", "x_4 + -1 * x_3 <= 0", "x_2 < 9"),
            ("x_1 + -1 * x_2 <= 0", "x_3 >= 10", "x_3 + -1 * x_1 <= 0", "x_2 < 9"),
        ]

        context.set_context("real", vars= {"x_1" : "real", "x_2": "real", "x_3": "real", "x_4": "real"})

        for tableau in test_data:
            tableau = [parse_term(tm) for tm in tableau]
            pt = simplex_strict.SimplexMacro().get_proof_term(args=tableau)
            self.assertNotEqual(pt.rule, "sorry")
            self.assertEqual(pt.prop, false)

        