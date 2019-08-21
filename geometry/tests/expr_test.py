"""Unit test for expressions."""

import unittest

from geometry import expr
from geometry.expr import Fact, Rule
from geometry import parser
from geometry.ruleset import ruleset


class ExprTest(unittest.TestCase):
    def testPrintExpr(self):
        test_data = [
            (Fact("coll", ["A", "B", "C"]), "coll(A,B,C)"),
        ]

        for f, s in test_data:
            self.assertEqual(str(f), s)

    def testPrintRule(self):
        test_data = [
            (Rule([Fact("coll", ["A", "B", "C"])], Fact("coll", ["A", "C", "B"])),
             "coll(A,C,B) :- coll(A,B,C)"),
        ]
        
        for r, s in test_data:
            self.assertEqual(str(r), s)

    def testMatchFact(self):
        test_data = [
            ("coll(A,B,C)", "coll(P,Q,R)", {}, {"A": "P", "B": "Q", "C": "R"}),
            ("coll(A,B,C)", "coll(P,Q,R)", {"A": "P"}, {"A": "P", "B": "Q", "C": "R"}),
            ("coll(A,B,C)", "coll(P,Q,R)", {"A": "Q"}, None),
            ("coll(A,B,C)", "para(P,Q,R,S)", {}, None),
        ]

        for pat, f, inst, res in test_data:
            pat = parser.parse_fact(pat)
            f = parser.parse_fact(f)
            if res is not None:
                expr.match_expr(pat, f, inst)
                self.assertEqual(inst, res)
            else:
                self.assertRaises(expr.MatchException, expr.match_expr, pat, f, inst)

    def testApplyRule1(self):
        fact = parser.parse_fact("coll(P,Q,R)")
        rule = ruleset["D1"]
        concl = parser.parse_fact("coll(P,R,Q)")
        self.assertEqual(expr.apply_rule(rule, [fact]), concl)


if __name__ == "__main__":
    unittest.main()
