"""Unit test for expressions."""

import unittest

from geometry import expr
from geometry.expr import Fact, Rule, Line
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

    def testMatchFactLines(self):
        lines = [Line(["O", "P", "Q"])]
        test_data = [
            ("perp(l, m)", "perp(P, Q, R, S)", {}, {"l": ("P", "Q"), "m": ("R", "S")}),
            ("perp(l, m)", "perp(P, Q, R, S)", {"l": ("Q", "P")}, {"l": ("Q", "P"), "m": ("R", "S")}),
            ("perp(l, m)", "perp(P, Q, R, S)", {"l": ("O", "P")}, {"l": ("O", "P"), "m": ("R", "S")}),
            ("perp(l, m)", "perp(P, Q, R, S)", {"l": ("A", "P")}, None),
        ]

        for pat, f, inst, res in test_data:
            pat = parser.parse_fact(pat)
            f = parser.parse_fact(f)
            if res is not None:
                expr.match_expr(pat, f, inst, lines=lines)
                self.assertEqual(inst, res)
            else:
                self.assertRaises(expr.MatchException, expr.match_expr, pat, f, inst, lines=lines)

    def testApplyRule(self):
        test_data = [
            (ruleset["D1"], ["coll(E, F, G)", "coll(P, Q, R)"], "coll(E, G, F)"),
        ]

        for rule, facts, concl in test_data:
            facts = [parser.parse_fact(fact) for fact in facts]
            concl = parser.parse_fact(concl)
            self.assertEqual(expr.apply_rule(rule, facts), concl)

    def testMakeLineFacts(self):
        test_data = [
            (["coll(A, B, C)", "coll(A, B, D)", "coll(P, Q, R)", "coll(R, S, T)", "coll(Q, R, S)"],
             ["line(A, B, C, D)", "line(P, Q, R, S, T)"]),
        ]
        for facts, concls in test_data:
            facts = [parser.parse_fact(fact) for fact in facts]
            line_facts = expr.make_line_facts(facts)
            concls = [parser.parse_line(line) for line in concls]
            self.assertEqual(set(line_facts), set(concls))

    def testApplyRuleHyps(self):
        test_data = [
            (ruleset["D3"], ["coll(E, F, G)", "coll(E, F, H)", "coll(P, Q, R)", "coll(P, Q, S)", "coll(A, B, C)"],
             ["coll(G, H, E)", "coll(H, G, E)", "coll(R, S, P)", "coll(S, R, P)"]),

            (ruleset["D5"], ["para(P, Q, R, S)"],
             ["para(R, S, P, Q)"]),

            (ruleset["D6"], ["para(P, Q, R, S)", "para(S, T, U, V)", "coll(R, S, T)"],
             ["para(P, Q, U, V)"]),
        ]

        for rule, hyps, concls in test_data:
            hyps = [parser.parse_fact(fact) for fact in hyps]
            concls = [parser.parse_fact(concl) for concl in concls]
            new_facts = expr.apply_rule_hyps(rule, hyps)
            self.assertEqual(set(new_facts), set(concls))

    def testApplyRulesetHyps(self):
        test_data = [
            (ruleset, ["coll(E, F, G)", "coll(E, F, H)"],
             ["coll(E, G, F)", "coll(E, H, F)", "coll(F, E, G)", "coll(F, E, H)", "coll(G, H, E)", "coll(H, G, E)"]),
        ]
        for rules, hyps, concls, in test_data:
            hyps = [parser.parse_fact(fact) for fact in hyps]
            concls = [parser.parse_fact(concl) for concl in concls]
            new_facts = expr.apply_ruleset_hyps(rules, hyps)
            self.assertEqual(set(new_facts), set(concls))


if __name__ == "__main__":
    unittest.main()
