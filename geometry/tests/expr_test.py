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
            (["coll(A, B, C)", "coll(A, B, D)", "coll(P, Q)", "coll(Q, R)", "coll(Q, R, S)"],
             ["line(A, B, C, D)", "line(P, Q)", "line(Q, R, S)"]),
        ]
        for facts, concls in test_data:
            facts = [parser.parse_fact(fact) for fact in facts]
            line_facts = expr.make_line_facts(facts)
            concls = [parser.parse_line(line) for line in concls]
            self.assertEqual(set(line_facts), set(concls))

    '''def testExtendLine(self):
        test_data = [
            ("line(A, B, C)", ["coll(C, B)", "coll(C, A)", "coll(B, A)", "coll(B, C)", "coll(A, B)", "coll(A, C)",
                               "coll(A, B, C)", "coll(A, C, B)", "coll(B, A, C)", "coll(B, C, A)", "coll(C, A, B)",
                               "coll(C, B, A)"]),
        ]
        for line, concls in test_data:
            colls = expr.extend_line(parser.parse_line(line))
            concls = [parser.parse_fact(coll) for coll in concls]
            different = [coll for coll in colls if coll not in concls]
            self.assertEqual(len(different), 0)'''

    def testApplyRuleHyps(self):
        test_data = [
            (ruleset["D3"], ["coll(E, F, G)", "coll(E, F, H)", "coll(P, Q, R)", "coll(P, Q, S)", "coll(A, B, C)"],
             ["coll(G, H, E)", "coll(H, G, E)", "coll(R, S, P)", "coll(S, R, P)"]),
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
