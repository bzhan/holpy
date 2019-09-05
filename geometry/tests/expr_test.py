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

    def testArgType(self):
        test_data = [
            ("l:{P, Q}", 2)
        ]
        for s, r in test_data:
            self.assertEqual(expr.arg_type(s), 2)

    def testMatchFact(self):
        test_data = [
            ("coll(A,B,C)", "coll(P,Q,R)", {}, [{"A": "P", "B": "Q", "C": "R"}]),
            ("coll(A,B,C)", "coll(P,Q,R)", {"A": "P"}, [{"A": "P", "B": "Q", "C": "R"}]),
            ("coll(A,B,C)", "coll(P,Q,R)", {"A": "Q"}, None),
            ("coll(A,B,C)", "para(P,Q,R,S)", {}, None),
        ]

        for pat, f, inst, res in test_data:
            pat = parser.parse_fact(pat)
            f = parser.parse_fact(f)
            if res is not None:
                insts = expr.match_expr(pat, f, inst)
                self.assertEqual(insts, res)
            else:
                self.assertRaises(expr.MatchException, expr.match_expr, pat, f, inst)

    def testMatchFactLines(self):
        test_data = [
            ("perp(l, m)", "perp(P, Q, R, S)", {}, ["line(O, P, Q)"], [{"l": ("P", "Q"), "m": ("R", "S")}]),
            ("perp(l, m)", "perp(P, Q, R, S)", {"l": ("Q", "P")}, ["line(O, P, Q)"], [{"l": ("Q", "P"), "m": ("R", "S")}]),
            ("perp(l, m)", "perp(P, Q, R, S)", {"l": ("Q", "P")}, [], [{"l": ("Q", "P"), "m": ("R", "S")}]),
            ("perp(l, m)", "perp(P, Q, R, S)", {"l": ("A", "P")}, ["line(O, P, Q)"], None),
            ("para(p, q)", "para(E, N, C, D)", {}, [], [{"p": ("E", "N"), "q": ("C", "D")}]),

            ("para({A, B}, {C, D})", "para(P, Q, R, S)", {'A': 'M', 'B': 'N'}, ["line(M, N, P, Q)"],
             [{'A': 'M', 'B': 'N', 'C': 'R', 'D': 'S'}, {'A': 'M', 'B': 'N', 'C': 'S', 'D': 'R'}]),

            ("para({A, B}, {C, D})", "para(P, Q, R, S)", {'A': 'M', 'B': 'N'}, ["line(E, F, G, H)"], None),

            ("para(C, D, {A, B})", "para(R, S, P, Q)", {}, ["line(O, P, Q)"], [
                {'C': 'R', 'D': 'S', 'A': 'P', 'B': 'Q'}, {'C': 'R', 'D': 'S', 'A': 'P', 'B': 'O'},
                {'C': 'R', 'D': 'S', 'A': 'Q', 'B': 'P'}, {'C': 'R', 'D': 'S', 'A': 'Q', 'B': 'O'},
                {'C': 'R', 'D': 'S', 'A': 'O', 'B': 'P'}, {'C': 'R', 'D': 'S', 'A': 'O', 'B': 'Q'}]),

            ("para({A, B}, C, D)", "para(P, Q, R, S)", {}, ["line(O, P, Q)"], [
                {'C': 'R', 'D': 'S', 'A': 'P', 'B': 'Q'}, {'C': 'R', 'D': 'S', 'A': 'P', 'B': 'O'},
                {'C': 'R', 'D': 'S', 'A': 'Q', 'B': 'P'}, {'C': 'R', 'D': 'S', 'A': 'Q', 'B': 'O'},
                {'C': 'R', 'D': 'S', 'A': 'O', 'B': 'P'}, {'C': 'R', 'D': 'S', 'A': 'O', 'B': 'Q'}]),

            ("para({A, B}, {C, D})", "para(P, Q, R, S)", {}, ["line(P, Q)"],
                [{"A": "P", "B": "Q", "C": "R", "D": "S"}, {"A": "Q", "B": "P", "C": "R", "D": "S"},
                {"A": "P", "B": "Q", "C": "S", "D": "R"}, {"A": "Q", "B": "P", "C": "S", "D": "R"},]),

            ("para({A, B}, C, D)", "para(P, Q, R, S)", {}, ["line(P, Q)"],
             [{"A": "P", "B": "Q", "C": "R", "D": "S"}, {"A": "Q", "B": "P", "C": "R", "D": "S"},]),

            ("para({A, B}, C, D)", "para(P, Q, R, S)", {"A": "Q"}, ["line(O, P, Q)"],
             [{"A": "Q", "B": "O", "C": "R", "D": "S"}, {"A": "Q", "B": "P", "C": "R", "D": "S"},]),

            ("para({A, B}, m)", "para(P, Q, R, S)", {"A": "Q"}, ["line(O, P, Q)"],
             [{"A": "Q", "B": "O", "m": ("R", "S")}, {"A": "Q", "B": "P", "m": ("R", "S")}, ]),

        ]

        for pat, f, inst, lines, res in test_data:
            pat = parser.parse_fact(pat)
            f = parser.parse_fact(f)
            lines = [parser.parse_line(line) for line in lines]
            if res is not None:
                insts = expr.match_expr(pat, f, inst, lines=lines)
                for inst in insts:
                    identical = [r for r in res if r == inst]
                    self.assertEqual(len(identical), 1)
            else:
                self.assertRaises(expr.MatchException, expr.match_expr, pat, f, inst, lines=lines)

    def testApplyRule(self):
        test_data = [
            #(ruleset["D1"], ["coll(E, F, G)"], [], "coll(E, G, F)"),
            #(ruleset["D5"], ["para(E, F, G, H)"], [], "para(G, H, E, F)"),
            #(ruleset["D5"], ["para(E, F, G, H)"], ["line(E, F)", "line(G, H)"], "para(G, H, E, F)"),
            #(ruleset["D44"], ["midp(P, E, F)", "midp(Q, E, G)"], ["line(E, F)", "line(G, E)"], "para(P, Q, F, G)"),
            (ruleset["D45"], ["midp(N, B, D)", "para(C, D, E, N)", "coll(E, B, C)"],
                                ["line(M, N, E)", "line(C, D)", "line(D, N, B)", "line(C, E, B)"], "midp(E, B, C)")
        ]

        for rule, facts, lines, concl in test_data:
            facts = [parser.parse_fact(fact) for fact in facts]
            concl = parser.parse_fact(concl)
            lines = [parser.parse_line(line) for line in lines]
            self.assertEqual(expr.apply_rule(rule, facts, lines=lines), concl)

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
