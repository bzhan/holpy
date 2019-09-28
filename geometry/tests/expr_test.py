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

    def testGetArgTypeByFact(self):
        test_data = [
            ("coll(A, B, C)", [expr.POINT, expr.POINT, expr.POINT]),
            ("perp(l, A, B)", [expr.LINE, expr.PonL]),
            ("cong(A, B, C, D)", [expr.SEG, expr.SEG]),
            ("para(A, B, C, D)", [expr.PonL, expr.PonL]),
        ]
        for fact, r in test_data:
            self.assertEqual(expr.get_arg_type_by_fact(parser.parse_fact(fact)), r)

    def testMatchFact(self):
        test_data = [
            ("coll(A,B,C)", "coll(P,Q,R)", {}, [{"A": "P", "B": "Q", "C": "R"}]),
            ("coll(A,B,C)", "coll(P,Q,R)", {"A": "P"}, [{"A": "P", "B": "Q", "C": "R"}]),
            ("coll(A,B,C)", "coll(P,Q,R)", {"A": "Q"}, []),
            ("coll(A,B,C)", "para(P,Q,R,S)", {}, []),
        ]

        for pat, f, inst, res in test_data:
            pat = parser.parse_fact(pat)
            f = parser.parse_fact(f)
            insts = expr.match_expr(pat, f, inst)
            self.assertEqual(insts, res)

    def testMatchFactLines(self):
        test_data = [
            ("perp(l, m)", "perp(P, Q, R, S)", {}, ["line(O, P, Q)"], [{"l": ("P", "Q"), "m": ("R", "S")}]),
            ("perp(l, m)", "perp(P, Q, R, S)", {"l": ("Q", "P")}, ["line(O, P, Q)"], [{"l": ("Q", "P"), "m": ("R", "S")}]),
            ("perp(l, m)", "perp(P, Q, R, S)", {"l": ("Q", "P")}, [], [{"l": ("Q", "P"), "m": ("R", "S")}]),
            ("perp(l, m)", "perp(P, Q, R, S)", {"l": ("A", "P")}, ["line(O, P, Q)"], []),
            ("para(p, q)", "para(E, N, C, D)", {}, [], [{"p": ("E", "N"), "q": ("C", "D")}]),

            ("para(A, B, C, D)", "para(P, Q, R, S)", {'A': 'M', 'B': 'N'}, ["line(M, N, P, Q)"],
             [{'A': 'M', 'B': 'N', 'C': 'R', 'D': 'S'}, {'A': 'M', 'B': 'N', 'C': 'S', 'D': 'R'}]),

            ("para(A, B, C, D)", "para(P, Q, R, S)", {'A': 'M', 'B': 'N'}, ["line(E, F, G, H)"], []),

            ("para(A, B, m)", "para(P, Q, R, S)", {"A": "Q"}, ["line(O, P, Q)"],
             [{"A": "Q", "B": "O", "m": ("R", "S")}, {"A": "Q", "B": "P", "m": ("R", "S")}, ]),

            ("cong(A, B, C, D)", "cong(P, Q, R, S)", {}, [], [{"A": "P", "B": "Q", "C": "R", "D": "S"},
                                                              {"A": "P", "B": "Q", "C": "S", "D": "R"},
                                                              {"A": "Q", "B": "P", "C": "R", "D": "S"},
                                                              {"A": "Q", "B": "P", "C": "S", "D": "R"},]),

            ("perp(B, A, C, A)", "perp(P, Q, P, R)", {}, [], [{"A": "P", "B": "Q", "C": "R"}]),
            
            ("cong(E, A, E, B)", "cong(A, Q, B, Q)", {"A": "A", "B": "B", "D": "P"}, [], [{"A": "A", "B": "B", "D": "P", "E": "Q"}]),
        ]

        for pat, f, inst, lines, res in test_data:
            pat = parser.parse_fact(pat)
            f = parser.parse_fact(f)
            lines = [parser.parse_line(line) for line in lines]
            insts = expr.match_expr(pat, f, inst, lines=lines)
            self.assertEqual(insts, res)

    def testApplyRule(self):
        test_data = [
            (ruleset["D1"], ["coll(E, F, G)"], [], ["coll(E, G, F)"]),
            (ruleset["D5"], ["para(E, F, G, H)"], ["line(E, F)", "line(G, H)"],
             ["para(G, H, E, F)"]),
            (ruleset["D44"], ["midp(P, E, F)", "midp(Q, E, G)"], ["line(E, F)", "line(G, E)"],
             ["para(P, Q, F, G)"]),
            (ruleset["D45"], ["midp(N, B, D)", "para(E, N, C, D)", "coll(E, B, C)"],
             ["line(M, N, E)", "line(C, D)", "line(D, N, B)", "line(C, E, B)"],
             ["midp(E, B, C)"]),
            (ruleset["D56"], ["cong(D, A, D, B)", "cong(E, A, E, B)"],
             [], ["perp(A, B, D, E)"]),
        ]

        for rule, facts, lines, concls in test_data:
            facts = [parser.parse_fact(fact) for fact in facts]
            concls = [parser.parse_fact(concl) for concl in concls]
            lines = [parser.parse_line(line) for line in lines]
            facts = expr.apply_rule(rule, facts, lines=lines)
            self.assertEqual(facts, concls)

    def testMakeNewLines(self):
        test_data = [
            (["coll(A, B, C)", "coll(A, B, D)", "coll(P, Q, R)", "coll(R, S, T)", "coll(Q, R, S)"], [],
             ["line(A, B, C, D)", "line(P, Q, R, S, T)"]),

            (["coll(A, B, C)"], ["line(B, C, D)"], ["line(A, B, C, D)"]),

            (["coll(E, F)"], ["line(F, G, H)"], ["line(E, F)", "line(F, G, H)"]),

        ]
        for facts, lines, concls in test_data:
            facts = [parser.parse_fact(fact) for fact in facts]
            lines = [parser.parse_line(line) for line in lines]
            prev_lines = lines
            expr.make_new_lines(facts, lines)
            self.assertEqual(set(prev_lines), set(lines))

    def testApplyRuleHyps(self):
        test_data = [
            (ruleset["D3"], ["coll(E, F, G)", "coll(E, F, H)", "coll(P, Q, R)", "coll(P, Q, S)", "coll(A, B, C)"],
             [], ["coll(G, H, E)", "coll(H, G, E)", "coll(R, S, P)", "coll(S, R, P)"]),

            (ruleset["D5"], ["para(P, Q, R, S)"], [], ["para(R, S, P, Q)"]),

            (ruleset["D45"], ["midp(N, B, D)", "para(E, N, C, D)", "coll(E, B, C)"],
             ["line(M, N, E)", "line(C, D)", "line(D, N, B)", "line(C, E, B)"],
             ["midp(E, B, C)"]),
        ]

        for rule, hyps, lines, concls in test_data:
            hyps = [parser.parse_fact(fact) for fact in hyps]
            concls = [parser.parse_fact(concl) for concl in concls]
            lines = [parser.parse_line(line) for line in lines]
            new_facts = expr.apply_rule_hyps(rule, hyps, lines=lines)
            self.assertEqual(set(new_facts), set(concls))

    def testApplyRulesetHyps(self):
        test_data = [
            (ruleset, ["midp(N, B, D)", "para(E, N, C, D)", "coll(E, B, C)"],
                ["line(M, N, E)", "line(C, D)", "line(D, N, B)", "line(C, E, B)"],
                ["midp(E, B, C)", "para(C, D, E, N)", "coll(B, E, C)", "coll(E, C, B)"]),
        ]
        for rules, hyps, lines, concls, in test_data:
            hyps = [parser.parse_fact(fact) for fact in hyps]
            concls = [parser.parse_fact(concl) for concl in concls]
            lines = [parser.parse_line(line) for line in lines]
            new_facts = expr.apply_ruleset_hyps(rules, hyps, lines=lines)
            self.assertEqual(set(new_facts), set(concls))

    def testSearchStep(self):
        test_data = [
        ]
        for rules, hyps, lines, concls in test_data:
            hyps = [parser.parse_fact(fact) for fact in hyps]
            lines = [parser.parse_line(line) for line in lines]
            concls = [parser.parse_fact(concl) for concl in concls]
            expr.search_step(rules, hyps, lines=lines)
            self.assertEqual(set(hyps), set(concls))

    def testSearchFixpoint(self):
        test_data = [
            (ruleset, ["cong(D, A, D, B)", "cong(E, A, E, B)", "perp(G, F, D, E)"],
             ["line(A, C, B)", "line(A, G, E)", "line(B, F, E)", "line(D, C, E)"],
            "para(A, C, G, F)")
        ]
        for rules, hyps, lines, concl in test_data:
            hyps = [parser.parse_fact(fact) for fact in hyps]
            concl = parser.parse_fact(concl)
            lines = [parser.parse_line(line) for line in lines]
            expr.search_fixpoint(ruleset, hyps, lines, concl)
            fact = expr.find_goal(hyps, concl, lines)
            self.assertIsNotNone(fact)

    def testPrintSearch(self):
        test_data = [
            (ruleset, ["cong(D, A, D, B)", "cong(E, A, E, B)", "perp(G, F, D, E)"],
             ["line(A, C, B)", "line(A, G, E)", "line(B, F, E)", "line(D, C, E)"],
             "para(A, C, G, F)")
        ]
        for rules, hyps, lines, concl in test_data:
            hyps = [parser.parse_fact(fact) for fact in hyps]
            concl = parser.parse_fact(concl)
            lines = [parser.parse_line(line) for line in lines]
            expr.search_fixpoint(ruleset, hyps, lines, concl)
            fact = expr.find_goal(hyps, concl, lines)
            self.assertIsNotNone(fact)
            expr.print_search(ruleset, hyps, fact)


if __name__ == "__main__":
    unittest.main()
