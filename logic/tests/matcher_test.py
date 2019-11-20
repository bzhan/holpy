# Author: Bohua Zhan

import unittest

from kernel.type import TVar
from kernel.term import Var, Const, Abs
from logic import basic
from logic import matcher
from logic.matcher import first_order_match, MatchException
from data.nat import natT
from syntax import parser
from logic.basic import Context

class MatcherTest(unittest.TestCase):
    def testIsPattern(self):
        test_data = [
            ("?a", True),
            ("?f ?a", False),
            ("?m + ?n", True),
            ("%x. ?P x", True),
            ("?P (THE x. ?P x)", False),
            ("(!x. ?P x) & ?P x", True),
            ("?P x & (!x. ?P x)", True),
            ("?P ?x & ?x > 0", True),
            ("?P (?x + 1)", False),
            ("∀x. ∀s. ?Q s ⟶ ¬x ∈ s ⟶ finite s ⟶ ?Q (insert x s)", True),
        ]

        ctxt = Context('set', svars={
            "f": "'a => 'b", "a": "'a", "m": "nat", "n": "nat",
            "P": "nat => bool", "Q": "nat set => bool", "x": "nat", "s": "nat set"})
        for t, res in test_data:
            t = parser.parse_term(ctxt, t)
            self.assertEqual(matcher.is_pattern(t, []), res)

    def run_test(self, thy, pat, t, *, vars=None, svars=None, tyinst=None, inst=None, failed=None):
        ctxt = Context(thy, vars=vars, svars=svars)
        thy = ctxt.thy
        pat = parser.parse_term(ctxt, pat)
        t = parser.parse_term(ctxt, t)
        tyinst = dict((nm, parser.parse_type(thy, s))
                      for nm, s in tyinst.items()) if tyinst is not None else dict()
        inst = dict((nm, parser.parse_term(ctxt, s))
                    for nm, s in inst.items()) if inst is not None else dict()

        if failed is not None:
            self.assertRaises(failed, first_order_match, pat, t)
            return

        self.assertEqual(first_order_match(pat, t), (tyinst, inst))

    def testFirstOrderMatchBasic(self):
        """Basic tests."""
        test_data = [
            ("?x", "a", {"x": "a"}),
            ("?x", "(0::nat)", {"x": "(0::nat)"}),
            ("(0::nat)", "(0::nat)", {}),
            ("?x + ?y", "a + b", {"x": "a", "y": "b"}),
            ("?x + ?x", "a + a", {"x": "a"}),
            ("?x + ?x", "a + b", None),
        ]

        svars = {'x': "nat", 'y': "nat"}
        vars = {"a": "nat", "b": "nat"}
        for pat, t, inst in test_data:
            if inst is not None:
                self.run_test('nat', pat, t, vars=vars, svars=svars, inst=inst)
            else:
                self.run_test('nat', pat, t, vars=vars, svars=svars, failed=MatchException)

    def testFirstOrderMatchAbs(self):
        """Tests involving abstraction."""
        test_data = [
            ("%x::nat. ?y", "%x::nat. a", {"y": "a"}),
            ("%x::nat. (0::nat)", "%x::nat. (0::nat)", {}),
            ("%x::nat. ?y", "%x::nat. x", None),
            ("%x::nat. x", "%x::nat. x", {}),
            ("%x::nat. x", "%x::nat. a", None),
            ("%x::nat. ?y", "%x::nat. a + b", {"y": "a + b"}),
            ("%x::nat. ?y", "%x::nat. even x", None),
            ("%x::nat. %y::nat. x", "%x::nat. %y::nat. x", {}),
            ("%x::nat. %y::nat. x", "%x::nat. %y::nat. y", None),
        ]

        svars = {'y': 'nat'}
        vars = {"a": "nat", "b": "nat"}
        for pat, t, inst in test_data:
            if inst is not None:
                self.run_test('nat', pat, t, vars=vars, svars=svars, inst=inst)
            else:
                self.run_test('nat', pat, t, vars=vars, svars=svars, failed=MatchException)

    def testFirstOrderMatchFun(self):
        """Tests involving variables in function position."""
        test_data = [
            ("%x. ?P x", "%x. P x & Q x", {"P": "%x. P x & Q x"}),
            ("%x. ?P x & ?Q x", "%x. Q x & P x", {"P": "Q", "Q": "P"}),
            ("%x. ?P x & ?Q x", "%x. (P x & Q x) & R x", {"P": "%x. P x & Q x", "Q": "R"}),
            ("?x. ?P x", "?x. P x & Q x", {"P": "%x. P x & Q x"}),
        ]

        svars = {"P": "nat => bool", "Q": "nat => bool"}
        vars = {"P": "nat => bool", "Q": "nat => bool", "R": "nat => bool"}
        for pat, t, inst in test_data:
            self.run_test('nat', pat, t, vars=vars, svars=svars, inst=inst)

    def testFirstOrderMatchFun2(self):
        """More complex matching with variables in function position."""
        test_data = [
            ("?f ?x + ?g ?y + ?x + ?y", "p a + q b + a + b", {"f": "p", "g": "q", "x": "a", "y": "b"}),
            ("?f ?x + ?x", "p (a + b) + (a + b)", {"f": "p", "x": "a + b"}),
            ("?f ?x + ?x", "(p a + q a) + a", {"f": "%x. p x + q x", "x": "a"}),
            ("?f ?x + ?x", "p (q a) + a", {"f": "%x. p (q x)", "x": "a"}),
        ]

        svars = {"f": "nat => nat", "g": "nat => nat", "x": "nat", "y": "nat"}
        vars = {"p": "nat => nat", "q": "nat => nat", "a": "nat", "b": "nat"}
        for pat, t, inst in test_data:
            self.run_test('nat', pat, t, vars=vars, svars=svars, inst=inst)

    def testFirstOrderMatchFun3(self):
        """Heuristic matching for variables in function position."""
        test_data = [
            ("%x. ?f (?m x + ?c)", "%x. g (r x + 0)", {"f": "g", "m": "r", "c": "(0::nat)"}),
        ]

        svars = {"f": "nat => nat", "m": "nat => nat", "c": "nat"}
        vars = {"g": "nat => nat", "r": "nat => nat"}
        for pat, t, inst in test_data:
            self.run_test('nat', pat, t, vars=vars, svars=svars, inst=inst)

    def testFirstOrderMatchType(self):
        """Tests involving type variables."""
        test_data = [
            ("?x", "m", {"a": "nat"}, {"x": "m"}),
        ]

        svars = {"x": "'?a"}
        vars = {"m": "nat"}
        for pat, t, tyinst, inst in test_data:
            self.run_test('nat', pat, t, vars=vars, svars=svars, tyinst=tyinst, inst=inst)


if __name__ == "__main__":
    unittest.main()
