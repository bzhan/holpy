# Author: Bohua Zhan

import unittest

from kernel.type import TVar
from kernel.term import Var, Const, Abs
from logic import basic
from logic import matcher
from logic.matcher import first_order_match, MatchException
from data.nat import natT
from syntax import parser

class MatcherTest(unittest.TestCase):
    def testToInternalVars(self):
        test_data = [
            (Var("x", TVar("a")), Var("_x", TVar("_a"))),
            (Var("x", natT), Var("_x", natT)),
            (Const("x", TVar("a")), Const("x", TVar("_a"))),
            (Const("x", natT), Const("x", natT)),
            (Abs("x", TVar("a"), Var("y", TVar("b"))), Abs("x", TVar("_a"), Var("_y", TVar("_b")))),
        ]

        for t, res in test_data:
            self.assertEqual(matcher.to_internal_vars(t), res)

    def testToInternalInstsp(self):
        test_data = [
            (({"a": TVar("a")}, {"x": Var("x", TVar("a"))}),
             ({"_a": TVar("a")}, {"_x": Var("x", TVar("a"))})),
        ]

        for instsp, res in test_data:
            self.assertEqual(matcher.to_internal_instsp(instsp), res)

    def testFromInternalInstsp(self):
        test_data = [
            (({"_a": TVar("a")}, {"_x": Var("x", TVar("a"))}),
             ({"a": TVar("a")}, {"x": Var("x", TVar("a"))})),
        ]

        for instsp, res in test_data:
            self.assertEqual(matcher.from_internal_instsp(instsp), res)

    def testIsPattern(self):
        test_data = [
            ("a", True),
            ("f a", False),
            ("m + n", True),
            ("%x. P x", True),
            ("P (THE x. P x)", False),
            ("(!x. P x) & P x", True),
            ("P x & (!x. P x)", True),
            ("P x & x > 0", True),
            ("P (x + 1)", False),
            ("∀x. ∀s. Q s ⟶ ¬x ∈ s ⟶ finite s ⟶ Q (insert x s)", True),
        ]

        thy = basic.load_theory('set')
        ctxt = {"f": "'a => 'b", "a": "'a", "m": "nat", "n": "nat",
                "P": "nat => bool", "Q": "nat set => bool", "x": "nat", "s": "nat set"}
        ctxt = {'vars': dict((nm, parser.parse_type(thy, s))
                        for nm, s in ctxt.items()) if ctxt is not None else {}}
        for t, res in test_data:
            t = parser.parse_term(thy, ctxt, t)
            self.assertEqual(matcher.is_pattern(t, []), res)

    def run_test(self, thy_name, ctxt, pat, t, *, tyinst=None, inst=None, failed=None):
        thy = basic.load_theory(thy_name)
        ctxt = {'vars': dict((nm, parser.parse_type(thy, s))
                        for nm, s in ctxt.items()) if ctxt is not None else {}}
        pat = parser.parse_term(thy, ctxt, pat)
        t = parser.parse_term(thy, ctxt, t)
        tyinst = dict((nm, parser.parse_type(thy, s))
                      for nm, s in tyinst.items()) if tyinst is not None else dict()
        inst = dict((nm, parser.parse_term(thy, ctxt, s))
                    for nm, s in inst.items()) if inst is not None else dict()

        if failed is not None:
            self.assertRaises(failed, first_order_match, pat, t)
            return

        self.assertEqual(first_order_match(pat, t), (tyinst, inst))

    def testFirstOrderMatchBasic(self):
        """Basic tests."""
        test_data = [
            ("x", "a", {"x": "a"}),
            ("x", "(0::nat)", {"x": "(0::nat)"}),
            ("(0::nat)", "(0::nat)", {}),
            ("x + y", "a + b", {"x": "a", "y": "b"}),
            ("x + x", "a + a", {"x": "a"}),
            ("x + x", "a + b", None),
        ]

        ctxt = {"x": "nat", "y": "nat", "z": "nat", "a": "nat", "b": "nat"}
        for pat, t, inst in test_data:
            if inst is not None:
                self.run_test('nat', ctxt, pat, t, inst=inst)
            else:
                self.run_test('nat', ctxt, pat, t, failed=MatchException)

    def testFirstOrderMatchAbs(self):
        """Tests involving abstraction."""
        test_data = [
            ("%x::nat. y", "%x::nat. a", {"y": "a"}),
            ("%x::nat. (0::nat)", "%x::nat. (0::nat)", {}),
            ("%x::nat. y", "%x::nat. x", None),
            ("%x::nat. x", "%x::nat. x", {}),
            ("%x::nat. x", "%x::nat. a", None),
            ("%x::nat. y", "%x::nat. a + b", {"y": "a + b"}),
            ("%x::nat. y", "%x::nat. even x", None),
            ("%x::nat. %y::nat. x", "%x::nat. %y::nat. x", {}),
            ("%x::nat. %y::nat. x", "%x::nat. %y::nat. y", None),
        ]

        ctxt = {"x": "nat", "y": "nat", "z": "nat", "a": "nat", "b": "nat"}
        for pat, t, inst in test_data:
            if inst is not None:
                self.run_test('nat', ctxt, pat, t, inst=inst)
            else:
                self.run_test('nat', ctxt, pat, t, failed=MatchException)

    def testFirstOrderMatchFun(self):
        """Tests involving variables in function position."""
        test_data = [
            ("%x. P x", "%x. P x & Q x", {"P": "%x. P x & Q x"}),
            ("%x. P x & Q x", "%x. Q x & P x", {"P": "Q", "Q": "P"}),
            ("%x. P x & Q x", "%x. (P x & Q x) & R x", {"P": "%x. P x & Q x", "Q": "R"}),
            ("?x. P x", "?x. P x & Q x", {"P": "%x. P x & Q x"}),
        ]

        ctxt = {"P": "nat => bool", "Q": "nat => bool", "R": "nat => bool"}
        for pat, t, inst in test_data:
            self.run_test('nat', ctxt, pat, t, inst=inst)

    def testFirstOrderMatchFun2(self):
        """More complex matching with variables in function position."""
        test_data = [
            ("f x + g y + x + y", "p a + q b + a + b", {"f": "p", "g": "q", "x": "a", "y": "b"}),
            ("f x + x", "p (a + b) + (a + b)", {"f": "p", "x": "a + b"}),
            ("f x + x", "(p a + q a) + a", {"f": "%x. p x + q x", "x": "a"}),
            ("f x + x", "p (q a) + a", {"f": "%x. p (q x)", "x": "a"}),
        ]

        ctxt = {"f": "nat => nat", "g": "nat => nat", "x": "nat", "y": "nat",
                "p": "nat => nat", "q": "nat => nat", "a": "nat", "b": "nat"}
        for pat, t, inst in test_data:
            self.run_test('nat', ctxt, pat, t, inst=inst)

    def testFirstOrderMatchType(self):
        """Tests involving type variables."""
        test_data = [
            ("x", "m", {"a": "nat"}, {"x": "m"}),
        ]

        ctxt = {"x": "'a", "m": "nat"}
        for pat, t, tyinst, inst in test_data:
            self.run_test('nat', ctxt, pat, t, tyinst=tyinst, inst=inst)


if __name__ == "__main__":
    unittest.main()
