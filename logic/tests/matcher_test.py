# Author: Bohua Zhan

import unittest

from kernel.type import TVar, TFun, hol_bool
from kernel.term import Var, Const, Abs, Bound
from logic.matcher import Matcher, MatchException

Ta = TVar("a")
Tf = TFun(Ta, Ta, Ta)
a = Const("a", Ta)
b = Const("b", Ta)
c = Const("c", Ta)
f = Const("f", Tf)
x = Var("x", Ta)
y = Var("y", Ta)
B0 = Bound(0)
B1 = Bound(1)

class MatcherTest(unittest.TestCase):
    def testFirstOrderMatch(self):
        test_data = [
            (x, y, {"x" : y}),
            (x, a, {"x" : a}),
            (a, a, {}),
            (a, b, None),
            (f(x,y), f(a,b), {"x" : a, "y" : b}),
            (f(x,x), f(a,a), {"x" : a}),
            (f(x,x), f(a,b), None),
            (Abs("x",Ta,x), Abs("x",Ta,a), {"x" : a}),
            (Abs("x",Ta,a), Abs("x",Ta,a), {}),
            (Abs("x",Ta,a), Abs("x",Ta,b), None),
            (Abs("x",Ta,x), Abs("x",Ta,B0), None),
            (Abs("x",Ta,x), Abs("x",Ta,"y",Ta,B0), {"x" : Abs("y",Ta,B0)}),
            (Abs("x",Ta,x), Abs("x",Ta,"y",Ta,B1), None),
            (Abs("x",Ta,B0), Abs("x",Ta,B0), {}),
            (Abs("x",Ta,"y",Ta,B0), Abs("x",Ta,"y",Ta,B1), None),
        ]

        for pat, t, inst in test_data:
            if inst is not None:
                self.assertEqual(Matcher.first_order_match(pat, t), inst)
            else:
                self.assertRaises(MatchException, Matcher.first_order_match, pat, t)

    def testFirstOrderMatchFun(self):
        """First-order matching of variables in function position."""
        P = Var("P", TFun(Ta, hol_bool))
        Q = Var("Q", TFun(Ta, hol_bool))
        conj = Const("conj", TFun(hol_bool, hol_bool, hol_bool))

        test_data = [
            (Abs("x",Ta,P(B0)), Abs("x",Ta,conj(P(B0),Q(B0))), {"P" : Abs("x",Ta,conj(P(B0),Q(B0)))}),
            (Abs("x",Ta,conj(P(B0),Q(B0))), Abs("x",Ta,conj(Q(B0),P(B0))), {"P": Abs("x",Ta,Q(B0)), "Q": Abs("x",Ta,P(B0))}),
            (Abs("x",Ta,conj(P(B0),P(B0))), Abs("x",Ta,conj(conj(P(B0),Q(B0)),conj(P(B0),Q(B0)))), {"P": Abs("x",Ta,conj(P(B0),Q(B0)))}),
        ]

        for pat, t, inst in test_data:
            if inst is not None:
                self.assertEqual(Matcher.first_order_match(pat, t), inst)
            else:
                self.assertRaises(MatchException, Matcher.first_order_match, pat, t)


if __name__ == "__main__":
    unittest.main()
