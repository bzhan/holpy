# Author: Bohua Zhan

import unittest

from kernel.type import TVar, TFun, hol_bool
from kernel.term import Term, Var, Const, Abs, Bound
from logic.matcher import Matcher, MatchException

Ta = TVar("a")
a = Const("a", Ta)
b = Const("b", Ta)
c = Const("c", Ta)
f = Const("f", TFun(Ta, Ta, Ta))
x = Var("x", Ta)
y = Var("y", Ta)
abs = Term.mk_abs

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
            (abs(x,y), abs(x,a), {"y" : a}),
            (abs(x,a), abs(x,a), {}),
            (abs(x,a), abs(x,b), None),
            (abs(x,y), abs(x,x), None),
            (abs(x,y), abs(x,abs(y,y)), {"y" : abs(y,y)}),
            (abs(x,y), abs(x,abs(y,x)), None),
            (abs(x,x), abs(x,x), {}),
            (abs(x,abs(y,y)), abs(x,abs(y,x)), None),
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
        C = Const("C", TFun(hol_bool, hol_bool, hol_bool))

        test_data = [
            (abs(x,P(x)), abs(x,C(P(x),Q(x))), {"P" : abs(x,C(P(x),Q(x)))}),
            (abs(x,C(P(x),Q(x))), abs(x,C(Q(x),P(x))), {"P": abs(x,Q(x)), "Q": abs(x,P(x))}),
            (abs(x,C(P(x),P(x))), abs(x,C(C(P(x),Q(x)),C(P(x),Q(x)))), {"P": abs(x,C(P(x),Q(x)))}),
        ]

        for pat, t, inst in test_data:
            if inst is not None:
                self.assertEqual(Matcher.first_order_match(pat, t), inst)
            else:
                self.assertRaises(MatchException, Matcher.first_order_match, pat, t)


if __name__ == "__main__":
    unittest.main()
