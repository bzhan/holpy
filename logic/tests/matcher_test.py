# Author: Bohua Zhan

import unittest
from kernel.type import *
from kernel.term import *
from logic.matcher import *

Ta = TVar("a")
Tf = TFun(Ta, TFun(Ta, Ta))
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
            (Comb2(f,x,y), Comb2(f,a,b), {"x" : a, "y" : b}),
            (Comb2(f,x,x), Comb2(f,a,a), {"x" : a}),
            (Comb2(f,x,x), Comb2(f,a,b), None),
            (Abs("x",Ta,x), Abs("x",Ta,a), {"x" : a}),
            (Abs("x",Ta,a), Abs("x",Ta,a), {}),
            (Abs("x",Ta,a), Abs("x",Ta,b), None),
            (Abs("x",Ta,x), Abs("x",Ta,B0), None),
            (Abs("x",Ta,x), Abs("x",Ta,Abs("y",Ta,B0)), {"x" : Abs("y",Ta,B0)}),
            (Abs("x",Ta,x), Abs("x",Ta,Abs("y",Ta,B1)), None),
            (Abs("x",Ta,B0), Abs("x",Ta,B0), {}),
            (Abs("x",Ta,Abs("y",Ta,B0)), Abs("x",Ta,Abs("y",Ta,B1)), None),
        ]

        for (pat, t, inst) in test_data:
            if inst is not None:
                self.assertEqual(Matcher.first_order_match(pat, t), inst)
            else:
                self.assertRaises(MatchException, Matcher.first_order_match, pat, t)

if __name__ == "__main__":
    unittest.main()
