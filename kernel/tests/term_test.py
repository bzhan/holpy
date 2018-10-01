# Author: Bohua Zhan

import unittest
from kernel.type import *
from kernel.term import *

Ta = TVar("a")
Tb = TVar("b")
Taa = TFun(Ta, Ta)             # 'a => 'a
Tab = TFun(Ta, Tb)             # 'a => 'b
Taab = TFun(Ta, TFun(Ta, Tb))  # 'a => 'a => 'b
a = Var("a", Ta)
b = Var("b", Tb)
c = Const("c", Ta)
f = Var("f", Tab)     # f: 'a => 'b
f2 = Var("f2", Taab)  # f2: 'a => 'a => 'b
g = Var("g", Taa)     # g: 'a => 'a
B0 = Bound(0)
B1 = Bound(1)

class TermTest(unittest.TestCase):
    def testPrintTerm(self):
        test_data = [
            (a, "Var(a,'a)"),
            (f, "Var(f,'a => 'b)"),
            (c, "Const(c,'a)"),
            (Comb(f, a), "Var(f,'a => 'b) $ Var(a,'a)"),
            (Comb(Comb(f2, a), a), "Var(f2,'a => 'a => 'b) $ Var(a,'a) $ Var(a,'a)"),
            (Comb(f, Comb(g, a)), "Var(f,'a => 'b) $ (Var(g,'a => 'a) $ Var(a,'a))"),
            (Abs("x", Ta, b), "Abs(x,'a,Var(b,'b))"),
            (Abs("x", Ta, B0), "Abs(x,'a,Bound 0)"),
            (Abs("x", Ta, Abs("y", Ta, B0)), "Abs(x,'a,Abs(y,'a,Bound 0))"),
            (Abs("x", Ta, Abs("y", Ta, B1)), "Abs(x,'a,Abs(y,'a,Bound 1))"),
        ]

        for (t, str_t) in test_data:
            self.assertEqual(str(t), str_t)

    def testReprTerm(self):
        test_data = [
            (a, "a"),
            (f, "f"),
            (c, "c"),
            (Comb(f, a), "f a"),
            (Comb(Comb(f2, a), a), "f2 a a"),
            (Comb(f, Comb(g, a)), "f (g a)"),
            (Abs("x", Ta, b), "%x. b"),
            (Abs("x", Ta, B0), "%x. x"),
            (Abs("x", Ta, Abs("y", Ta, B0)), "%x. %y. y"),
            (Abs("x", Ta, Abs("y", Ta, B1)), "%x. %y. x"),
            (Abs("x", Ta, Abs("y", Ta, Comb(f,B0))), "%x. %y. f y"),
            (Abs("x", Ta, Abs("y", Ta, Comb(Comb(f2, B1), B0))), "%x. %y. f2 x y"),
        ]

        for (t, repr_t) in test_data:
            self.assertEqual(repr(t), repr_t)

    def testEquals(self):
        test_data = [
            (Abs("x", Ta, b), Abs("y", Ta, b)),
            (Abs("x", Tb, Comb(f, B0)), Abs("y", Tb, Comb(f, B0))),
        ]

        for (t1, t2) in test_data:
            self.assertEqual(t1, t2)

if __name__ == "__main__":
    unittest.main()
