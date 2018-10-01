# Author: Bohua Zhan

import unittest
from kernel.type import *

Ta = TVar("a")
Tb = TVar("b")
Tc = TVar("c")

class TypeTest(unittest.TestCase):
    def testPrintType(self):
        test_data = [
            (Ta, "'a"),
            (TVar("ab"), "'ab"),
            (Type("bool"), "bool"),
            (Type("list", Ta), "'a list"),
            (Type("list", Type("list", Ta)), "'a list list"),
            (Type("tree", [Ta, Tb]), "('a, 'b) tree"),
            (TFun(Ta, Tb), "'a => 'b"),
            (TFun(Ta, TFun(Tb, Tc)), "'a => 'b => 'c"),
            (TFun(TFun(Ta, Tb), Tc), "('a => 'b) => 'c"),
            (TFun(Type("list", Ta), Tb), "'a list => 'b"),
            (TFun(Ta, Type("list", Tb)), "'a => 'b list"),
        ]

        for (T, str_T) in test_data:
            self.assertEqual(str(T), str_T)

    def testSubst(self):
        test_data = [
            (Ta, {"a" : Tb}, Tb),
            (Ta, {"b" : Tb}, Ta),
            (TFun(Ta, Tb), {"a" : Tb}, TFun(Tb, Tb)),
            (TFun(Ta, Tb), {"a" : Tb, "b" : Ta}, TFun(Tb, Ta)),
            (Type("list", Ta), {"a" : Tb}, Type("list", Tb)),
        ]

        for (T, subst, res) in test_data:
            self.assertEqual(T.subst(subst), res)

if __name__ == "__main__":
    unittest.main()
