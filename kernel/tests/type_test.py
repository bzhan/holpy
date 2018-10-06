# Author: Bohua Zhan

import unittest
from kernel.type import TVar, Type, TFun, hol_bool, TypeMatchException

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
            (Type("tree", Ta, Tb), "('a, 'b) tree"),
            (TFun(Ta, Tb), "'a => 'b"),
            (TFun(Ta, Tb, Tc), "'a => 'b => 'c"),
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

        for (T, tyinst, res) in test_data:
            self.assertEqual(T.subst(tyinst), res)

    def testMatch(self):
        test_data = [
            (Ta, Tb, {"a" : Tb}),
            (TFun(Ta,Tb), TFun(Tb,Ta), {"a" : Tb, "b" : Ta}),
            (Ta, hol_bool, {"a" : hol_bool}),
            (TFun(Ta,hol_bool), TFun(hol_bool,hol_bool), {"a" : hol_bool}),
        ]

        for (pat, T, tyinst) in test_data:
            self.assertEqual(pat.match(T), tyinst)

    def testMatchFail(self):
        test_data = [
            (TFun(Ta,Ta), TFun(Ta,Tb)),
            (hol_bool, Ta),
        ]
        
        for (pat, T) in test_data:
            self.assertRaises(TypeMatchException, pat.match, T)

if __name__ == "__main__":
    unittest.main()
