# Author: Bohua Zhan

import unittest

from kernel.type import STVar, TVar, Type, TFun, BoolType, TypeMatchException

Ta = TVar("a")
Tb = TVar("b")
Tc = TVar("c")
STa = STVar("a")
STb = STVar("b")
STc = STVar("c")

class TypeTest(unittest.TestCase):
    def testReprType(self):
        test_data = [
            (Ta, "TVar(a)"),
            (Type("bool"), "Type(bool, [])"),
            (Type("list", Ta), "Type(list, [TVar(a)])"),
            (Type("tree", Ta, Tb), "Type(tree, [TVar(a), TVar(b)])"),
            (Type("fun", Ta, Tb), "Type(fun, [TVar(a), TVar(b)])"),
        ]

        for T, repr_T in test_data:
            self.assertEqual(repr(T), repr_T)

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
            (Type("list", TFun(Ta, Tb)), "('a => 'b) list"),
            (Type("list", Type("list", TFun(Ta, Tb))), "('a => 'b) list list"),
            (TFun(Type("list", Ta), Type("list", Tb)), "'a list => 'b list"),
            (Type("list", TFun(Type("list", Ta), Tb)), "('a list => 'b) list"),
        ]

        for T, str_T in test_data:
            self.assertEqual(str(T), str_T)

    def testStripType(self):
        test_data = [
            (Ta, ([], Ta)),
            (TFun(Ta, Tb), ([Ta], Tb)),
            (TFun(Ta, Ta, Tb), ([Ta, Ta], Tb)),
        ]

        for T, res in test_data:
            self.assertEqual(T.strip_type(), res)

    def testSubst(self):
        test_data = [
            (STa, {"a" : Tb}, Tb),
            (STa, {"b" : Tb}, STa),
            (TFun(STa, Tb), {"a" : Tb}, TFun(Tb, Tb)),
            (TFun(STa, STb), {"a" : Tb, "b" : Ta}, TFun(Tb, Ta)),
            (Type("list", STa), {"a" : Tb}, Type("list", Tb)),
        ]

        for T, tyinst, res in test_data:
            self.assertEqual(T.subst(tyinst), res)

    def testMatch(self):
        test_data = [
            (STa, Tb, {"a" : Tb}),
            (TFun(STa, STb), TFun(Tb,Ta), {"a" : Tb, "b" : Ta}),
            (STa, BoolType, {"a" : BoolType}),
            (TFun(STa, BoolType), TFun(BoolType, BoolType), {"a" : BoolType}),
        ]

        for pat, T, tyinst in test_data:
            self.assertEqual(pat.match(T), tyinst)

    def testMatchFail(self):
        test_data = [
            (TFun(STa, STa), TFun(Ta,Tb)),
            (BoolType, Ta),
        ]
        
        for pat, T in test_data:
            self.assertRaises(TypeMatchException, pat.match, T)

    def testGetTVars(self):
        test_data = [
            (BoolType, []),
            (TFun(Ta,Ta), [Ta]),
            (TFun(Ta,Tb), [Ta, Tb]),
        ]

        for T, res in test_data:
            self.assertEqual(T.get_tvars(), res)

    def testGetTSubs(self):
        test_data = [
            (BoolType, [BoolType]),
            (TFun(Ta,Ta), [TFun(Ta,Ta), Ta]),
            (TFun(Ta,Tb), [TFun(Ta,Tb), Ta, Tb]),
        ]

        for T, res in test_data:
            self.assertEqual(T.get_tsubs(), res)


if __name__ == "__main__":
    unittest.main()
