# Author: Bohua Zhan

import unittest
from kernel.theory import *

thy = Theory.EmptyTheory()

Ta = TVar("a")
Tb = TVar("b")

class TheoryTest(unittest.TestCase):
    def testEmptyTheory(self):
        self.assertEqual(thy.get_type_sig("bool"), 0)
        self.assertEqual(thy.get_type_sig("fun"), 2)
        self.assertEqual(thy.get_term_sig("equals"), TFun(Ta,TFun(Ta,hol_bool)))
        self.assertEqual(thy.get_term_sig("implies"), TFun(hol_bool,TFun(hol_bool,hol_bool)))

    def testCheckType(self):
        test_data = [
            Ta,
            TFun(Ta, Tb),
            TFun(TFun(Ta, Ta), Tb),
            TFun(hol_bool, hol_bool),
            TFun(TFun(Ta, hol_bool), hol_bool),
        ]

        for T in test_data:
            self.assertEqual(thy.check_type(T), None)

    def testCheckTypeFail(self):
        test_data = [
            Type("bool", Ta),
            Type("bool", [Ta, Ta]),
            Type("fun"),
            Type("fun", Ta),
            Type("fun", [Ta, Ta, Ta]),
            Type("random")
        ]

        for T in test_data:
            self.assertRaises(TheoryException, thy.check_type, T)

if __name__ == "__main__":
    unittest.main()
