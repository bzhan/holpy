# Author: Bohua Zhan

import unittest
from kernel.type import *

class TypeTest(unittest.TestCase):
    def testTFun(self):
        self.assertEqual(TFun(TVar("a"), TVar("b")), Type("fun", [TVar("a"), TVar("b")]))

    def testPrintType(self):
        test_data = [
            (TVar("a"), "'a"),
            (TVar("ab"), "'ab"),
            (Type("bool"), "bool"),
            (Type("list", TVar("a")), "'a list"),
            (Type("list", Type("list", TVar("a"))), "'a list list"),
            (Type("tree", [TVar("a"), TVar("b")]), "('a, 'b) tree"),
            (TFun(TVar("a"), TVar("b")), "'a => 'b"),
            (TFun(TVar("a"), TFun(TVar("b"), TVar("c"))), "'a => 'b => 'c"),
            (TFun(TFun(TVar("a"), TVar("b")), TVar("c")), "('a => 'b) => 'c"),
            (TFun(Type("list", TVar("a")), TVar("b")), "'a list => 'b"),
            (TFun(TVar("a"), Type("list", TVar("b"))), "'a => 'b list"),
        ]

        for (t, str_t) in test_data:
            self.assertEqual(str(t), str_t)

if __name__ == "__main__":
    unittest.main()
