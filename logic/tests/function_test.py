# Author: Bohua Zhan

import unittest

from kernel.type import TVar, TFun
from kernel.term import Var
from logic.function import mk_fun_upd, strip_fun_upd

Ta = TVar("a")
Tb = TVar("b")
f = Var("f", TFun(Ta, Tb))
a1 = Var("a1", Ta)
a2 = Var("a2", Ta)
b1 = Var("b1", Ta)
b2 = Var("b2", Ta)

class FunctionTest(unittest.TestCase):
    def testMkFunUpd(self):
        self.assertEqual(mk_fun_upd(f, a1, b1, a2, b2),
                         mk_fun_upd(mk_fun_upd(f, a1, b1), a2, b2))

    def testStripFunUpd(self):
        self.assertEqual(strip_fun_upd(f), (f, []))
        self.assertEqual(strip_fun_upd(mk_fun_upd(f, a1, b1)), (f, [(a1, b1)]))
        self.assertEqual(strip_fun_upd(mk_fun_upd(f, a1, b1, a2, b2)), (f, [(a1, b1), (a2, b2)]))


if __name__ == "__main__":
    unittest.main()
