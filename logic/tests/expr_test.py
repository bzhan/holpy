# Author: Bohua Zhan

import unittest

from kernel.type import TFun
from kernel.term import Var
from kernel.thm import Thm
from logic import basic
from logic import nat
from logic import expr

natT = nat.natT
zero = nat.zero
one = nat.one
five = nat.to_binary(5)

thy = basic.loadTheory('expr')

class ExprTest(unittest.TestCase):
    def testProveEvalI(self):
        s = Var("s", TFun(natT, natT))
        t = expr.Plus(expr.V(one), expr.N(five))
        n = nat.plus(s(one), five)
        self.assertEqual(expr.prove_avalI(thy, s, t), Thm([], expr.avalI(s, t, n)))


if __name__ == "__main__":
    unittest.main()
