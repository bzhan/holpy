# Author: Bohua Zhan

import unittest

from kernel.type import TVar
from kernel.term import Term, Var, Abs, Bound
from logic.logic import Logic

Ta = TVar("a")
x = Var("x", Ta)
y = Var("y", Ta)
abs = Term.mk_abs

class LogicTest(unittest.TestCase):
    def testBetaNorm(self):
        test_data = [
            (abs(x,x)(x), x),
            (abs(x,abs(y,y))(x,y), y),
            (abs(x,abs(y,x))(x,y), x),
        ]

        for t, res in test_data:
            self.assertEqual(Logic.beta_norm(t), res)

if __name__ == "__main__":
    unittest.main()
