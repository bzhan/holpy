# Author: Bohua Zhan

import unittest

from kernel.type import TVar
from kernel.term import Var, Abs, Bound
from logic.logic import Logic

Ta = TVar("a")
x = Var("x", Ta)
y = Var("y", Ta)

class LogicTest(unittest.TestCase):
    def testBetaNorm(self):
        test_data = [
            (Abs("x",Ta,Bound(0))(x), x),
            (Abs("x",Ta,"y",Ta,Bound(0))(x,y), y),
            (Abs("x",Ta,"y",Ta,Bound(1))(x,y), x),
        ]

        for t, res in test_data:
            self.assertEqual(Logic.beta_norm(t), res)

if __name__ == "__main__":
    unittest.main()
