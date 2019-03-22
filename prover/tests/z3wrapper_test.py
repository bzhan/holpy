# Author: Bohua Zhan

import unittest

from kernel.type import TFun
from logic import nat
from logic import basic
from syntax import parser
from syntax import printer
from prover import z3wrapper

thy = basic.loadTheory('nat')

natT = nat.natT

class Z3WrapperTest(unittest.TestCase):
    def testSolve(self):
        ctxt = {"s": TFun(natT, natT), "A": natT, "B": natT}
        test_data = [
            ("s 0 = 0 & s 1 = 0 --> s 1 = s 0 * B", True),
            ("s 1 = s 0 * B & ~~s 0 = A --> s 1 = A * B", True),
            ("s 1 = s 0 * B & ~s 0 = A --> s 1 + B = (s 0 + 1) * B", True),
            ("A * B + 1 = 1 + B * A", True),
            ("s 0 = s 1", False),
            ("s 0 + s 1 = A --> A + s 2 = B --> s 0 + s 2 + s 1 = B", True),
            ("s 0 + s 1 = A --> A + s 2 = B --> s 0 + s 2 = B", False),
        ]

        for s, res in test_data:
            t = parser.parse_term(thy, ctxt, s)
            self.assertEqual(z3wrapper.solve(t), res)


if __name__ == "__main__":
    unittest.main()
