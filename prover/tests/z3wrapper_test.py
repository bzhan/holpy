# Author: Bohua Zhan

import unittest

from kernel.type import TFun
from kernel.thm import Thm
from logic import nat
from logic import basic
from syntax import parser
from syntax import printer
from prover import z3wrapper

thy = basic.load_theory('nat')

natT = nat.natT

class Z3WrapperTest(unittest.TestCase):
    def testSolve(self):
        if not z3wrapper.z3_loaded:
            return

        ctxt = {"s": TFun(natT, natT), "A": natT, "B": natT}
        test_data = [
            ("s 0 = 0 & s 1 = 0 --> s 1 = s 0 * B", True),
            ("s 1 = s 0 * B & ~~s 0 = A --> s 1 = A * B", True),
            ("s 1 = s 0 * B & ~s 0 = A --> s 1 + B = (s 0 + 1) * B", True),
            ("A * B + 1 = 1 + B * A", True),
            ("s 0 = s 1", False),
            ("s 0 + s 1 = A --> A + s 2 = B --> s 0 + s 2 + s 1 = B", True),
            ("s 0 + s 1 = A --> A + s 2 = B --> s 0 + s 2 = B", False),
            ("(!n. s n = 0) --> s 2 = 0", True),
            ("(!n. s n = 0) --> s 0 = 1", False),
        ]

        for s, res in test_data:
            t = parser.parse_term(thy, ctxt, s)
            self.assertEqual(z3wrapper.solve(t), res)

    def testZ3Macro(self):
        if not z3wrapper.z3_loaded:
            return

        macro = z3wrapper.Z3Macro()

        ctxt = {"s": TFun(natT, natT), "A": natT, "B": natT}
        test_data = [
            ("A * B + 1 = 1 + B * A", True),
            ("s 0 = s 1", False),
        ]

        for s, res in test_data:
            t = parser.parse_term(thy, ctxt, s)
            if res:
                self.assertEqual(macro.eval(thy, t, []), Thm([], t))
            else:
                self.assertRaises(AssertionError, macro.eval, thy, t, [])


if __name__ == "__main__":
    unittest.main()
