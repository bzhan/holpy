# Author: Bohua Zhan

import unittest
import sympy
from sympy import Symbol, sqrt, sin, cos
from sympy.abc import x

from logic.context import Context
from syntax import parser
from prover import sympywrapper


class SymPyWrapperTest(unittest.TestCase):
    def testConvert(self):
        test_data = [
            ("1 - x ^ (2::nat)", 1 - x ** 2),
            ("sqrt(2) * sin(x)", sqrt(2) * sin(x)),
        ]

        ctxt = Context('realintegral', vars={'x': 'real'})
        for s, res in test_data:
            s = parser.parse_term(ctxt, s)
            self.assertEqual(sympywrapper.convert(s), res)


if __name__ == "__main__":
    unittest.main()
