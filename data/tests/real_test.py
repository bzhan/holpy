# Author: Bohua Zhan

import unittest

from logic.tests.conv_test import test_conv
from logic.tests.logic_test import test_macro
from data import real


class RealTest(unittest.TestCase):
    def testRealNormMacro(self):
        test_data = [
            ("x * (y * z) = y * (z * x)"),
            ("-x = -1 * x"),
            ("x - y = x + -1 * y"),
        ]

        vars = {'x': 'real', 'y': 'real', 'z': 'real'}
        for expr in test_data:
            test_macro(self, 'real', 'real_norm', vars=vars, args=expr, res=expr, eval_only=True)

    def testRealNormMacroFailed(self):
        test_data = [
            ("x * y * z = x * y + z"),
            ("1 + x + y = x + y + 2"),
        ]

        vars = {'x': 'real', 'y': 'real', 'z': 'real'}
        for expr in test_data:
            test_macro(self, 'real', 'real_norm', vars=vars, args=expr, failed=AssertionError, eval_only=True)

    def testRealNormConv(self):
        test_data = [
            ("x + 0", "x"),
            ("x * (y + z)", "x * y + x * z"),
            ("of_nat 2 + x", "2 + x"),
            ("of_nat (m + n) + x", "of_nat m + of_nat n + x"),
            ("of_nat (m * n) + x", "of_nat m * of_nat n + x"),
            ("x ^ (1::nat)", "x"),
            ("(x + y) ^ (2::nat)", "2 * x * y + x ^ (2::nat) + y ^ (2::nat)"),
            ("x ^ ((2::nat) - 1)", "x"),
        ]

        vars = {'x': 'real', 'y': 'real', 'z': 'real', 'm': 'nat', 'n': 'nat'}
        for expr, res in test_data:
            test_conv(self, 'real', real.real_norm_conv(), vars=vars, t=expr, t_res=res)


if __name__ == "__main__":
    unittest.main()
