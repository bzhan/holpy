# Author: Bohua Zhan

import unittest

from logic import basic
from data.int import is_binary_int, from_binary_int, to_binary_int, uminus, zero, one

thy = basic.load_theory("int")


class IntTest(unittest.TestCase):
    def testIsBinaryInt(self):
        test_data = [
            (zero, True),
            (one, True),
            (uminus(one), True)
        ]

        for t, res in test_data:
            self.assertEqual(is_binary_int(t), res)

    def testConvertBinaryInt(self):
        test_data = [
            0, 1, -1, 2, -2, 3, -3, 10, -10,
        ]
        
        for n in test_data:
            self.assertEqual(from_binary_int(to_binary_int(n)), n)


if __name__ == "__main__":
    unittest.main()
