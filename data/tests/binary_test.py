# Author: Bohua Zhan

import unittest

from data import binary
from data.binary import zero, one, bit0, bit1


class BinaryTest(unittest.TestCase):
    def testBinary(self):
        test_data = [
            (0, zero),
            (1, one),
            (2, bit0(one)),
            (3, bit1(one)),
            (4, bit0(bit0(one))),
            (5, bit1(bit0(one))),
            (6, bit0(bit1(one))),
            (7, bit1(bit1(one))),
            (19, bit1(bit1(bit0(bit0(one))))),
            (127, bit1(bit1(bit1(bit1(bit1(bit1(one))))))),
        ]

        for n, t in test_data:
            self.assertEqual(binary.to_binary(n), t)
            self.assertEqual(binary.from_binary(t), n)

    def testBinaryLarge(self):
        test_data = [
            100, 10000, 100000, 111111, 999999, 10101010101, 12345678987654321,
        ]

        for n in test_data:
            self.assertEqual(binary.from_binary(binary.to_binary(n)), n)

    def testIsBinary(self):
        test_data = [
            (zero, True),
            (one, True),
            (bit0(one), True),
            (bit0, False),
            (bit1, False),
        ]

        for n, b in test_data:
            self.assertEqual(binary.is_binary(n), b)


if __name__ == "__main__":
    unittest.main()
