# Author: Bohua Zhan

import unittest

from logic import nat
from logic.nat import Nat, bit0, bit1

zero = Nat.zero
one = Nat.one

class NatTest(unittest.TestCase):
    def testPlus(self):
        self.assertEqual(Nat.mk_plus(), zero)
        self.assertEqual(Nat.mk_plus(zero), zero)
        self.assertEqual(Nat.mk_plus(one), one)
        self.assertEqual(Nat.mk_plus(zero, one), Nat.plus(zero, one))
        self.assertEqual(Nat.mk_plus(*([zero]*3)), Nat.plus(Nat.plus(zero, zero), zero))

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

        for n, binary in test_data:
            self.assertEqual(nat.to_binary(n), binary)
            self.assertEqual(nat.from_binary(binary), n)

    def testBinaryLarge(self):
        test_data = [
            100, 10000, 100000, 111111, 999999, 10101010101, 12345678987654321,
        ]

        for n in test_data:
            self.assertEqual(nat.from_binary(nat.to_binary(n)), n)

    def testIsBinary(self):
        test_data = [
            (zero, True),
            (Nat.Suc(zero), True),
            (Nat.Suc(one), False),
            (bit0(one), True),
            (bit0(Nat.Suc(bit0(one))), False),
            (bit0, False),
            (bit1, False),
        ]

        for n, b in test_data:
            self.assertEqual(nat.is_binary(n), b)

if __name__ == "__main__":
    unittest.main()
