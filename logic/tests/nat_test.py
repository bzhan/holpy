# Author: Bohua Zhan

import unittest

from logic.nat import Nat

zero = Nat.zero
one = Nat.one

class NatTest(unittest.TestCase):
    def testPlus(self):
        self.assertEqual(Nat.mk_plus(), zero)
        self.assertEqual(Nat.mk_plus(zero), zero)
        self.assertEqual(Nat.mk_plus(one), one)
        self.assertEqual(Nat.mk_plus(zero, one), Nat.plus(zero, one))
        self.assertEqual(Nat.mk_plus(*([zero]*3)), Nat.plus(Nat.plus(zero, zero), zero))

if __name__ == "__main__":
    unittest.main()
