# Author: Bohua Zhan

import unittest

from kernel.thm import Thm
from data import nat
from data import interval
from data import set
from logic import basic
from syntax import printer

thy = basic.load_theory('iterate')

class IntervalTest(unittest.TestCase):
    def testNumsegConv(self):
        test_data = [
            (5, 4),
            (5, 5),
            (3, 5),
            (0, 10),
        ]

        for m, n in test_data:
            mt, nt = nat.to_binary_nat(m), nat.to_binary_nat(n)
            t = interval.mk_interval(mt, nt)
            pt = interval.numseg_conv().get_proof_term(thy, t)
            rhs = set.mk_literal_set([nat.to_binary_nat(i) for i in range(m, n+1)], nat.natT)
            prf = pt.export()
            self.assertEqual(thy.check_proof(prf), Thm.mk_equals(t, rhs))


if __name__ == "__main__":
    unittest.main()
