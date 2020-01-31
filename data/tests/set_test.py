# Author: Bohua Zhan

import unittest

from kernel.type import TVar
from kernel.term import Var
from logic import basic
from data import set

basic.load_theory('set')

class SetTest(unittest.TestCase):
    def testIsLiteralSet(self):
        Ta = TVar('a')
        x = Var('x', Ta)
        y = Var('x', Ta)
        test_data = [
            (set.empty_set(Ta), True),
            (set.mk_insert(x, set.empty_set(Ta)), True),
            (x, False),
        ]

        for t, res in test_data:
            self.assertEqual(set.is_literal_set(t), res)


if __name__ == "__main__":
    unittest.main()
