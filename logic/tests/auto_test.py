# Author: Bohua Zhan

import unittest
from logic import auto
from logic.tests.logic_test import test_macro


class AutoTest(unittest.TestCase):
    def testSolve(self):
        test_data = [
            ("A --> B --> A & B"),
            ("A & B --> B & A"),
            ("A | B --> B | A"),
            ("A & B & C --> (A & B) & C"),
            ("A | B | C --> (A | B) | C")
        ]

        vars = {'A': 'bool', 'B': 'bool'}
        for expr in test_data:
            test_macro(self, 'logic_base', 'auto', vars=vars, args=expr, res=expr)


if __name__ == "__main__":
    unittest.main()
