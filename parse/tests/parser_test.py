# Author: Bohua Zhan

import unittest

from kernel.type import TVar, Type, HOLType
from parse.parser import type_parser

class ParserTest(unittest.TestCase):
    def testParseType(self):
        parse = type_parser.parse

        test_data = [
            "'b",
            "nat",
            "'a list",
            "nat list",
            "('a, 'b) prod",
            "nat list list",
            "(nat, 'a) prod",
        ]

        for s in test_data:
            T = parse(s)
            self.assertIsInstance(T, HOLType)
            self.assertEqual(str(T), s)

if __name__ == "__main__":
    unittest.main()
