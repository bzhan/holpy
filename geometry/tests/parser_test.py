"""Unit test for parsing."""

import unittest

from geometry import parser
from geometry.expr import Fact, Rule

class ParserTest(unittest.TestCase):
    def testParseFact(self):
        test_data = [
            ("coll(A, C, B)", Fact("coll", ["A", "C", "B"])),
            ("coll(A,C,B)", Fact("coll", ["A", "C", "B"])),
        ]

        for s, f in test_data:
            self.assertEqual(parser.parse_fact(s), f)

    def testParseRule(self):
        test_data = [
            ("coll(A, C, B) :- coll(A, B, C)",
             Rule([Fact("coll", ["A", "B", "C"])], Fact("coll", ["A", "C", "B"]))),
        ]

        for s, r in test_data:
            self.assertEqual(parser.parse_rule(s), r)


if __name__ == "__main__":
    unittest.main()
