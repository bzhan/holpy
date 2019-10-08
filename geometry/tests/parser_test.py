"""Unit test for parsing."""

import unittest

from geometry import parser
from geometry.expr import Fact, Rule, Line, Circle

class ParserTest(unittest.TestCase):
    def testParseFact(self):
        test_data = [
            ("coll(A0, C, B)", Fact("coll", ["A0", "C", "B"])),
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

    def testParseLine(self):
        test_data = [
            ("line(A, B, C)", Line(["A", "B", "C"])),
        ]

        for s, l in test_data:
            self.assertEqual(parser.parse_line(s), l)

    def testParseCircle(self):
        test_data = [
            ("circle(None, A, B, C)", Circle(["A", "B", "C"])),
            ("circle(P, E, F, G, H)", Circle(["E", "F", "G", "H"], center="P"))
        ]

        for s, l in test_data:
            self.assertEqual(parser.parse_circle(s), l)


if __name__ == "__main__":
    unittest.main()
