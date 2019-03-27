# Author: Bohua Zhan

import unittest

from logic import basic
from logic import hoare
from logic.hoare_parser import parse_hoare, process_file
from syntax import parser
from syntax import printer

thy = basic.loadTheory('hoare')


class HoareParserTest(unittest.TestCase):
    def testHoareParser(self):
        test_data = [
            ("while (a != 5) { b := b + 7; a := a + 1 }",
             "While (%s. ~s 0 = 5) (%s. true) (Seq (Assign 1 (%s. s 1 + 7)) (Assign 0 (%s. s 0 + 1)))"),

            ("if (a == 0) then a := a + 1 else skip",
             "Cond (%s. s 0 = 0) (Assign 0 (%s. s 0 + 1)) Skip")
        ]

        for s, res in test_data:
            t = parse_hoare(s)
            t_res = parser.parse_term(thy, {}, res)
            self.assertEqual(t, t_res)

    def testParseFile(self):
        process_file("test", "hoare_test_output")


if __name__ == "__main__":
    unittest.main()
