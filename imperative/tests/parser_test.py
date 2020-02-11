# Author: Bohua Zhan

import unittest

from logic import basic
from imperative import imp
from imperative.parser import parse_com, process_file
from syntax import parser

basic.load_theory('hoare')


class HoareParserTest(unittest.TestCase):
    def testHoareParser(self):
        test_data = [
            ("while (a != 5) { b := b + 7; a := a + 1 }",
             "While (%s. ~s (0::nat) = (5::nat)) (%s. true) (Seq (Assign 1 (%s. s 1 + 7)) (Assign 0 (%s. s 0 + 1)))"),

            ("if (a == 0) then a := a + 1 else skip",
             "Cond (%s. s (0::nat) = (0::nat)) (Assign 0 (%s. s 0 + 1)) Skip")
        ]

        for s, res in test_data:
            t = parse_com(s)
            t_res = parser.parse_term(res)
            self.assertEqual(t, t_res)

    def testParseFile(self):
        process_file("test", "hoare_test_output")


if __name__ == "__main__":
    unittest.main()
