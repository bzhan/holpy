# Author: Bohua Zhan

import unittest

from logic import basic
from imperative import parser2
from imperative import imp

thy = basic.load_theory('int')

class Parser2Test(unittest.TestCase):
    def testParsePrint(self):
        test_case = [
            ("while (a != A) {[b == a * B] b := b + B; a := a + 1}",
             "while (a != A) {\n  [b == a * B]\n  b := b + B;\n  a := a + 1\n}"),

            ("if (a != 0) then a := 0 else skip",
             "if (a != 0) then\n  a := 0\nelse\n  skip"),

            ("if (m <= n) then c := n else c := m",
             "if (m <= n) then\n  c := n\nelse\n  c := m"),

            ("m := a + b; n := a - b",
             "m := a + b;\nn := a - b"),
        ]

        for s, res in test_case:
            com = parser2.com_parser.parse(s)
            lines = com.print_com({'a': 'int', 'b': 'int', 'A': 'int', 'B': 'int', 'm': 'int', 'n': 'int'})
            self.assertEqual('\n'.join(lines), res)

    def testParseFile(self):
        parser2.process_file("test")


if __name__ == "__main__":
    unittest.main()
