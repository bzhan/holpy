# Author: Bohua Zhan

import unittest

from logic import basic
from imperative import parser2

thy = basic.load_theory('nat')

class Parser2Test(unittest.TestCase):
    def testParsePrint(self):
        test_case = [
            ("while (a != A) [b == a * B] {b := b + B; a := a + 1}",
             "while (a != A) {\n  [b == a * B]\n  b := b + B;\na := a + 1\n}"),

            ("if (a != 0) then a := 0 else skip",
             "if (a != 0) then\n  a := 0\nelse\n  skip"),

            ("if (m <= n) then c := n else c := m",
             "if (m <= n) then\n  c := n\nelse\n  c := m")
        ]

        for s, res in test_case:
            com = parser2.com_parser.parse(s)
            self.assertEqual(com.print_com(thy), res)

if __name__ == "__main__":
    unittest.main()
