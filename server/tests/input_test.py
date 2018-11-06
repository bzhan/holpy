# Author: Bohua Zhan

import unittest
from server.input import get_unicode_table_suffix

class InputTest(unittest.TestCase):
    def testUnicodeTable(self):
        test_data = [
            ("A &", "∧"),
            ("A -->", "⟶"),
            ("A \\and", "∧"),
        ]

        for s, res in test_data:
            self.assertEqual(get_unicode_table_suffix(s), res)

if __name__ == "__main__":
    unittest.main()
