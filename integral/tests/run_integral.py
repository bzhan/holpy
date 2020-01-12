"""Overall test of integral module."""

import unittest
import json

from integral import proof

test_cases = {
    "Exercise 1": "34 / 3",
    "Exercise 2": "1 / 4",
    "Exercise 3": "-(1 / 6) + (1 / 6) * exp(6)",
    "Exercise 4": "exp(2) + 2 * exp(-1)",
    "Exercise 5": "1 + -1/2 * sqrt(2)",
    "Exercise 7": "21 / 8",
    "Exercise 12": "1 / 4",
    "Exercise 13": "-(4 / 3) + pi",
    "Exercise 14": "1 / 6 * pi + -(1 / 8) * sqrt(3)"
}

class RunIntegral(unittest.TestCase):
    def testRunIntegral(self):
        with open('integral/examples/ref_test.json', 'r', encoding='utf-8') as f:
            f_data = json.load(f)

        for item in f_data['content']:
            if item['name'] in test_cases:
                target = test_cases[item['name']]
                proof.translate_item(item, target)


if __name__ == "__main__":
    unittest.main()
