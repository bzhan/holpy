"""Overall test of integral module."""

import unittest
import json

from integral import proof
from prover import sympywrapper

test_cases = {
    "Exercise 1": "34 / 3",
    "Exercise 2": "1 / 4",
    "Exercise 3": "-(1 / 6) + (1 / 6) * exp(6)",
    "Exercise 4": "exp(2) + 2 * exp(-1)",
    "Exercise 5": "1 + -1/2 * 2 ^ (1/2)",
    "Exercise 7": "21 / 8",
    "Exercise 8": None,
    "Exercise 9": "-(81 / 11) * 2 ^ (2 / 3) + 945 / 44 * 3 ^ (2 / 3)",
    "Exercise 10": None,
    "Exercise 11": "-(136 / 3) + -27 * exp(1) + -(9 / 2) * (3 + exp(1)) ^ 2 + 1 / 3 * (3 + exp(1)) ^ 3",
    "Exercise 12": "1 / 4",
    "Exercise 13": "-(4 / 3) + pi",
    "Exercise 14": "1 / 6 * pi + -(1 / 8) * 3 ^ (1/2)",
    "Exercise 15": "1 / 4 * pi",
    "Exercise 16": "1 / 2 * pi",
    "Exercise 17": None,
    "Exercise 18": None,
    "Exercise 19": "1 / 6",
    "Exercise 20": "2 + 2 * log(2) + -2 * log(3)",
    "Exercise 21": None,
    "Exercise 22": "1 + -1 * exp (-1/2)",
    "Exercise 23": "-2 + 2 * 3 ^ (1/2)",
    "Exercise 24": None,
    "Exercise 28": "1 + -2 * exp(-1)",
    "Exercise 29": "1 / 4 + 1 / 4 * exp(2)",
    "Exercise 31": "-4 + 4 * log(4)",
    "Exercise 36": "2 + -2 * exp (-1)",
}


class RunIntegral(unittest.TestCase):
    def testRunIntegral(self):
        with open('integral/examples/ref_test.json', 'r', encoding='utf-8') as f:
            f_data = json.load(f)

        for item in f_data['content']:
            if item['name'] in test_cases:
                target = test_cases[item['name']]
                proof.translate_item(item, target, debug=True)


if __name__ == "__main__":
    unittest.main()
