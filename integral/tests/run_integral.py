"""Overall test of integral module."""

import unittest
import json
from pstats import Stats
import cProfile

from integral import proof
from prover import sympywrapper

test_cases = {
    "test": {
        "Exercise 1": "34 / 3",
        "Exercise 2": "1 / 4",
        "Exercise 3": "-(1 / 6) + (1 / 6) * exp(6)",
        "Exercise 4": "2 * exp(-1) + exp(2)",
        "Exercise 5": "1 - 1/2 * 2 ^ (1/2)",
        # "Exercise 6": None,
        "Exercise 7": "21 / 8",
        "Exercise 8": "-(3 / 4)",
        "Exercise 9": "1 / 11 * -81 * 2 ^ (2 / 3) + 1 / 44 * 945 * 3 ^ (2 / 3)",
        "Exercise 10": "1 + 1 / 4 * pi",
        "Exercise 11": "(-(136/3) - 27 * exp(1) - 9/2 * (3 + exp(1)) ^ 2) + 1/3 * (3 + exp(1)) ^ 3",
        "Exercise 12": "1 / 4",
        "Exercise 13": "-(4 / 3) + pi",
        "Exercise 14": "1/8 * -(3 ^ (1/2)) + 1/6 * pi",
        "Exercise 15": "1 / 4 * pi",
        "Exercise 16": "1 / 2 * pi",
        "Exercise 17": "2 * 2 ^ (1 / 2) + 2 ^ (1 / 2) * pi",
        # "Exercise 18": None,
        "Exercise 19": "1 / 6",
        "Exercise 20": "2 + 2 * log(2) - 2 * log(3)",
        # "Exercise 21": None,
        "Exercise 22": "1 - exp (-1/2)",
        "Exercise 23": "-2 + 2 * 3 ^ (1/2)",
    # need test (split)   # "Exercise 24": "1 / 2 * pi",
        "Exercise 25": "3 / 8 * pi",
    # need test (split)   # "Exercise 26": "4 / 3",
    #    "Exercise 27": "2 * 2 ^ (1 / 2)",
        "Exercise 28": "1 - 2 * exp(-1)",
        "Exercise 29": "1 / 4 + 1 / 4 * exp(2)",
        # "Exercise 30": None,
        "Exercise 31": "-4 + 4 * log(4)",
        "Exercise 32": "-(1 / 2) + 1 / 4 * pi",
        "Exercise 33": "-(2 / 5) + 1 / 5 * exp(pi)",
        "Exercise 34": "-(1 / 4) * pi + 1 / 6 * pi ^ 3",
        "Exercise 35": "1 / 2 + -(1 / 2) * (cos(1) * exp(1)) + 1 / 2 * (exp(1) * sin(1))",
    # need test (split)    # "Exercise 36": "2 + -2 * exp (-1)",
        "Interesting 1": "1 / 4 * pi",
    },
    "2013": {
        "Exercise 2": "-2 + exp 1 + exp 3",
        "Exercise 6": "18",
        "Exercise 8": "7 / 2",
        "Exercise 10": "-1 * log (-1 + exp(1)) + log (-1 + exp(2))",
        "Exercise 11": "1 / 8 * pi",
        "Exercise 20": "-1 + -2 * log (1 / 2) + 3 * log (1 / 2 * 3 ^ (1 / 2))",
        "Exercise 25": "1 / 24 * (pi * 2 ^ (1 / 2))",
    },
    "2014": {
        "Exercise 6": "-(4 / 5)",
    },
    "2019": {
        "Exercise 1": "-2/39 * log(cos(39 * pi / 200))",
        "Exercise 2": "log (sin(1) + exp(1))",
    }
}


class RunIntegral(unittest.TestCase):
    def testRunIntegral(self):
        filenames = ["test", "2019"]
        test_only = None
        profile = False

        if profile:
            pr = cProfile.Profile()
            pr.enable()

        for filename in filenames:
            with open('integral/examples/%s.json' % filename, 'r', encoding='utf-8') as f:
                f_data = json.load(f)

            for item in f_data['content']:
                if (test_only and test_only[0] == filename and test_only[1] == item['name']) or \
                   (not test_only and item['name'] in test_cases[filename]):
                    target = test_cases[filename][item['name']]
                    proof.translate_item(item, target, debug=True)

        if profile:
            p = Stats(pr)
            p.strip_dirs()
            p.sort_stats('cumtime')
            p.print_stats()


if __name__ == "__main__":
    unittest.main()
