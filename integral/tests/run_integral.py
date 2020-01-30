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
        "Exercise 18": "1 - 1/4 * pi",
        "Exercise 19": "1 / 6",
        "Exercise 20": "2 + 2 * log(2) - 2 * log(3)",
        # "Exercise 21": "1 - 2 * log(2)",
        "Exercise 22": "1 - exp (-1/2)",
        "Exercise 23": "-2 + 2 * 3 ^ (1/2)",
        "Exercise 24": "1/2 * pi",
        "Exercise 25": "3 / 8 * pi",
        "Exercise 26": "4 / 3",
        "Exercise 27": "2 * 2 ^ (1 / 2)",
        "Exercise 28": "1 - 2 * exp(-1)",
        "Exercise 29": "1 / 4 + 1 / 4 * exp(2)",
        "Exercise 30": "((1/4 - 3 ^ (1/2) * (1/9)) * pi - log(2 ^ (1/2) * (1/2))) + log(3 ^ (1/2) * (1/2))",
        "Exercise 31": "-4 + 4 * log(4)",
        "Exercise 32": "-(1 / 2) + 1 / 4 * pi",
        "Exercise 33": "-(2 / 5) + 1 / 5 * exp(pi)",
        "Exercise 34": "-(1 / 4) * pi + 1 / 6 * pi ^ 3",
        "Exercise 35": "1/2 + -(1/2) * cos(1) * exp(1) + 1/2 * sin(1) * exp(1)",
        "Exercise 36": "2 - 2 * exp (-1)",
        "Interesting 1": "1 / 4 * pi",
    },
    "2013": {
        "Exercise 1": "2 * log(2) + 2 * exp(1) + -2 * log(2 * exp(1)) * exp(1)",
        "Exercise 2": "-2 + exp(1) + exp(3)",
        "Exercise 3": "-sin(exp(1)) + 1/2 * sin(exp(2))",
        "Exercise 4": "2500",
        "Exercise 5": "3 ^ (1/2) * pi",
        "Exercise 6": "18",
        # "Exercise 7": "log(2)",
        "Exercise 8": "5 / 2",
        # "Exercise 9": None,
        "Exercise 10": "(1 - log(1 - exp(-1))) + log(1 - exp(-2))",
        "Exercise 11": "1 / 8 * pi",
        # "Exercise 12": "4",
        "Exercise 13": "1 - 1/4 * pi",
        # "Exercise 14": "24 - 8 * e",
        # "Exercise 15": None,
        # "Exercise 16": "e * log(e)^2",   # TypeError
        "Exercise 18": "1/2 - 1/2 * log(2)",
        "Exercise 19": "1/4 * pi",
        "Exercise 20": "-1 + 2 * log(2) + 3 * log (3 ^ (1 / 2) * (1 / 2))",
        # "Exercise 21": None,
        # "Exercise 25": "1 / 24 * (pi * 2 ^ (1 / 2))",
    },
    "2014": {
        "Exercise 6": "-(4 / 5)",
    },
    "2019": {
        "Exercise 1": "-2/39 * log(cos(39 * pi / 200))",
        "Exercise 2": "log (sin(1) + exp(1))",
    },
    "UCDAVIS/usubstitution": {
        "Exercise 1": "209952",
        "Exercise 2": "175099 / 11",
        "Exercise 3": "74 / 21",
        "Exercise 4": "-1/3 + 1/3 * 2 ^ (3/4)",
        "Exercise 5": "-(1/5) * exp(2) + 1/5 * exp(7)",
        "Exercise 6": "4 / 3",
        "Exercise 7": "0",
        # "Exercise 8": "3/2 * log(2) - 3/2 * log(3)",
        # "Exercise 9": None,
        "Exercise 10": "3 * log(2)",
        "Exercise 11": "1/5 - 1/5 * exp(-1)",
        "Exercise 12": "1",
        "Exercise 13": "-11 / 21",
        "Exercise 14": "128 / 15",
        # "Exercise 15": "(1/2 - 7/4 * log(3)) + 7/4 * log(5)",
        "Exercise 16": "(-(3/2) - 8 * log(2)) + 8 * log(3)",
        "Exercise 17": "41 / 6",
        "Exercise 18": "188 / 15"
    },
    "UCDAVIS/Exponentials": {
        "Exercise 1": "-5 + 5 * exp(1)",
        "Exercise 2": "5 - 3 * exp(1)",
        "Exercise 3": "2",
        # "Exercise 4": None,
        "Exercise 5": "-149/98 + 3/2 * exp(2) + 1/49 * exp(7)",
        "Exercise 6": "-243/10 + 1/10 * (1 + 2 * exp(1)) ^ 5",
        "Exercise 7": "(-2 - 1/8 * exp(-8)) + 1/8 * exp(8)",
        "Exercise 8": "(-(2/3) + exp(1)) - 1/3 * exp(3)",
        # "Exercise 9": None,
        # "Exercise 10": "((880640/189 - 5/27 * (1 + 3 * exp(-1)) ^ 6) + 20/63 * (1 + 3 * exp(-1)) ^ 7) - 5/36 * (1 + 3 * exp(-1)) ^ 8",
        "Exercise 11": "-16 * 2 ^ (1/2) + 8 * (1 + 6 * exp(1) + exp(2)) ^ (1/2)",
        # "Exercise 12": "-7 * 28 ^ (1/3) + 1/4 * (27 + exp(3)) ^ (4/3)"
    },
    "UCDAVIS/Trigonometric": {
        "Exercise 1": "1 / 3",
        "Exercise 2": "(-1/5) * log(2 ^ (1/2) * (1/2))",
        "Exercise 3": "5 / 4",
        "Exercise 4": "1 + 1/2 * pi",
        "Exercise 5": "3/4 * pi",
        "Exercise 6": "(1 + 3/4 * pi) - 4 * log(2 ^ (1/2) * (1/2))",
        "Exercise 7": "2 / 3",
        # "Exercise 8": "-(1/5) * log(3) + 1/5 * log(4)",
        "Exercise 9": "-2 + pi",
        "Exercise 10": "-2 + 2 ^ (1/2) + 1/4 * pi",
        "Exercise 11": "(-2 * 2 ^ (1/2) * (1/3) + 4/3) - 1/12 * pi",
        "Exercise 12": "-16/3 + 4 * 6 ^ (1/2)",
        "Exercise 13": "-1/4 - log(2 ^ (1/2) * (1/2))",
        "Exercise 14": "-7/6",
        "Exercise 15": "-exp(4) + exp(5)",
        "Exercise 16": "0",
        "Exercise 17": "-(1/2) * log(2) ^ 2 + 1/2 * log(2 ^ (1/2) * (1/2)) ^ 2",
        "Exercise 18": "-14 * 7 ^ (1/2) * (1/9) + 2/9 * (4 + 3 * 2 ^ (1/2)) ^ (3/2)",
        "Exercise 19": "-1/2 + 2 ^ (1/2) * (1/2)",
        "Exercise 20": "-1/9",
        "Exercise 21": "-2 + 1/4 * pi^2",
        "Exercise 22": "1 + (-1 + 2 ^ (1/2) * (1/2)) * exp(2 ^ (1/2) * (1/2))",
        "Exercise 23": "1/2 + 1/2 * exp(1/2 * pi)",
        "Exercise 24": "-3/7",
        # "Exercise 25": None,
        "Exercise 26": "1 / 2 * log (2 ^ (1 / 2) * (1 / 2))",
        "Exercise 27": "log(1 + exp(1/2 * pi))",
    },
    "Byparts": {
        "Exercise 1": "1",
        "Exercise 2": "1",
        "Exercise 3": "1/4 + 1/4 * exp(2)",
        "Exercise 4": "(-1/9 - 2 ^ (1/2) * (1/18)) + 2 ^ (1/2) * (1/24) * pi",
        "Exercise 5": "1/16 - 5/16 * exp(-4)",
        # "Exercise 6": None,
        "Exercise 7": "1",
        "Exercise 8": "-1 + 1/2 * pi",
        "Exercise 9": "-5/27 * exp(3) + 26/27 * exp(6)",
        "Exercise 10": "(1/16 - 1/4 * log(5) - 1/16 * exp(4)) + 1/4 * log(5 * exp(1)) * exp(4)",
        "Exercise 11": "-2 + exp(1)",
        "Exercise 12": "6 - 2 * exp(1)",
        "Exercise 13": "-8/5",
        "Exercise 14": "1 / 8",
        "Exercise 15": "2 - 5 * exp(-1)",
        "Exercise 16": "1 / 3",
        "Exercise 17": "-1/2 + 1/32 * pi ^ 2 * sin(pi ^ 2 / 16) + 1/2 * cos(pi ^ 2 / 16)",
        "Exercise 18": "-8 * 2 ^ (1/2) * (1/135) + 5 ^ (3/2) * (1/27)",
        # "Exercise 19": "((-5/36) - 1/2 * log(6)) + 1/2 * log(9)",
        "Exercise 20": "(1/3 * cos(1) - 1/3 * sin(1)) + (-1/3) * cos(exp(3)) * exp(3) + 1/3 * sin(exp(3))",
        # "Exercise 21": "-1/2 + 1/4 * exp(1)",
        "Exercise 22": "-1/2 + 1/2 * cos(1) * exp(1) + 1/2 * sin(1) * exp(1)",
        "Exercise 23": "-1/4",
    },
    "UCDAVIS/LogAndArctangent": {
        "Exercise 1": "3/2 + 3 * log(2)",
        "Exercise 2": "-7 * log(5) + 7 * log(6)",
        "Exercise 3": "3 * atan(1/2)",
        "Exercise 4": "1/2 * log(4) - 1/2 * log(5)",
        "Exercise 5": "26/3 - 8 * log(3)",
        "Exercise 6": "-4/3 + 1/2 * pi",
        # "Exercise 7": "-log(3) + log(4)",
        # "Exercise 8": "(-1 - 10 * log(3)) + 10 * log(4)",
        "Exercise 9": "-atan(2) + atan(3)",
        # "Exercise 10": "1/40 * pi - 1/10 * atan(4/5)",
        # "Exercise 11": "(-1/6) * pi + 2/3 * atan(4/3)",
        # "Exercise 12": "0",
        "Exercise 13": "1/4 * pi",
        "Exercise 14": "(-1/2) * log(2) + 1/2 * log(1 + exp(2))",
        "Exercise 15": "(-1/4) * pi + atan(exp(1))",
        "Exercise 16": "((-1/2) + 1/2 * log(2) + 1/2 * exp(2)) - 1/2 * log(1 + exp(2))",
        "Exercise 17": "-1/2 + log(2)",
        "Exercise 18": "((-1/8) * pi - 1/2 * log(5/4)) + 1/2 * atan(1/2) + 1/2 * log(2)",
        # "Exercise 19": "(7/4 * log(14) - 7/4 * log(30)) + 13 * 5 ^ (1/2) * (1/5) * atan(sqrt(5)) + -13 * 5 ^ (1/2) * (1/5) * atan((3 * sqrt(5)) / 5)",
        # "Exercise 20": "1/2 * log(2) - 1/2 * log(1 + exp(-2))",
        "Exercise 21": "(-1 + 1/4 * pi + exp(1)) - atan(exp(1))",
        # "Exercise 22": "(7 - 2 * log(5)) + 2 * log(6)",
    }
}


class RunIntegral(unittest.TestCase):
    def testRunIntegral(self):
        filenames = [
            # "test",
            # "2013",
            # "2014",
            # "2019",
            # "UCDAVIS/usubstitution",
            # "UCDAVIS/Exponentials",
            # "UCDAVIS/Trigonometric",
            # "Byparts",
            "UCDAVIS/LogAndArctangent"
        ]
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
