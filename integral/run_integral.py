"""Overall test of integral module."""

import unittest
import json
from pstats import Stats
import cProfile

from logic import basic
from integral import proof
from integral import rules
from integral import inequality
from prover import sympywrapper

test_cases = {
    "tongji7": {
        "Exercise 1": "34/3",
        "Exercise 2": "1/4",
        "Exercise 3": "-1/6 + 1/6 * exp(6)",
        "Exercise 4": "2 * exp(-1) + exp(2)",
        "Exercise 5": "1 + -1/2 * sqrt(2)",
        "Exercise 6": "3/2",
        "Exercise 7": "21/ 8",
        "Exercise 8": "-3/4",
        "Exercise 9": "-81/11 * 2 ^ (2 / 3) + 945/44 * 3 ^ (2 / 3)",
        "Exercise 10": "1 + 1/4 * pi",
        "Exercise 11": "-461/6 + -45 * exp(1) + -3/2 * exp(2) + 1/3 * exp(3)",
        "Exercise 12": "1/4",
        "Exercise 13": "-4/3 + pi",
        "Exercise 14": "-1/8 * sqrt(3) + 1/6 * pi",
        "Exercise 15": "1/4 * pi",
        "Exercise 16": "1/2 * pi",
        "Exercise 17": "2 * sqrt(2) + sqrt(2) * pi",
        "Exercise 18": "1 + -1/4 * pi",
        "Exercise 19": "1/6",
        "Exercise 20": "2 + 2 * log(2) + -2 * log(3)",
        "Exercise 21": "1 + -2 * log(2)",
        "Exercise 22": "1 + -exp(-1/2)",
        "Exercise 23": "-2 + 2 * sqrt(3)",
        "Exercise 24": "1/2 * pi",
        "Exercise 25": "3/8 * pi + -1/4 * sin(-pi)",
        "Exercise 26": "4/3",
        "Exercise 27": "2 * sqrt(2)",
        "Exercise 28": "1 + -2 * exp(-1)",
        "Exercise 29": "1/4 + 1/4 * exp(2)",
        "Exercise 30": "-1/9 * sqrt(3) * pi + 1/4 * pi + -1/2 * log(2) + 1/2 * log(3)",
        "Exercise 31": "-4 + 8 * log(2)",
        "Exercise 32": "-1/2 + 1/4 * pi",
        "Exercise 33": "-2/5 + 1/5 * exp(pi)",
        "Exercise 34": "-1/4 * pi + 1/6 * pi ^ 3",
        "Exercise 35": "1/2 + -1/2 * cos(1) * exp(1) + 1/2 * exp(1) * sin(1)",
        "Exercise 36": "2 + -2 * exp (-1)",
        # "Interesting 1": "1 / 4 * pi",
    },
    "MIT/2013": {
        "Exercise 1": "-2 * exp(1) * log(2) + 2 * log(2)",
        "Exercise 2": "-2 + exp(1) + exp(3)",
        "Exercise 3": "-sin(exp(1)) + 1/2 * sin(exp(2))",
        "Exercise 4": "2500",
        "Exercise 5": "sqrt(3) * pi",
        "Exercise 6": "18 + cos(-3) + -cos(3)",
        "Exercise 7": "log(2)",
        "Exercise 8": "5 / 2",
        "Exercise 9": "-1",
        "Exercise 10": "1 + log(1 + -exp(-2)) + -log(1 + -exp(-1))",
        "Exercise 11": "1 / 8 * pi",
        "Exercise 12": "2 + -2 * cos(-pi)",
        "Exercise 13": "1 + -1/4 * pi",
        # "Exercise 14": None,  # out of range
        "Exercise 15": "24 + -8 * exp(1)",
        # "Exercise 16": "-1/2 + log(2) + log(3 ^ (1/2) * (1/2))",
        "Exercise 17": "exp(1)",
        "Exercise 18": "1/2 + -1/2 * log(2)",
        "Exercise 19": "1/4 * pi",
        # "Exercise 20": "-1 + 2 * log(2) + 3 * log (3 ^ (1 / 2) * (1 / 2))",
        "Exercise 21": "1/2 * log(2) + -1/4 * log(3)",
        "Exercise 22": "3/2 + (1/3) * sqrt(3) * pi",
        "Exercise 23": "418 / 35",
        # "Exercise 24": "2",
        # "Exercise 25": "2 ^ (1/2) * (1/8) * pi + -2 ^ (1/2) * (1/2) * atan(sqrt(14) / 7)"
    },
    "MIT/2014": {
        "Exercise 6": "-9/10 + -1/10 * cos(-pi)",
        "Exercise 8": "1/4062240",
    },
    "MIT/2019": {
        "Exercise 1": "-2/39 * log(cos(39/200 * pi))",
        "Exercise 2": "log(exp(1) + sin(1))",
    },
    "UCDAVIS/usubstitution": {
        "Exercise 1": "209952",
        "Exercise 2": "175099 / 11",
        "Exercise 3": "74 / 21",
        "Exercise 4": "-1/3 + 1/3 * 2 ^ (3/4)",
        "Exercise 5": "-(1/5) * exp(2) + 1/5 * exp(7)",
        "Exercise 6": "4 / 3",
        "Exercise 7": "0",
        "Exercise 8": "-(3/2) * log(2) + 3 * log(3)",
        # "Exercise 9": None,  # non-constant exponent
        "Exercise 10": "3 * log(2)",
        "Exercise 11": "1/5 + -1/5 * exp(-1)",
        "Exercise 12": "1",
        "Exercise 13": "-11 / 21",
        "Exercise 14": "128/15",
        "Exercise 15": "1/2 + -7/4 * log(3) + 7/4 * log(5)",
        "Exercise 16": "-3/2 + -8 * log(2) + 8 * log(3)",
        "Exercise 17": "41 / 6",
        "Exercise 18": "188 / 15"
    },
    "UCDAVIS/Exponentials": {
        "Exercise 1": "-5 + 5 * exp(1)",
        "Exercise 2": "5 + -3 * exp(1)",
        "Exercise 3": "2",
        # "Exercise 4": None,  # out of range
        "Exercise 5": "-149/98 + 3/2 * exp(2) + 1/49 * exp(7)",
        "Exercise 6": "-243/10 + 1/10 * (1 + 2 * exp(1)) ^ 5",
        "Exercise 7": "-2 + -1/8 * exp(-8) + 1/8 * exp(8)",
        "Exercise 8": "-2/3 + exp(1) + -1/3 * exp(3)",
        # "Exercise 9": None,  # out of range
        # "Exercise 10": "((880640/189 - 5/27 * (1 + 3 * exp(-1)) ^ 6) + 20/63 * (1 + 3 * exp(-1)) ^ 7) - 5/36 * (1 + 3 * exp(-1)) ^ 8",  # normalization
        # "Exercise 11": "-16 * 2 ^ (1/2) + 8 * (1 + 6 * exp(1) + exp(2)) ^ (1/2)",
        # "Exercise 12": "-7 * 28 ^ (1/3) + 1/4 * (27 + exp(3)) ^ (4/3)"  # normalization
    },
    "UCDAVIS/Trigonometric": {
        "Exercise 1": "1 / 3",
        "Exercise 2": "1/10 * log(2)",
        "Exercise 3": "5 / 4",
        "Exercise 4": "1 + 1/2 * pi",
        "Exercise 5": "3/4 * pi + 3/20 * sin(-pi)",
        "Exercise 6": "1 + 3/4 * pi + 2 * log(2)",
        "Exercise 7": "2 / 3",
        "Exercise 8": "2/5 * log(2) + -1/5 * log(3)",
        "Exercise 9": "-2 + pi",
        "Exercise 10": "-2 + sqrt(2) + 1/4 * pi",
        # "Exercise 11": "4/3 + -2/3 * sqrt(2) + -1/12 * pi",
        # "Exercise 12": "-16/3 + 4 * sqrt(2) * sqrt(3)",
        "Exercise 13": "-1/4 + 1/2 * log(2)",
        # "Exercise 14": "-7/6",
        "Exercise 15": "-exp(4) + exp(5)",
        "Exercise 16": "1/3 * cos(-1) + -1/3 * cos(1)",
        "Exercise 17": "-3/8 * log(2) ^ 2",
        "Exercise 18": "-14/9 * sqrt(7) + 2/9 * (4 + 3 * sqrt(2)) ^ (3/2)",
        "Exercise 19": "-1/2 + 1/2 * sqrt(2)",
        "Exercise 20": "-1/9",
        "Exercise 21": "-2 + 1/4 * pi^2",
        "Exercise 22": "1 + 1/2 * sqrt(2) * exp(1/2 * sqrt(2)) + -exp(1/2 * sqrt(2))",
        "Exercise 23": "1/2 + 1/2 * exp(1/2 * pi)",
        "Exercise 24": "-3/7",
        # "Exercise 25": "-2 + 2 * (1 + 2 ^ (1/2)) ^ (1/2)",
        "Exercise 26": "-1/4 * log(2)",
        # "Exercise 27": "log(1 + exp(1/2 * pi))",
    },
    "UCDAVIS/Byparts": {
        "Exercise 1": "1",
        "Exercise 2": "1",
        "Exercise 3": "1/4 + 1/4 * exp(2)",
        "Exercise 4": "-1/9 + -1/18 * sqrt(2) + 1/24 * sqrt(2) * pi",
        "Exercise 5": "1/16 + -5/16 * exp(-4)",
        # "Exercise 6": None,  # out of range (arcsin)
        "Exercise 7": "1",
        "Exercise 8": "-1 + 1/2 * pi",
        "Exercise 9": "-5/27 * exp(3) + 26/27 * exp(6)",
        "Exercise 10": "1/16 + 3/16 * exp(4) + 1/4 * exp(4) * log(5) + -1/4 * log(5)",
        "Exercise 11": "-2 + exp(1)",
        "Exercise 12": "6 + -2 * exp(1)",
        "Exercise 13": "-8/5",
        "Exercise 14": "1 / 8",
        "Exercise 15": "2 + -5 * exp(-1)",
        "Exercise 16": "1 / 3",
        "Exercise 17": "-1/2 + 1/32 * pi ^ 2 * sin(1/16 * pi ^ 2) + 1/2 * cos(1/16 * pi ^ 2)",
        "Exercise 18": "-8/135 * sqrt(2) + 5/27 * sqrt(5)",
        "Exercise 19": "-5/36 + -1/2 * log(2) + 1/2 * log(3)",
        "Exercise 20": "1/3 * cos(1) + -1/3 * exp(3) * cos(exp(3)) + -1/3 * sin(1) + 1/3 * sin(exp(3))",
        "Exercise 21": "-1/2 + 1/4 * exp(1)",
        "Exercise 22": "-1/2 + 1/2 * cos(1) * exp(1) + 1/2 * exp(1) * sin(1)",
        "Exercise 23": "-1/4",
    },
    "UCDAVIS/LogAndArctangent": {
        "Exercise 1": "3/2 + 3 * log(2)",
        "Exercise 2": "7 * log(2) + 7 * log(3) + -7 * log(5)",
        "Exercise 3": "-3/2 * atan(-1/2) + 3/2 * atan(1/2)",
        "Exercise 4": "log(2) + -1/2 * log(5)",
        "Exercise 5": "26/3 + -8 * log(3)",
        "Exercise 6": "-4/3 + 1/2 * pi",
        "Exercise 7": "2 * log(2) + -log(3)",
        "Exercise 8": "-1 + 20 * log(2) + -10 * log(3)",
        "Exercise 9": "-atan(2) + atan(3)",
        "Exercise 10": "1/40 * pi + -1/10 * atan(4/5)",
        "Exercise 11": "(-1/6) * pi + 2/3 * atan(4/3)",
        "Exercise 12": "1/2 * log(2)",
        "Exercise 13": "1/4 * pi",
        "Exercise 14": "-log(2) + 1/2 * log(2 + 2 * exp(2))",
        "Exercise 15": "(-1/4) * pi + atan(exp(1))",
        "Exercise 16": "-1/2 + 1/2 * exp(2) + log(2) + -1/2 * log(2 + 2 * exp(2))",
        "Exercise 17": "-1/2 + log(2)",
        "Exercise 18": "-1/8 * pi + 1/2 * atan(1/2) + 3/2 * log(2) + -1/2 * log(5)",
        "Exercise 19": "-13/5 * sqrt(5) * atan(-sqrt(5)) + 13/5 * sqrt(5) * atan(-3/5 * sqrt(5)) + -7/4 * log(3) + -7/4 * log(5) + 7/4 * log(7)",
        "Exercise 20": "1/2 * log(2) + -1/2 * log(1 + exp(-2))",
        "Exercise 21": "-1 + 1/4 * pi + exp(1) + -atan(exp(1))",
        # "Exercise 22": "(7 - 2 * log(5)) + 2 * log(6)",  # order of boundary
    },
    "UCDAVIS/PartialFraction": {
        "Exercise 1": "-1/4 * log(3) + 1/4 * log(5)",
        "Exercise 2": "-5/2 * log(2) + 1/2 * log(5)",
        "Exercise 3": "9/5 * log(2) + 7/5 * log(3) + -7/5 * log(7)",
        "Exercise 4": "1 + -15/4 * log(3) + 15/8 * log(5)",
        "Exercise 5" : "46 / 3 + -(17/3) * log(2) + -3 * log(3) + 13/3 * log(5)",
        "Exercise 6" : "log(2) + log(3) + -(1/2) * log(5)",
        "Exercise 7" : "7/8 + -(5/2) * log(2) + 5/4 * log(3)",
        "Exercise 8" : "127/64 + -(15/4) * log(2) + 31/8 * log(3)",
        "Exercise 9": "-3/8 + log(2)",
        # "Exercise 10": "-1/8 + -15/4 * log(2) + 3/4 * log(3) + 4/3 * log(5)",
        # "Exercise 11": "53/90 + 2/9 * log(2) + 7/27 * log(5)",  # quotient
        # "Exercise 12": "sqrt(3) + 1/2 * log(3) + -(tan(1/12 * pi) ^ -1) + log(tan(1/12 * pi)) + log(1 + -1/3 * sqrt(3)) + -log(1 + -tan(1/12 * pi))",
        "Exercise 13": "1 + 15/2 * log(2) + -9/2 * log(3) + 7/6 * log(5)",
        "Exercise 14": "-1/4 * log(-4 + 4 * exp(1)) + 1/4 * log(-4 + 4 * exp(2)) + 1/4 * log(12 + 4 * exp(1)) + -1/4 * log(12 + 4 * exp(2))",
        "Exercise 15": "1 + log(2) + -log(1 + exp(1))",
        "Exercise 16": "1/4 * pi + -atan(2) + 9/2 * log(2) + -3/2 * log(5)",
        "Exercise 17": "1/50 + 1/125 * atan(1/5) + -1/125 * atan(2/5) + 9/50 * log(2) + 3/50 * log(13) + -3/50 * log(29)",
        "Exercise 18": "-1/16 * atan(1/2) + -1/32 * log(3)",
        "Exercise 19": "1/2 * log(3) + 1/2 * log(5) + -1/2 * log(7)",
        # "Exercise 20": "1/8 * atan(2) + 1/16 * log(5)",
    }
}


class RunIntegral(unittest.TestCase):
    def testRunIntegral(self):
        filenames = [
            "tongji7",
            "MIT/2013",
            "MIT/2014",
            "MIT/2019",
            "UCDAVIS/usubstitution",
            "UCDAVIS/Exponentials",
            "UCDAVIS/Trigonometric",
            "UCDAVIS/Byparts",
            "UCDAVIS/LogAndArctangent",
            "UCDAVIS/PartialFraction",
        ]

        if profile:
            pr = cProfile.Profile()
            pr.enable()

        basic.load_theory('realintegral')
        basic.load_theory('interval_arith')
        for filename in filenames:
            with open('integral/examples/%s.json' % filename, 'r', encoding='utf-8') as f:
                f_data = json.load(f)

            for item in f_data['content']:
                if test_file is None or test_file == filename:
                    if (test_case is None and item['name'] in test_cases[filename]) or \
                       test_case == item['name']:
                        target = test_cases[filename][item['name']]
                        rules.check_item(item, target, debug=True)
                        proof.translate_item(item, target, debug=True)

        if profile:
            p = Stats(pr)
            p.strip_dirs()
            p.sort_stats('cumtime')
            p.print_stats(100)


if __name__ == "__main__":
    import sys, getopt
    opts, args = getopt.getopt(sys.argv[1:], 'pf:c:')

    profile = False
    test_file = None
    test_case = None
    for opt, arg in opts:
        if opt == '-p':
            profile = True
        if opt == '-f':
            test_file = arg
        if opt == '-c':
            test_case = arg

    sys.argv = sys.argv[:1]  # remove own arguments for unittest
    unittest.main()
