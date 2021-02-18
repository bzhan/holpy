import unittest
import json
import cProfile
from integral import slagle
import time

test_cases = {
    "tongji": {
        "Exercise 1": "INT x:[2,3]. 2 * x + x ^ 2",
        "Exercise 2": "INT x:[0,1]. (3 * x + 1) ^ (-2)",
        "Exercise 3": "INT x:[0,1]. exp(6*x)",
        "Exercise 4": "INT x:[-1,2]. x * exp(x)",
        "Exercise 5": "INT x:[0,pi/4]. sin(x)",
        "Exercise 6": "INT x:[0,1]. 3*x^2 - x + 1",
        "Exercise 7": "INT x:[1,2]. x^2 + 1/x^4",
        "Exercise 8": "INT x:[pi/3, pi]. sin(2*x+pi/3)",
        "Exercise 9": "INT x:[4, 9]. x ^ (1 / 3) * (x ^ (1 / 2) + 1)",
        "Exercise 12": "INT x:[0, pi / 2]. sin(x) * cos(x) ^ 3",
        "Exercise 13": "INT x:[0, pi]. (1 - sin(x)^3)",
        "Exercise 14": "INT x:[pi/6, pi/2]. cos(x) ^ 2",
        "Exercise 15": "INT x:[0, 1]. (1 - x^2) ^ (1/2)",
        "Exercise 16": "INT x:[0, sqrt(2)]. sqrt(2 - x^2)",
        "Exercise 17": "INT y:[-sqrt(2), sqrt(2)]. sqrt(8 - 2*y^2)",
        "Exercise 19": "INT x:[-1, 1]. x / sqrt(5 - 4 * x)",
        "Exercise 21": "INT x:[3/4, 1]. 1/(sqrt(1-x) - 1)",
        "Exercise 22": "INT t:[0, 1]. t * exp(-t ^ 2 / 2)",
        "Exercise 23": "INT x:[1, exp(2)]. 1 / (x*sqrt(1+log(x)))",
        "Exercise 28": "INT x:[0, 1].x*exp(-x)",
        "Exercise 29": "INT x:[1, exp(1)]. x * log(x)",
        "Exercise 31": "INT x:[1, 4]. log(x) / sqrt(x)"
    },

    "MIT/2013": {
        "Exercise 2": "INT x:[-1, 3].exp(abs(x))",
        "Exercise 4": "INT x:[1, 11].x^3 - 3*x^2 + 3*x - 1",
        "Exercise 6": "INT x:[0, 6].x+(x - 3)^7 + sin(x - 3)",
        "Exercise 8": "INT x:[1, 2].(x^5 - x^3 + x^2 - 1) / (x^4 - x^3 + x - 1)",
        "Exercise 12": "INT x:[0, 441]. (pi * sin(pi*sqrt(x))) / sqrt(x)",
        "Exercise 19": "INT x:[0, 1].1/(2 - 2*x + x^2)",
    },
    
    "MIT/2014": {
        "Exercise 1": "2",
    },

    "UCDAVIS/usubstitution": {
        "Exercise 1": "209952",
        "Exercise 2":"175099/11",
        "Exercise 3": "74/21",
        "Exercise 4": "-1/3 + 1/3 * 2 ^ (3/4)",
        "Exercise 5": "-1/5 * exp(2) + 1/5 * exp(7)",
        "Exercise 6": "4/3",
        "Exercise 7": "0",
        "Exercise 8": "-3/2 * log(2) + 3/2 * log(9)",
        "Exercise 12": "1",
        "Exercise 13": "-11/21",
        "Exercise 14": "128/15 + -8/3 * 0 ^ (3/2) + 2/5 * 0 ^ (5/2)",
        "Exercise 17": "41/6",
    },
    
    "UCDAVIS/Exponentials": {
        "Exercise 1" : "-5 + 5 * exp(1)",
        "Exercise 2" : "5 + -3 * exp(1)",
        "Exercise 3" : "-2 + 2 * exp(log(2))",
        "Exercise 5" : "-149/98 + 3/2 * exp(2) + 1/49 * exp(7)",
        "Exercise 6" : "-121/5 + exp(1) + 4 * exp(2) + 8 * exp(3) + 8 * exp(4) + 16/5 * exp(5)",
        "Exercise 7" : "-2 + -1/8 * exp(-8) + 1/8 * exp(8)",
        "Exercise 8" : "-2/3 + exp(1) + -1/3 * exp(3)",
    },

    "UCDAVIS/Trigonometric": {
        "Exercise 1" : "1/3",
        "Exercise 2" : "-1/5 * log(abs(1/2 * sqrt(2)))",
        "Exercise 3" : "5/4",
        "Exercise 5" : "3/4 * pi + -3/20 * sin(-pi)",
        "Exercise 8" : "-1/5 * log(15) + 1/5 * log(20)",
        "Exercise 12" : "-16/3 + 4 * sqrt(2) * sqrt(3)",
        "Exercise 15" : "-exp(4) + exp(5)",
        "Exercise 16" : "1/3 * cos(-1) + -1/3 * cos(1)",
        "Exercise 17" : "1/2 * log(1/2) * log(2) + 1/8 * log(2) ^ 2",
        "Exercise 19" : "-sin(exp(log(1/6) + log(pi))) + sin(exp(log(1/4) + log(pi)))",
        "Exercise 25" : "-2 + 2 * sqrt(1 + sqrt(2))",
    },

    "UCDAVIS/Byparts": {
        "Exercise 1" : "1",
        "Exercise 2" : "1",
        "Exercise 3" : "1/4 + 1/4 * exp(2)",
        "Exercise 4" : "-1/9 + -1/18 * sqrt(2) + 1/24 * sqrt(2) * pi",
        "Exercise 5" : "1/16 + -5/16 * exp(-4)",
        "Exercise 9" : "-5/27 * exp(3) + 26/27 * exp(6)",
        "Exercise 12" : "6 + -2 * exp(1)",
        "Exercise 13" : "-8/5",
        "Exercise 15" : "2 + -5 * exp(-1)",
    }
}


tongji_not_solved = [
    10, 11, 18, 24
]

class RunSlagle(unittest.TestCase):
    def testRunSlagle(self):
        file_names = [
            # "tongji7",
            # "MIT/2013",
            # "MIT/2014",
            # "MIT/2019",
            # "UCDAVIS/usubstitution",
            # "UCDAVIS/Exponentials",
            # "UCDAVIS/Trigonometric",
            "UCDAVIS/Byparts",
            # "UCDAVIS/LogAndArctangent",
            # "UCDAVIS/PartialFraction",
        ]

        for filename in file_names:
            with open("integral/examples/%s.json" % filename, "r", encoding="utf-8") as f:
                f_data = json.load(f)

            for item in f_data["content"]:
                test_case = item["problem"]
                item_num = int(item["name"].split(" ")[1])
                if item_num in tongji_not_solved:
                    continue
                time1 = time.perf_counter()
                try:
                    result = slagle.Slagle(20).eval(test_case)
                except:
                    print(item["name"], "Error")
                    continue
                time2 = time.perf_counter()
                if result is None:
                    continue
                if result.is_constant():
                    # print(item["name"], result, "%.3fs"%(time2 - time1))
                    print("\"%s\" : \"%s\"," % (item["name"], result))
                elif result is None:
                    print(item["name"], "Timeout!")
                else:
                    print()

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