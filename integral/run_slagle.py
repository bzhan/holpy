import unittest
import json
import cProfile
from integral import slagle
from integral import rules
import time

test_cases = {
    "tongji7": {
        "Exercise 1" : "34/3",
        "Exercise 2" : "1/4",
        "Exercise 3" : "-1/6 + 1/6 * exp(6)",
        "Exercise 4" : "2 * exp(-1) + exp(2)",
        "Exercise 5" : "1 + -1/2 * sqrt(2)",
        "Exercise 6" : "3/2",
        "Exercise 7" : "21/8",
        "Exercise 8" : "-3/4",
        "Exercise 9" : "-81/11 * 2 ^ (2/3) + 945/44 * 3 ^ (2/3)",
        "Exercise 10" : "1 + 1/4 * pi",
        "Exercise 11" : "277/6 + -45 * exp(1) + -3/2 * exp(2) + 1/3 * exp(3) + -123 * log(abs(exp(1)))",
        "Exercise 12" : "1/4",
        "Exercise 14" : "-1/8 * sqrt(3) + 1/6 * pi",
        "Exercise 15" : "1/4 * pi",
        "Exercise 16" : "1/2 * pi",
        "Exercise 17" : "2 * sqrt(2) + sqrt(2) * pi",
        "Exercise 18" : "1 + -1/4 * pi",
        "Exercise 19" : "1/6",
        "Exercise 20" : "2 + 2 * log(2) + -2 * log(3)",
        "Exercise 21" : "1 + 2 * log(1/2)",
        "Exercise 22" : "1 + -exp(-1/2)",
        "Exercise 23" : "-2 + 2 * sqrt(3)",
        "Exercise 28" : "1 + -2 * exp(-1)",
        "Exercise 29" : "1/4 + 1/4 * exp(2)",
        "Exercise 31" : "-4 + 4 * log(4)",
        "Exercise 32" : "-1/2 + 1/4 * pi",
        "Exercise 34" : "-1/4 * pi + 1/6 * pi ^ 3",
    },

    "MIT/2013": {
        "Exercise 2" : "-2 + exp(1) + exp(3)",
        "Exercise 4" : "2500",
        "Exercise 5" : "sqrt(3) * pi",
        "Exercise 6" : "18 + cos(-3) + -cos(3)",
        "Exercise 15" : "-8 * exp(1) + -24 * 0 ^ (1/4) * exp(0 ^ (1/4)) + 12 * (0 ^ (1/4)) ^ 2 * exp(0 ^ (1/4)) + -4 * (0 ^ (1/4)) ^ 3 * exp(0 ^ (1/4)) + 24 * exp(0 ^ (1/4))",
        "Exercise 19" : "1/4 * pi",
    },
    
    "MIT/2014": {
        "Exercise 1": "2",
        "Exercise 5" : "-4 + 2 * exp(1)",
        "Exercise 7" : "4 * sqrt(3) + 2/3 * pi",
    },

    # "MIT/2019": {
    #     # "Exercise 2": "log(abs(exp(1) + sin(1)))",
    # },

    "MIT/2020": {
        "Exercise 3": "1/4 + 1/4 * exp(2)",
        "Exercise 5": "1/2 * pi"
    },

    "UCDAVIS/usubstitution": {
        # "Exercise 1" : "209952",
        "Exercise 2" : "175099/11",
        "Exercise 3" : "74/21",
        "Exercise 4" : "-1/3 + 1/3 * 2 ^ (3/4)",
        "Exercise 5" : "-1/5 * exp(2) + 1/5 * exp(7)",
        "Exercise 6" : "4/3",
        "Exercise 7" : "0",
        "Exercise 10" : "3 * log(2)",
        "Exercise 11" : "1/5 + -1/5 * exp(-1)",
        "Exercise 12" : "1",
        "Exercise 13" : "-11/21",
        "Exercise 14" : "128/15 + -8/3 * 0 ^ (3/2) + 2/5 * 0 ^ (5/2)",
        "Exercise 15" : "1/2 + -7/4 * log(6) + 7/4 * log(10)",
        "Exercise 16" : "-3/2 + -8 * log(2) + 8 * log(3)",
        "Exercise 17" : "41/6",
        "Exercise 18" : "188/15",
    },
    
    "UCDAVIS/Exponentials": {
        "Exercise 1" : "-5 + 5 * exp(1)",
        "Exercise 2" : "5 + -3 * exp(1)",
        "Exercise 3" : "-2 + 2 * exp(log(2))",
        "Exercise 5" : "-149/98 + 3/2 * exp(2) + 1/49 * exp(7)",
        "Exercise 6" : "-121/5 + exp(1) + 4 * exp(2) + 8 * exp(3) + 8 * exp(4) + 16/5 * exp(5)",
        "Exercise 7" : "-2 + -1/8 * exp(-8) + 1/8 * exp(8)",
        "Exercise 8" : "-2/3 + exp(1) + -1/3 * exp(3)",
        "Exercise 10" : "130465/28 + -3645/4 * exp(-8) + -12150/7 * exp(-7) + -1350 * exp(-6) + -540 * exp(-5) + -225/2 * exp(-4) + -10 * exp(-3)",
    },

    "UCDAVIS/Trigonometric": {
        "Exercise 1" : "1/3",
        "Exercise 2" : "1/10 * log(2)",
        "Exercise 3" : "5/4",
        "Exercise 4" : "1 + 1/2 * pi",
        "Exercise 5" : "3/4 * pi + 3/20 * sin(-pi)",
        "Exercise 6" : "1 + 3/4 * pi + -2 * log(1/2)",
        "Exercise 7" : "2/3 + -(0 ^ (1/2)) + 1/3 * 0 ^ (3/2)",
        "Exercise 8" : "-1/5 * log(15) + 1/5 * log(20)",
        "Exercise 12" : "-16/3 + 4 * sqrt(2) * sqrt(3)",
        "Exercise 13" : "-1/4 + -1/2 * log(1/2)",
        "Exercise 15" : "-exp(4) + exp(5)",
        "Exercise 16" : "1/3 * cos(-1) + -1/3 * cos(1)",
        "Exercise 17" : "1/2 * log(1/2) * log(2) + 1/8 * log(2) ^ 2",
        "Exercise 19" : "-sin(exp(log(1/6) + log(pi))) + sin(exp(log(1/4) + log(pi)))",
        "Exercise 20" : "-1/9",
        "Exercise 21" : "-2 + 1/4 * pi ^ 2",
        "Exercise 22" : "1 + 1/2 * sqrt(2) * exp(1/2 * sqrt(2)) + -exp(1/2 * sqrt(2))",
        "Exercise 25" : "-2 + 2 * sqrt(1 + sqrt(2))",
        
        # Exercise 9 Can't Solve.
        # Exercise 10 Timeout!
        # Exercise 11 Timeout!
        # Exercise 14 Timeout!
        # Exercise 18 Timeout!
        # Exercise 23 Timeout!
        # Exercise 24 Timeout!
        # Exercise 26 Timeout!
        # Exercise 27 Timeout!
    },

    "UCDAVIS/Byparts": {
        "Exercise 1" : "1",
        "Exercise 2" : "1",
        "Exercise 3" : "1/4 + 1/4 * exp(2)",
        "Exercise 4" : "-1/9 + -1/18 * sqrt(2) + 1/24 * sqrt(2) * pi",
        "Exercise 5" : "1/16 + -5/16 * exp(-4)",
        "Exercise 8" : "-1 + 1/2 * pi",
        "Exercise 9" : "-5/27 * exp(3) + 26/27 * exp(6)",
        "Exercise 10" : "1/16 + 3/16 * exp(4) + 1/4 * exp(4) * log(5) + -1/4 * log(5)",
        "Exercise 11" : "-2 + exp(1)",
        "Exercise 12" : "6 + -2 * exp(1)",
        "Exercise 13" : "-8/5",
        "Exercise 14" : "1/8",
        "Exercise 15" : "2 + -5 * exp(-1)",
        "Exercise 16" : "1/3",
        "Exercise 17" : "-1/2 + 1/32 * pi ^ 2 * sin(1/16 * pi ^ 2) + 1/2 * cos(1/16 * pi ^ 2)",
        "Exercise 18" : "-8/135 * sqrt(2) + 5/27 * sqrt(5)",
        "Exercise 19" : "-5/36 + -1/2 * log(1/9) + 1/2 * log(1/6)",
        "Exercise 20" : "1/3 * cos(1) + -1/3 * exp(3) * cos(exp(3)) + -1/3 * sin(1) + 1/3 * sin(exp(3))",

        # Exercise 6 Can't Solve.
        # Exercise 7 Can't Solve.
        # Exercise 21 Timeout!
        # Exercise 22 Timeout!
        # Exercise 23 Timeout!
    },

    "UCDAVIS/LogAndArctangent": {
        "Exercise 1" : "3/2 + 3 * log(2)",
        "Exercise 2" : "-7 * log(5) + 7 * log(6)",
        "Exercise 4" : "1/2 * log(1/5) + -1/2 * log(1/4)",
        "Exercise 5" : "26/3 + -8 * log(3)",
        "Exercise 7" : "-log(3) + log(4)",
        "Exercise 8" : "-1 + -10 * log(3) + 10 * log(4)",
        "Exercise 9" : "-atan(2) + atan(3)",
        "Exercise 12" : "-1/2 * log(2) + 1/2 * log(4)",
        "Exercise 14" : "-1/2 * log(4) + 1/2 * log(abs(2 + 2 * exp(2)))",
        "Exercise 16" : "-1/2 + 1/2 * exp(2) + 1/2 * log(4) + -1/2 * log(abs(2 + 2 * exp(2)))",
        "Exercise 17" : "-1/2 + log(2)",
        "Exercise 20" : "-1/2 * log(2) + 1/2 * log(8) + 1/2 * log(abs(2 * exp(2))) + -1/2 * log(abs(4 + 4 * exp(2)))",
        "Exercise 21" : "-1 + 1/4 * pi + exp(1) + -atan(exp(1))",
        
        # Exercise 3 Timeout!
        # Exercise 6 Timeout!
        # Exercise 10 Timeout!
        # Exercise 11 Timeout!
        # Exercise 13 Timeout!
        # Exercise 15 Timeout!
        # Exercise 18 Timeout!
        # Exercise 19 Timeout!
        # Exercise 22 Timeout!
    },

    "UCDAVIS/PartialFraction": {
        # "Exercise 1" : "-1/4 * log(4) + 1/4 * log(8) + 1/4 * log(20) + -1/4 * log(24)",
        # "Exercise 2" : "3/2 * log(2) + -3/2 * log(4) + -1/2 * log(8) + 1/2 * log(10)",
        # "Exercise 3" : "2/5 * log(2) + 7/5 * log(30) + -7/5 * log(35)",
        # "Exercise 4" : "1 + 15/8 * log(16) + -15/8 * log(24) + 15/8 * log(40) + -15/8 * log(48)",
        # "Exercise 5" : "46/3 + -4/3 * log(6) + 4/3 * log(9) + 13/3 * log(15) + -13/3 * log(18)",
        # "Exercise 6" : "-3/2 * log(2) + log(4) + log(6) + -1/2 * log(10)",
        # "Exercise 7" : "7/8 + 5/4 * log(2) + -5/4 * log(4) + -5/4 * log(16) + 5/4 * log(24)",
        # "Exercise 8" : "127/64 + -1/8 * log(2) + 1/8 * log(4) + -31/8 * log(32) + 31/8 * log(48)",
        # "Exercise 9" : "-3/8 + log(2)",
        # "Exercise 10" : "-1/8 + -log(12) + 4/3 * log(15) + -3/4 * log(16) + 5/12 * log(24)",
        # "Exercise 11" : "53/90 + -20/27 * log(27) + 20/27 * log(54) + -7/27 * log(108) + 7/27 * log(135)",
        # "Exercise 12" : "sqrt(3) + -(tan(1/12 * pi) ^ -1) + -log(abs(1/3 * sqrt(3))) + log(abs(tan(1/12 * pi))) + log(abs(-1 + 1/3 * sqrt(3))) + -log(abs(-1 + tan(1/12 * pi)))",
        # "Exercise 13" : "1 + -16/3 * log(3) + 9/2 * log(4) + 5/6 * log(6) + -7/6 * log(24) + 7/6 * log(30)",
        # "Exercise 14" : "-1/4 * log(abs(-4 + 4 * exp(1))) + 1/4 * log(abs(-4 + 4 * exp(2))) + 1/4 * log(abs(12 + 4 * exp(1))) + -1/4 * log(abs(12 + 4 * exp(2)))",
        # "Exercise 15" : "log(2) + log(abs(exp(1))) + -log(abs(1 + exp(1)))",
        # "Exercise 16" : "1/4 * pi + -atan(2) + 9/2 * log(2) + -3/2 * log(5)",
        # Exercise 17 Timeout!
        # Exercise 18 Timeout!
        # Exercise 19 Timeout!
        # Exercise 20 Timeout!
    }
}

file_names = [
    "tongji7",
    "MIT/2013",
    "MIT/2014",
    "MIT/2020",
    "UCDAVIS/usubstitution",
    "UCDAVIS/Exponentials",
    "UCDAVIS/Trigonometric",
    "UCDAVIS/Byparts",
    "UCDAVIS/LogAndArctangent",
    "UCDAVIS/PartialFraction",
]

class RunSlagle(unittest.TestCase):
    # def testRunSlagle(self):

    #     for filename in file_names:
    #         with open("integral/examples/slagle/%s.json" % filename, "r", encoding="utf-8") as f:
    #             f_data = json.load(f)

    #         for item in f_data['content']:
    #             if test_file is None or test_file == filename:
    #                 if (test_case is None and item['name'] in test_cases[filename]) or \
    #                    test_case == item['name']:
    #                     target = test_cases[filename][item['name']]
    #                     rules.check_item(item, target, debug=True)

    # def testRunSlagle1(self):
    #     for filename in file_names:
    #         with open("integral/examples/%s.json" % filename, "r", encoding="utf-8") as f:
    #             f_data = json.load(f)
    #         for item in f_data["content"]:
    #             test_case = item["problem"]
    #             solver = slagle.Slagle(20)
    #             time1 = time.perf_counter()
    #             try:
    #                 result = solver.eval(test_case)
    #             except:
    #                 print(item["name"], "Slagle bugs.")
    #                 continue
    #             time2 = time.perf_counter()
    #             if isinstance(result, expr.Expr) and result.is_constant():
    #                 # print(item["name"], result, "%.3fs"%(time2 - time1))
    #                 print("\"%s\" : \"%s\"," % (item["name"], result))
    #                 # solver.write_slagle_json("integral\examples\slagle\%s.json" % filename, item["name"])
    #             elif result is None:
    #                 print(item["name"], "Timeout!")
    #             else:
    #                 print(item["name"], "Can't Solve.")


    def testValidateSlagle(self):
        for filename in file_names:
            with open("integral/examples/%s.json" % filename, "r", encoding="utf-8") as f:
                f_data = json.load(f)

            for item in f_data["content"]:
                if item["name"] in test_cases[filename]:
                    steps = slagle_infos(item["name"], item["problem"])
                    target = test_cases[filename][item['name']]
                    rules.check_item(item, target, debug=True)
            


def slagle_infos(name, e):
    """Given an integral, return the steps performed in algorithms."""
    log = {}
    solver = slagle.Slagle(20)
    time1 = time.perf_counter()
    steps = slagle.perform_steps(solver.compute_node(e))
    time2 = time.perf_counter()
    print("\n%s get result in %.3fs" % (name, time2 - time1))
    return {
        "name": name,
        "problem": e,
        "calc": steps
    }

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