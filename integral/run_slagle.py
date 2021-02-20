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
        "Exercise 12" : "1/4",
        "Exercise 14" : "-1/8 * sqrt(3) + 1/6 * pi",
        "Exercise 15" : "1/4 * pi",
        "Exercise 16" : "1/2 * pi",
        "Exercise 17" : "2 * sqrt(2) + sqrt(2) * pi",
        "Exercise 20" : "2 + 2 * log(2) + -2 * log(3)",
        "Exercise 21" : "1 + 2 * log(1/2)",
        "Exercise 22" : "1 + -exp(-1/2)",
        "Exercise 23" : "-2 + 2 * sqrt(3)",
        "Exercise 28" : "1 + -2 * exp(-1)",
        "Exercise 29" : "1/4 + 1/4 * exp(2)",
        "Exercise 31" : "-4 + 4 * log(4)",
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

    "MIT/2019": {
        "Exercise 2": "log(abs(exp(1) + sin(1)))",
    },

    "UCDAVIS/usubstitution": {
        # "Exercise 1" : "209952 + -78125 * 0 ^ (9/2) + -21875 * 0 ^ (11/2) + -875 * 0 ^ (13/2) + -5 * 0 ^ (15/2)",
        "Exercise 2" : "175099/11",
        "Exercise 3" : "74/21",
        "Exercise 4" : "-1/3 + 1/3 * 2 ^ (3/4)",
        "Exercise 5" : "-1/5 * exp(2) + 1/5 * exp(7)",
        "Exercise 6" : "4/3",
        "Exercise 7" : "0",
        "Exercise 12" : "1",
        "Exercise 13" : "-11/21",
        "Exercise 14" : "128/15 + -8/3 * 0 ^ (3/2) + 2/5 * 0 ^ (5/2)",
        "Exercise 15" : "1/2 + -7/4 * log(3) + 7/4 * log(5)",
        "Exercise 16" : "-3/2 + -8 * log(2) + 8 * log(3)",
        "Exercise 17" : "41/6",
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
    },

    "UCDAVIS/LogAndArctangent": {
        "Exercise 1" : "3/2 + 3/2 * log(4)",
        "Exercise 2" : "-7 * log(5) + 7 * log(6)",
        "Exercise 4" : "1/2 * log(4) + -1/2 * log(5)",
        "Exercise 7" : "-log(3) + log(4)",
        "Exercise 8" : "-1 + -10 * log(3) + 10 * log(4)",
        "Exercise 9" : "-atan(2) + atan(3)",
        "Exercise 12" : "-1/2 * log(2) + 1/2 * log(4)",
        "Exercise 14" : "-1/2 * log(4) + 1/2 * log(abs(2 + 2 * exp(2)))",
        "Exercise 16" : "-1/2 + 1/2 * exp(2) + 1/2 * log(4) + -1/2 * log(abs(2 + 2 * exp(2)))",
        "Exercise 17" : "-1/2 + log(2)",
    },

    "UCDAVIS/PartialFraction": {
        "Exercise 9" : "-3/8 + log(2)",
        "Exercise 15" : "log(2) + -log(abs(1 + exp(-1)))",
    }
}


tongji_not_solved = [
    10, 11, 18, 24
]

class RunSlagle(unittest.TestCase):
    def testRunSlagle(self):
        file_names = [
            "tongji7",
            # "MIT/2013",
            # "MIT/2014",
            # "MIT/2019",
            # "UCDAVIS/usubstitution",
            # "UCDAVIS/Exponentials",
            # "UCDAVIS/Trigonometric",
            # "UCDAVIS/Byparts",
            # "UCDAVIS/LogAndArctangent",
            # "UCDAVIS/PartialFraction",
        ]

        for filename in file_names:
            with open("integral/examples/slagle/tongji7.json", "r", encoding="utf-8") as f:
                f_data = json.load(f)

            for item in f_data['content']:
                if test_file is None or test_file == "tongji7":
                    if (test_case is None and item['name'] in test_cases["tongji7"]) or \
                       test_case == item['name']:
                        target = test_cases["tongji7"][item['name']]
                        rules.check_item(item, target, debug=True)
            # for item in f_data["content"]:
            #     test_case = item["problem"]
            #     item_num = int(item["name"].split(" ")[1])
            #     if item_num in tongji_not_solved:
            #         continue
            #     solver = slagle.Slagle(20)
            #     time1 = time.perf_counter()
            #     try:
            #         result = solver.eval(test_case)
            #     except:
            #         print(item["name"], "Error")
            #         continue
            #     time2 = time.perf_counter()
            #     if result is None:
            #         continue
            #     if result.is_constant():
            #         # print(item["name"], result, "%.3fs"%(time2 - time1))
            #         print("\"%s\" : \"%s\"," % (item["name"], result))
            #         solver.write_slagle_json("integral\examples\slagle\%s.json" % filename, item["name"])
            #     elif result is None:
            #         print(item["name"], "Timeout!")
            #     else:
            #         print(item["name"], "Errors!")

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