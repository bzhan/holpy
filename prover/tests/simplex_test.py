import unittest
from logic import context
from syntax import parser
from prover import simplex

context.set_context('real', vars={
    "x9_plus": "real", "x9_minus": "real", "x6_plus": "real", "x6_minus": "real", "x5_plus": "real", "x5_minus": "real", "x4_plus": "real", "x4_minus": "real",
    "x3_plus": "real", "x3_minus": "real", "x2_plus": "real", "x2_minus": "real", "x0_plus": "real", "x0_minus": "real", "x7_plus": "real", "x7_minus": "real",
    "x1_plus": "real", "x1_minus": "real", "x8_plus": "real", "x8_minus": "real",
    "x14_plus": "real", "x14_minus": "real", "x12_plus": "real", "x12_minus": "real", "x10_plus": "real", "x10_minus": "real",
    "x13_plus": "real", "x13_minus": "real", "x19_plus": "real", "x19_minus": "real", "x18_plus": "real", "x18_minus": "real",
    "x17_plus": "real", "x17_minus": "real", "x16_plus": "real", "x16_minus": "real", "x15_plus": "real", "x15_minus": "real",
    'x': 'real', 'y': 'real', 'z': 'real'
})

class SimplexTest(unittest.TestCase):

    # def test10Vars(self):
    #     test_data = [
    #                     "7 * x6_plus + -7 * x6_minus + x5_plus + -1 * x5_minus + 4 * x3_plus + -4 * x3_minus + x7_plus + -1 * x7_minus + -5 * x1_plus + 5 * x1_minus + -7 * x8_plus + 7 * x8_minus ≥ 1", 
    #                     "2 * x9_plus + -2 * x9_minus + 14 * x6_plus + -14 * x6_minus + 6 * x4_plus + -6 * x4_minus + -5 * x3_plus + 5 * x3_minus + -1 * x2_plus + x2_minus + 4 * x7_plus + -4 * x7_minus ≤ 0", 
    #                     "4 * x9_plus + -4 * x9_minus + x6_plus + -1 * x6_minus + -8 * x4_plus + 8 * x4_minus + 15 * x2_plus + -15 * x2_minus + 4 * x0_plus + -4 * x0_minus + 4 * x1_plus + -4 * x1_minus ≥ 0", 
    #                     "3 * x9_plus + -3 * x9_minus + 9 * x6_plus + -9 * x6_minus + 2 * x5_plus + -2 * x5_minus + -1 * x4_plus + x4_minus + 16 * x2_plus + -16 * x2_minus + -6 * x0_plus + 6 * x0_minus ≤ -9", 
    #                     "2 * x5_plus + -2 * x5_minus + 2 * x4_plus + -2 * x4_minus + 4 * x3_plus + -4 * x3_minus + 9 * x7_plus + -9 * x7_minus + 11 * x1_plus + -11 * x1_minus + -2 * x8_plus + 2 * x8_minus ≤ 5",
    #                     "3 * x9_plus + -3 * x9_minus + 9 * x5_plus + -9 * x5_minus + -9 * x4_plus + 9 * x4_minus + 5 * x2_plus + -5 * x2_minus + 2 * x0_plus + -2 * x0_minus + -1 * x7_plus + x7_minus + x1_plus + -1 * x1_minus ≤ -5", 
    #                     "9 * x9_plus + -9 * x9_minus + 4 * x4_plus + -4 * x4_minus + -12 * x2_plus + 12 * x2_minus + 6 * x0_plus + -6 * x0_minus + 5 * x7_plus + -5 * x7_minus + 8 * x8_plus + -8 * x8_minus ≤ 4", 
    #                     "5 * x9_plus + -5 * x9_minus + -3 * x6_plus + 3 * x6_minus + -7 * x5_plus + 7 * x5_minus + x4_plus + -1 * x4_minus + 7 * x3_plus + -7 * x3_minus + 4 * x2_plus + -4 * x2_minus + 13 * x0_plus + -13 * x0_minus ≤ 6", 
    #                     "8 * x9_plus + -8 * x9_minus + -7 * x6_plus + 7 * x6_minus + 17 * x5_plus + -17 * x5_minus + -3 * x4_plus + 3 * x4_minus + -3 * x0_plus + 3 * x0_minus + 5 * x1_plus + -5 * x1_minus + 3 * x8_plus + -3 * x8_minus ≥ -1", 
    #                     "3 * x9_plus + -3 * x9_minus + -7 * x6_plus + 7 * x6_minus + -7 * x5_plus + 7 * x5_minus + 4 * x4_plus + -4 * x4_minus + 4 * x2_plus + -4 * x2_minus + -8 * x0_plus + 8 * x0_minus + -6 * x1_plus + 6 * x1_minus ≤ -9", 
    #                     "7 * x6_plus + -7 * x6_minus + -7 * x5_plus + 7 * x5_minus + 6 * x4_plus + -6 * x4_minus + -4 * x3_plus + 4 * x3_minus + -14 * x0_plus + 14 * x0_minus + -19 * x1_plus + 19 * x1_minus + 9 * x8_plus + -9 * x8_minus ≥ 7"
    #     ]
    #     comparsions = [parser.parse_term(c) for c in test_data]
    #     unsat_pt = simplex.solve_hol_ineqs(comparsions)
    #     self.assertNotEqual(unsat_pt.rule, "sorry")

    # def test15Vars1(self):
    #     test_data = [
    #         "2 * x10_plus + -2 * x10_minus + -1 * x2_plus + x2_minus + -1 * x4_plus + x4_minus + x6_plus + -1 * x6_minus ≤ 0",
    #         "2 * x14_plus + -2 * x14_minus + -1 * x10_plus + x10_minus + -1 * x8_plus + x8_minus + x0_plus + -1 * x0_minus ≤ 0",
    #         "x9_plus + -1 * x9_minus + -1 * x7_plus + x7_minus + x1_plus + -1 * x1_minus + -1 * x4_plus + x4_minus + x6_plus + -1 * x6_minus ≥ 0",
    #         "x13_plus + -1 * x13_minus + x11_plus + -1 * x11_minus + x3_plus + -1 * x3_minus + -1 * x2_plus + x2_minus + x6_plus + -1 * x6_minus ≤ 0",
    #         "x9_plus + -1 * x9_minus + x8_plus + -1 * x8_minus + -1 * x5_plus + x5_minus + -2 * x4_plus + 2 * x4_minus + -1 * x6_plus + x6_minus ≤ -1",
    #         "x12_plus + -1 * x12_minus + -1 * x8_plus + x8_minus + -1 * x0_plus + x0_minus + 2 * x11_plus + -2 * x11_minus + -1 * x3_plus + x3_minus + x2_plus + -1 * x2_minus ≤ 1", 
    #         "x14_plus + -1 * x14_minus + x10_plus + -1 * x10_minus + x1_plus + -1 * x1_minus + x3_plus + -1 * x3_minus + -1 * x2_plus + x2_minus + x4_plus + -1 * x4_minus + x6_plus + -1 * x6_minus ≥ 0", 
    #         "x14_plus + -1 * x14_minus + -1 * x12_plus + x12_minus + -1 * x5_plus + x5_minus + -1 * x1_plus + x1_minus + x13_plus + -1 * x13_minus + -1 * x4_plus + x4_minus + x6_plus + -1 * x6_minus ≥ 0",
    #         "x12_plus + -1 * x12_minus + x10_plus + -1 * x10_minus + x7_plus + -1 * x7_minus + x5_plus + -1 * x5_minus + x11_plus + -1 * x11_minus + -1 * x2_plus + x2_minus + -1 * x6_plus + x6_minus ≥ 0",
    #         "2 * x10_plus + -2 * x10_minus + x8_plus + -1 * x8_minus + x7_plus + -1 * x7_minus + x5_plus + -1 * x5_minus + x3_plus + -1 * x3_minus + x4_plus + -1 * x4_minus + -1 * x6_plus + x6_minus ≥ 1", 
    #         "x14_plus + -1 * x14_minus + x12_plus + -1 * x12_minus + -1 * x9_plus + x9_minus + -1 * x8_plus + x8_minus + -1 * x5_plus + x5_minus + x11_plus + -1 * x11_minus + -1 * x3_plus + x3_minus + x6_plus + -1 * x6_minus ≥ 1", 
    #         "x12_plus + -1 * x12_minus + -1 * x7_plus + x7_minus + -1 * x5_plus + x5_minus + -1 * x1_plus + x1_minus + x0_plus + -1 * x0_minus + -1 * x13_plus + x13_minus + x3_plus + -1 * x3_minus + -1 * x6_plus + x6_minus ≥ 1", 
    #         "2 * x10_plus + -2 * x10_minus + -1 * x8_plus + x8_minus + -1 * x5_plus + x5_minus + x1_plus + -1 * x1_minus + 2 * x2_plus + -2 * x2_minus + x4_plus + -1 * x4_minus + -1 * x6_plus + x6_minus ≥ -1", 
    #         "x14_plus + -1 * x14_minus + x12_plus + -1 * x12_minus + x10_plus + -1 * x10_minus + x9_plus + -1 * x9_minus + x8_plus + -1 * x8_minus + x7_plus + -1 * x7_minus + -1 * x5_plus + x5_minus + -1 * x1_plus + x1_minus + x0_plus + -1 * x0_minus ≤ 1",
    #         "x12_plus + -1 * x12_minus + -1 * x9_plus + x9_minus + x8_plus + -1 * x8_minus + -1 * x7_plus + x7_minus + x13_plus + -1 * x13_minus + -1 * x11_plus + x11_minus + -1 * x3_plus + x3_minus + -1 * x2_plus + x2_minus + x4_plus + -1 * x4_minus ≤ 0", 
    #         "x14_plus + -1 * x14_minus + -1 * x12_plus + x12_minus + x5_plus + -1 * x5_minus + 2 * x1_plus + -2 * x1_minus + -1 * x0_plus + x0_minus + x13_plus + -1 * x13_minus + -1 * x11_plus + x11_minus + x3_plus + -1 * x3_minus + -2 * x2_plus + 2 * x2_minus ≤ 0"]

    #     comparsions = [parser.parse_term(c) for c in test_data]
    #     unsat_pt = simplex.solve_hol_ineqs(comparsions)
    #     self.assertNotEqual(unsat_pt.rule, "sorry")

    # def test15Vars2(self):
    #     test_data = [
    #         "2 * x14_plus + -2 * x14_minus + x2_plus + -1 * x2_minus + -1 * x1_plus + x1_minus + -1 * x0_plus + x0_minus ≤ 0",
    #         "x13_plus + -1 * x13_minus + -1 * x6_plus + x6_minus + -1 * x2_plus + x2_minus + x0_plus + -1 * x0_minus + -1 * x9_plus + x9_minus ≤ 0",
    #         "x11_plus + -1 * x11_minus + -1 * x8_plus + x8_minus + x4_plus + -1 * x4_minus + x3_plus + -1 * x3_minus + -2 * x1_plus + 2 * x1_minus ≥ 0", 
    #         "x11_plus + -1 * x11_minus + -1 * x8_plus + x8_minus + -1 * x3_plus + x3_minus + -2 * x5_plus + 2 * x5_minus + x9_plus + -1 * x9_minus ≤ 1", 
    #         "x14_plus + -1 * x14_minus + x10_plus + -1 * x10_minus + -1 * x7_plus + x7_minus + 2 * x2_plus + -2 * x2_minus + x0_plus + -1 * x0_minus ≤ -1", 
    #         "3 * x13_plus + -3 * x13_minus + x4_plus + -1 * x4_minus + x2_plus + -1 * x2_minus + -1 * x1_plus + x1_minus + -1 * x5_plus + x5_minus ≤ -1", 
    #         "x13_plus + -1 * x13_minus + -2 * x10_plus + 2 * x10_minus + x6_plus + -1 * x6_minus + x4_plus + -1 * x4_minus + -1 * x2_plus + x2_minus + -1 * x0_plus + x0_minus ≤ -1",
    #         "x14_plus + -1 * x14_minus + x13_plus + -1 * x13_minus + -1 * x12_plus + x12_minus + x11_plus + -1 * x11_minus + x8_plus + -1 * x8_minus + -1 * x4_plus + x4_minus + -1 * x1_plus + x1_minus ≥ 0", 
    #         "x14_plus + -1 * x14_minus + -1 * x13_plus + x13_minus + -1 * x11_plus + x11_minus + x10_plus + -1 * x10_minus + -1 * x4_plus + x4_minus + x3_plus + -1 * x3_minus + -1 * x2_plus + x2_minus ≤ -1",
    #         "x14_plus + -1 * x14_minus + -1 * x11_plus + x11_minus + x10_plus + -1 * x10_minus + x8_plus + -1 * x8_minus + -1 * x7_plus + x7_minus + -1 * x4_plus + x4_minus + -1 * x3_plus + x3_minus ≤ -1", 
    #         "2 * x8_plus + -2 * x8_minus + x7_plus + -1 * x7_minus + -1 * x2_plus + x2_minus + 2 * x0_plus + -2 * x0_minus + -1 * x5_plus + x5_minus + x9_plus + -1 * x9_minus ≤ 0", 
    #         "x12_plus + -1 * x12_minus + -1 * x11_plus + x11_minus + 3 * x7_plus + -3 * x7_minus + x6_plus + -1 * x6_minus + -1 * x3_plus + x3_minus + x2_plus + -1 * x2_minus + -1 * x0_plus + x0_minus ≤ 0", 
    #         "2 * x13_plus + -2 * x13_minus + -1 * x12_plus + x12_minus + x11_plus + -1 * x11_minus + -1 * x8_plus + x8_minus + -1 * x7_plus + x7_minus + x1_plus + -1 * x1_minus + 2 * x5_plus + -2 * x5_minus ≤ 1", 
    #         "x14_plus + -1 * x14_minus + x10_plus + -1 * x10_minus + -1 * x6_plus + x6_minus + -1 * x3_plus + x3_minus + x1_plus + -1 * x1_minus + -1 * x0_plus + x0_minus + -1 * x5_plus + x5_minus + -2 * x9_plus + 2 * x9_minus ≥ -1", 
    #         "x14_plus + -1 * x14_minus + 4 * x13_plus + -4 * x13_minus + x12_plus + -1 * x12_minus + -2 * x11_plus + 2 * x11_minus + -1 * x10_plus + x10_minus + -1 * x8_plus + x8_minus + 2 * x7_plus + -2 * x7_minus + x6_plus + -1 * x6_minus + x4_plus + -1 * x4_minus + -1 * x3_plus + x3_minus + x1_plus + -1 * x1_minus + -1 * x0_plus + x0_minus ≥ -1", 
    #         "308 * x14_plus + -308 * x14_minus + 1391 * x13_plus + -1391 * x13_minus + 308 * x12_plus + -308 * x12_minus + -669 * x11_plus + 669 * x11_minus + -308 * x10_plus + 308 * x10_minus + -361 * x8_plus + 361 * x8_minus + 616 * x7_plus + -616 * x7_minus + 308 * x6_plus + -308 * x6_minus + 308 * x4_plus + -308 * x4_minus + -308 * x3_plus + 308 * x3_minus + -53 * x2_plus + 53 * x2_minus + 308 * x1_plus + -308 * x1_minus + -308 * x0_plus + 308 * x0_minus ≥ -615"]
            
    #         # 20-vars very slow
    #         # ("x18_plus + -1 * x18_minus + x12_plus + -1 * x12_minus + -1 * x4_plus + x4_minus + -1 * x8_plus + x8_minus + -1 * x5_plus + x5_minus ≥ 0",
    #         # "x14_plus + -1 * x14_minus + -1 * x13_plus + x13_minus + x12_plus + -1 * x12_minus + 2 * x4_plus + -2 * x4_minus + x2_plus + -1 * x2_minus ≤ 1",
    #         # "x16_plus + -1 * x16_minus + -1 * x14_plus + x14_minus + x13_plus + -1 * x13_minus + -1 * x6_plus + x6_minus + x0_plus + -1 * x0_minus + x1_plus + -1 * x1_minus ≥ 1",
    #         # "x19_plus + -1 * x19_minus + -1 * x11_plus + x11_minus + -1 * x15_plus + x15_minus + x10_plus + -1 * x10_minus + -1 * x8_plus + x8_minus + x3_plus + -1 * x3_minus ≤ 0",
    #         # "x14_plus + -1 * x14_minus + -1 * x13_plus + x13_minus + x12_plus + -1 * x12_minus + -1 * x11_plus + x11_minus + -1 * x4_plus + x4_minus + -1 * x5_plus + x5_minus ≤ 0",
    #         # "x16_plus + -1 * x16_minus + x14_plus + -1 * x14_minus + -2 * x13_plus + 2 * x13_minus + -1 * x9_plus + x9_minus + -1 * x6_plus + x6_minus + x17_plus + -1 * x17_minus ≥ 1",
    #         # "x18_plus + -1 * x18_minus + x13_plus + -1 * x13_minus + x9_plus + -1 * x9_minus + -1 * x17_plus + x17_minus + x15_plus + -1 * x15_minus + x5_plus + -1 * x5_minus + -1 * x7_plus + x7_minus ≤ 0",
    #         # "x18_plus + -1 * x18_minus + x4_plus + -1 * x4_minus + -1 * x2_plus + x2_minus + x0_plus + -1 * x0_minus + x10_plus + -1 * x10_minus + x7_plus + -1 * x7_minus + -1 * x1_plus + x1_minus ≤ -1", 
    #         # "2 * x19_plus + -2 * x19_minus + x18_plus + -1 * x18_minus + 2 * x16_plus + -2 * x16_minus + -1 * x0_plus + x0_minus + -1 * x3_plus + x3_minus + x1_plus + -1 * x1_minus ≤ 0",
    #         # "x18_plus + -1 * x18_minus + -1 * x12_plus + x12_minus + -1 * x11_plus + x11_minus + 2 * x4_plus + -2 * x4_minus + -1 * x17_plus + x17_minus + -1 * x15_plus + x15_minus + -1 * x5_plus + x5_minus ≥ 0",
    #         # "x19_plus + -1 * x19_minus + -1 * x18_plus + x18_minus + x11_plus + -1 * x11_minus + x0_plus + -1 * x0_minus + -1 * x10_plus + x10_minus + -1 * x7_plus + x7_minus + x3_plus + -1 * x3_minus + x1_plus + -1 * x1_minus ≤ 0",
    #         # "x19_plus + -1 * x19_minus + -1 * x14_plus + x14_minus + x13_plus + -1 * x13_minus + x12_plus + -1 * x12_minus + -1 * x11_plus + x11_minus + -1 * x9_plus + x9_minus + -1 * x3_plus + x3_minus + -1 * x1_plus + x1_minus ≤ 0",
    #         # "2 * x12_plus + -2 * x12_minus + 2 * x11_plus + -2 * x11_minus + x4_plus + -1 * x4_minus + x2_plus + -1 * x2_minus + -2 * x5_plus + 2 * x5_minus + x3_plus + -1 * x3_minus ≥ 0", 
    #         # "x19_plus + -1 * x19_minus + x14_plus + -1 * x14_minus + x13_plus + -1 * x13_minus + -1 * x6_plus + x6_minus + -1 * x4_plus + x4_minus + x2_plus + -1 * x2_minus + -1 * x17_plus + x17_minus + -1 * x15_plus + x15_minus + x3_plus + -1 * x3_minus ≥ 0",
    #         # "2 * x19_plus + -2 * x19_minus + -2 * x18_plus + 2 * x18_minus + x16_plus + -1 * x16_minus + -1 * x13_plus + x13_minus + x0_plus + -1 * x0_minus + 2 * x15_plus + -2 * x15_minus + -1 * x7_plus + x7_minus ≥ 1", 
    #         # "2 * x16_plus + -2 * x16_minus + -1 * x14_plus + x14_minus + -2 * x9_plus + 2 * x9_minus + -2 * x0_plus + 2 * x0_minus + -1 * x17_plus + x17_minus + -1 * x15_plus + x15_minus + x8_plus + -1 * x8_minus ≤ 0",
    #         # "x14_plus + -1 * x14_minus + -1 * x13_plus + x13_minus + 3 * x9_plus + -3 * x9_minus + 2 * x6_plus + -2 * x6_minus + x2_plus + -1 * x2_minus + -1 * x0_plus + x0_minus + -2 * x1_plus + 2 * x1_minus ≥ -1", 
    #         # "x16_plus + -1 * x16_minus + -1 * x14_plus + x14_minus + -1 * x13_plus + x13_minus + x11_plus + -1 * x11_minus + -2 * x6_plus + 2 * x6_minus + x0_plus + -1 * x0_minus + x15_plus + -1 * x15_minus + x10_plus + -1 * x10_minus + -1 * x5_plus + x5_minus ≤ 0", 
    #         # "x18_plus + -1 * x18_minus + 3 * x16_plus + -3 * x16_minus + x14_plus + -1 * x14_minus + -1 * x11_plus + x11_minus + x9_plus + -1 * x9_minus + x4_plus + -1 * x4_minus + -1 * x15_plus + x15_minus + x10_plus + -1 * x10_minus + x5_plus + -1 * x5_minus ≤ -1", 
    #         # "x19_plus + -1 * x19_minus + x14_plus + -1 * x14_minus + x13_plus + -1 * x13_minus + -1 * x4_plus + x4_minus + x2_plus + -1 * x2_minus + -1 * x17_plus + x17_minus + x15_plus + -1 * x15_minus + -1 * x10_plus + x10_minus + -1 * x8_plus + x8_minus + -3 * x5_plus + 3 * x5_minus ≤ 0",
    #         # "x19_plus + -1 * x19_minus + -1 * x18_plus + x18_minus + x16_plus + -1 * x16_minus + x14_plus + -1 * x14_minus + -1 * x13_plus + x13_minus + x12_plus + -1 * x12_minus + -1 * x11_plus + x11_minus + x9_plus + -1 * x9_minus + x6_plus + -1 * x6_minus + x4_plus + -1 * x4_minus + x2_plus + -1 * x2_minus + x0_plus + -1 * x0_minus ≤ 0")

    #     comparsions = [parser.parse_term(c) for c in test_data]
    #     unsat_pt = simplex.solve_hol_ineqs(comparsions)
    #     self.assertNotEqual(unsat_pt.rule, "sorry")
    pass