# Author: Bohua Zhan

"""Statistics of common theorems."""

import unittest
from pstats import Stats
import cProfile

from server.tests.server_test import testSteps

test_theorems = [
    # Logic
    ('logic', 'double_neg'),
    ('logic', 'disj_conv_imp'),
    ('logic', 'ex_conj_distrib'),
    ('logic', 'all_conj_distrib'),
    ('logic', 'conj_disj_distribL1'),
    ('logic', 'pierce'),
    ('logic', 'drinker'),
    # Sets
    ('set', 'subset_antisym'),
    ('set', 'subset_trans'),
    ('set', 'cantor'),
    ('set', 'Inter_subset'),
    ('set', 'subset_Inter'),
    ('set', 'Union_union'),
    ('set', 'lfp_lowerbound'),
    ('set', 'lfp_greatest'),
    ('set', 'lfp_unfold'),
    # Functions
    ('function', 'fun_upd_triv'),
    ('function', 'fun_upd_upd'),
    ('function', 'fun_upd_twist'),
    ('function', 'comp_fun_assoc'),
    ('function', 'injective_comp_fun'),
    ('function', 'surjective_comp_fun'),
    # Peano arithmetic
    ('nat', 'add_comm'),
    ('nat', 'add_assoc'),
    ('nat', 'distrib_l'),
    ('nat', 'mult_assoc'),
    ('nat', 'mult_comm'),
    ('nat', 'less_eq_trans'),
    # Lists
    ('list', 'append_right_neutral'),
    ('list', 'append_assoc'),
    ('list', 'length_append'),
    ('list', 'rev_append'),
    ('list', 'rev_rev'),
    ('list', 'rev_length'),
]

profile = True

class CollectStat(unittest.TestCase):
    def testCollectStat(self):
        if profile:
            pr = cProfile.Profile()
            pr.enable()

        for thy_name, thm_name in test_theorems:
            try:
                testSteps(self, thy_name, thm_name, no_gaps=True, print_stat=True)
            except Exception as e:
                print(thy_name, thm_name, "failed:", e.__class__)
                # raise e

        if profile:
            p = Stats(pr)
            p.strip_dirs()
            p.sort_stats('cumtime')
            p.print_stats(100)

if __name__ == "__main__":
    unittest.main()
