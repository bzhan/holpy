"""Unit test for congruence closure."""

import unittest

from prover import congc


MERGE, CHECK = range(2)

class CongClosureTest(unittest.TestCase):
    def run_test(self, data, verbose=False):
        closure = congc.CongClosure()
        for item in data:
            if item[0] == MERGE:
                _, s, t = item
                closure.merge(s, t)
                if verbose:
                    print("Merge %s, %s" % (s, t))
                    print("After:")
                    print(closure)
            else:
                _, s, t, b = item
                self.assertEqual(closure.test(s, t), b)

    def test1(self):
        self.run_test([
            (MERGE, "t1", "t2"),
            (MERGE, "t3", "t4"),
            (CHECK, "t2", "t4", False),
            (MERGE, "t1", "t3"),
            (CHECK, "t2", "t4", True),
        ])

    def test2(self):
        self.run_test([
            (MERGE, ("t1", "t2"), "t3"),
            (MERGE, ("t4", "t5"), "t6"),
            (MERGE, "t1", "t4"),
            (CHECK, "t3", "t6", False),
            (MERGE, "t2", "t5"),
            (CHECK, "t3", "t6", True),
        ])

    def test3(self):
        self.run_test([
            (MERGE, ("t1", "t2"), "t3"),
            (MERGE, ("t1", "t4"), "t5"),
            (MERGE, "t2", "t4"),
            (CHECK, "t3", "t5", True),
        ])


if __name__ == "__main__":
    unittest.main()
