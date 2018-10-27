# Author: Bohua Zhan

import unittest

from kernel.type import hol_bool
from kernel.term import Term, Var
from kernel.thm import Thm
from kernel.proof import Proof

A = Var("A", hol_bool)
B = Var("B", hol_bool)
A_to_B = Term.mk_implies(A,B)

class ProofTest(unittest.TestCase):
    def testProof(self):
        prf = Proof(A_to_B, A)
        th = Thm([A, A_to_B], B)
        prf.add_item("C", "implies_elim", prevs = ["A1", "A2"], th = th)

        self.assertEqual(prf.get_num_item(), 3)
        self.assertEqual(prf.get_thm(), th)

        str_prf = "\n".join([
            "A1: by assume implies A B",
            "A2: by assume A",
            "C: A, implies A B |- B by implies_elim from A1, A2"])
        
        self.assertEqual(str(prf), str_prf)

if __name__ == "__main__":
    unittest.main()
