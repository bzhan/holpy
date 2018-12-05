# Author: Bohua Zhan

import unittest

from kernel.type import hol_bool
from kernel.term import Term, Var
from kernel.thm import Thm
from kernel.proof import ProofItem, Proof

A = Var("A", hol_bool)
B = Var("B", hol_bool)
A_to_B = Term.mk_implies(A,B)

class ProofTest(unittest.TestCase):
    def testProofItem(self):
        test_data = [
            (ProofItem("S1", "theorem", args="conjD1"), "S1: theorem conjD1"),
            (ProofItem("S2", "assume", args=A_to_B), "S2: assume implies A B"),
            (ProofItem("S6", "substitution", args={"A": B, "B": A}, prevs=["S5"]),
                "S6: substitution {A: B, B: A} from S5"),
            (ProofItem("S7", "implies_elim", prevs=["S6", "S4"]),
                "S7: implies_elim from S6, S4"),
            (ProofItem("S1", "apply_theorem_for", args=("conjD2", {"A": B, "B": A}), prevs=["A1"]),
                "S1: apply_theorem_for conjD2, {A: B, B: A} from A1")
        ]

        for item, s in test_data:
            self.assertEqual(str(item), s)

    def testProof(self):
        prf = Proof(A_to_B, A)
        th = Thm([A, A_to_B], B)
        prf.add_item("C", "implies_elim", prevs=["A1", "A2"], th=th)

        self.assertEqual(prf.get_num_item(), 3)
        self.assertEqual(prf.get_thm(), th)

        str_prf = "\n".join([
            "A1: assume implies A B",
            "A2: assume A",
            "C: A, implies A B |- B by implies_elim from A1, A2"])
        
        self.assertEqual(str(prf), str_prf)

if __name__ == "__main__":
    unittest.main()
