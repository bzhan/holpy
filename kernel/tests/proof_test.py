# Author: Bohua Zhan

import unittest

from kernel.type import boolT
from kernel.term import Term, Var
from kernel.thm import Thm
from kernel.proof import ProofItem, Proof, ItemID

A = Var("A", boolT)
B = Var("B", boolT)
A_to_B = Term.mk_implies(A,B)

class ProofTest(unittest.TestCase):
    def testIncrIdAfter(self):
        test_data = [
            (("0", "0", 1), "1"),
            (("0.1", "0", 1), "1.1"),
            (("1", "2.2", 1), "1"),
            (("2.1", "2.2", 1), "2.1"),
            (("2.2", "2.2", 1), "2.3"),
            (("2.3.2", "2.2", 1), "2.4.2"),
            (("3", "2.2", 1), "3"),
        ]

        for (id, start, n), res in test_data:
            id = ItemID(id)
            start = ItemID(start)
            self.assertEqual(str(id.incr_id_after(start, n)), res)

    def testCanDependOn(self):
        test_data = [
            ("0", "0", False),
            ("0", "1", False),
            ("1", "0", True),
            ("1.1", "1.0", True),
            ("1.1", "1", False),
            ("2", "1.1", False)
        ]

        for id1, id2, res in test_data:
            self.assertEqual(ItemID(id1).can_depend_on(ItemID(id2)), res)

    def testProofItem(self):
        test_data = [
            (ProofItem(0, "theorem", args="conjD1"),
             "0: theorem conjD1",
             {'id': 0, 'th': '', 'rule': 'theorem', 'args': 'conjD1', 'prevs': []}),
            (ProofItem(1, "assume", args=A_to_B),
             "1: assume implies A B",
             {'id': 1, 'th': '', 'rule': 'assume', 'args': 'implies A B', 'prevs': []}),
            (ProofItem(5, "substitution", args={"A": B, "B": A}, prevs=[4]),
             "5: substitution {A: B, B: A} from 4",
             {'id': 5, 'th': '', 'rule': 'substitution', 'args': '{A: B, B: A}', 'prevs': [4]}),
            (ProofItem(6, "implies_elim", prevs=[5, 3]),
             "6: implies_elim from 5, 3",
             {'id': 6, 'th': '', 'rule': 'implies_elim', 'args': '', 'prevs': [5, 3]}),
            (ProofItem(1, "apply_theorem_for", args=("conjD2", {}, {"A": B, "B": A}), prevs=[0]),
             "1: apply_theorem_for conjD2, {}, {A: B, B: A} from 0",
             {'id': 1, 'th': '', 'rule': 'apply_theorem_for', 'args': 'conjD2, {A: B, B: A}', 'prevs': [0]})
        ]

        for item, s, d in test_data:
            self.assertEqual(str(item), s)

    def testProof(self):
        prf = Proof(A_to_B, A)
        prf.vars = [A, B]
        th = Thm([A, A_to_B], B)
        prf.add_item(2, "implies_elim", prevs=[0, 1], th=th)

        self.assertEqual(len(prf.items), 3)
        self.assertEqual(prf.items[-1].th, th)

        str_prf = "\n".join([
            "0: assume implies A B",
            "1: assume A",
            "2: A, implies A B |- B by implies_elim from 0, 1"])
        
        self.assertEqual(str(prf), str_prf)


if __name__ == "__main__":
    unittest.main()
