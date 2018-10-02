# Author: Bohua Zhan

import unittest
from kernel.term import *
from kernel.type import *
from kernel.theory import *
from logic.proofterm import *

thy = Theory.EmptyTheory()

Ta = TVar("a")
x = Var("x", Ta)
y = Var("y", Ta)
z = Var("z", Ta)

class ProofTermTest(unittest.TestCase):
    def testExport(self):
        """Basic case."""
        pt1 = ProofTerm.assume(Term.mk_equals(x,y))
        pt2 = ProofTerm.assume(Term.mk_equals(y,z))
        pt3 = ProofTerm.transitive(pt1, pt2)

        prf = pt3.export()
        self.assertEqual(prf.get_num_item(), 3)
        self.assertEqual(thy.check_proof(prf), pt3.th)

    def testExport2(self):
        """Repeated theorems."""
        pt1 = ProofTerm.assume(Term.mk_equals(x,x))
        pt2 = ProofTerm.transitive(pt1, pt1)

        prf = pt2.export()
        self.assertEqual(prf.get_num_item(), 2)
        self.assertEqual(thy.check_proof(prf), pt2.th)

if __name__ == "__main__":
    unittest.main()
