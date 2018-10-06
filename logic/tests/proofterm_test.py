# Author: Bohua Zhan

import unittest
from kernel.term import *
from kernel.type import *
from kernel.theory import *
from logic.basic import *
from logic.proofterm import *

thy = BasicTheory()

Ta = TVar("a")
x = Var("x", Ta)
y = Var("y", Ta)
z = Var("z", Ta)
f = Var("f", TFun(Ta,Ta,Ta))

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
        pt1 = ProofTerm.assume(Term.mk_equals(x,y))
        pt2 = ProofTerm.reflexive(f)
        pt3 = ProofTerm.combination(pt2, pt1)  # f x = f y
        pt4 = ProofTerm.combination(pt3, pt1)  # f x x = f y y

        prf = pt4.export()
        self.assertEqual(prf.get_num_item(), 4)
        self.assertEqual(thy.check_proof(prf), pt4.th)

if __name__ == "__main__":
    unittest.main()
