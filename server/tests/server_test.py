# Author: Bohua Zhan

import unittest
import io

from kernel.type import hol_bool
from logic.basic import BasicTheory
from server.server import Server

class ServerTest(unittest.TestCase):
    def testCheckProof(self):
        """Proof of A & B --> B & A."""
        input = "\n".join([
            "var A :: bool",
            "var B :: bool",
            "A1: assume A & B",
            "S1: theorem conjD1",
            "S2: implies_elim from S1, A1",
            "S3: theorem conjD2",
            "S4: implies_elim from S3, A1",
            "S5: theorem conjI",
            "S6: substitution {A: B, B: A} from S5",
            "S7: implies_elim from S6, S4",
            "S8: implies_elim from S7, S2",
            "S9: implies_intr A & B from S8"])

        output = "\n".join([
            "A1: A & B |- A & B by assume A & B",
            "S1: |- A & B --> A by theorem conjD1",
            "S2: A & B |- A by implies_elim from S1, A1",
            "S3: |- A & B --> B by theorem conjD2",
            "S4: A & B |- B by implies_elim from S3, A1",
            "S5: |- A --> B --> A & B by theorem conjI",
            "S6: |- B --> A --> B & A by substitution {A: B, B: A} from S5",
            "S7: A & B |- A --> B & A by implies_elim from S6, S4",
            "S8: A & B |- B & A by implies_elim from S7, S2",
            "S9: |- A & B --> B & A by implies_intr A & B from S8"])
        
        server = Server(BasicTheory())
        res = server.check_proof(io.StringIO(input))
        self.assertEqual(res, output)

    def testCheckProofMacro(self):
        """Proof of f = g --> x = y --> f x = g y."""
        input = "\n".join([
            "var x :: 'a",
            "var y :: 'a",
            "var f :: 'a => 'a",
            "var g :: 'a => 'a",
            "A1: assume f = g",
            "A2: assume x = y",
            "S1: arg_combination f from A2",
            "S2: fun_combination y from A1",
            "S3: transitive from S1, S2",
            "S4: implies_intr x = y from S3",
            "S5: implies_intr f = g from S4"])

        output = "\n".join([
            "A1: f = g |- f = g by assume f = g",
            "A2: x = y |- x = y by assume x = y",
            "S1: x = y |- f x = f y by arg_combination f from A2",
            "S2: f = g |- f y = g y by fun_combination y from A1",
            "S3: f = g, x = y |- f x = g y by transitive from S1, S2",
            "S4: f = g |- x = y --> f x = g y by implies_intr x = y from S3",
            "S5: |- f = g --> x = y --> f x = g y by implies_intr f = g from S4"])

        server = Server(BasicTheory())
        res = server.check_proof(io.StringIO(input))
        self.assertEqual(res, output)

    def testCheckProofDoubleNegInv(self):
        """Proof of ~~A --> A."""
        input = "\n".join([
            "var A :: bool",
            "A1: assume ~~A",
            "S1: theorem classical",
            "S2: assume A",
            "S3: assume ~A",
            "S4: apply_theorem negE from A1, S3",
            "S5: apply_theorem falseE from S4",
            "S6: implies_intr A from S2",
            "S7: implies_intr ~A from S5",
            "S8: apply_theorem disjE from S1, S6, S7",
            "S9: implies_intr ~~A from S8"])

        output = "\n".join([
            "A1: ~~A |- ~~A by assume ~~A",
            "S1: |- A | ~A by theorem classical",
            "S2: A |- A by assume A",
            "S3: ~A |- ~A by assume ~A",
            "S4: ~A, ~~A |- false by apply_theorem negE from A1, S3",
            "S5: ~A, ~~A |- A by apply_theorem falseE from S4",
            "S6: |- A --> A by implies_intr A from S2",
            "S7: ~~A |- ~A --> A by implies_intr ~A from S5",
            "S8: ~~A |- A by apply_theorem disjE from S1, S6, S7",
            "S9: |- ~~A --> A by implies_intr ~~A from S8"])

        server = Server(BasicTheory())
        res = server.check_proof(io.StringIO(input))
        self.assertEqual(res, output)

if __name__ == "__main__":
    unittest.main()
