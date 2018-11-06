# Author: Bohua Zhan

import unittest
import io

from kernel.type import hol_bool
from logic.basic import BasicTheory
from server.server import Server

server = Server(BasicTheory())

class ServerTest(unittest.TestCase):
    def testCheckProof(self):
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
        
        res = server.check_proof(io.StringIO(input))
        self.assertEqual(res, output)

    def testCheckProofMacro(self):
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

        res = server.check_proof(io.StringIO(input))
        self.assertEqual(res, output)
