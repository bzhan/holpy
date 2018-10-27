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
