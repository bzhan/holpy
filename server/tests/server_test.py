# Author: Bohua Zhan

import unittest
import io

from kernel.type import hol_bool
from logic.basic import BasicTheory
from server.server import Server

thy = BasicTheory()

ctxt = {
    "A": hol_bool,
    "B": hol_bool,
    "C": hol_bool,
}

server = Server(thy, ctxt)

class ServerTest(unittest.TestCase):
    def testCheckProof(self):
        input = "\n".join([
            "A1: assume conj A B",
            "S1: theorem conjD1",
            "S2: implies_elim from S1, A1",
            "S3: theorem conjD2",
            "S4: implies_elim from S3, A1",
            "S5: theorem conjI",
            "S6: substitution {A: B, B: A} from S5",
            "S7: implies_elim from S6, S4",
            "S8: implies_elim from S7, S2",
            "S9: implies_intr conj A B from S8"])

        input_stream = io.StringIO(input)
        prf = server.check_proof(input_stream)
        
        output = "\n".join([
            "A1: conj A B |- conj A B by assume conj A B",
            "S1: |- implies (conj A B) A by theorem conjD1",
            "S2: conj A B |- A by implies_elim from S1, A1",
            "S3: |- implies (conj A B) B by theorem conjD2",
            "S4: conj A B |- B by implies_elim from S3, A1",
            "S5: |- implies A (implies B (conj A B)) by theorem conjI",
            "S6: |- implies B (implies A (conj B A)) by substitution {A: B, B: A} from S5",
            "S7: conj A B |- implies A (conj B A) by implies_elim from S6, S4",
            "S8: conj A B |- conj B A by implies_elim from S7, S2",
            "S9: |- implies (conj A B) (conj B A) by implies_intr conj A B from S8"])
        
        self.assertEqual(str(prf), output)
