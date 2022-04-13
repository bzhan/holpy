import unittest
from smt.veriT.proof_parser import parse_decl, proof_parser
from smt.veriT import interface, proof_rec
import os

def test_parse_step(verit_proof, ctx):
    print("start parse proof......")
    parser = proof_parser(ctx)
    for s in verit_proof.replace("\r", "").split("\n"):
        if s == "unsat" or s == "":
            continue
        k = parser.parse(s)
    print("Finish")

class ParserTest(unittest.TestCase): 
    def testParseQF_UF(self):
        test_dirs = [
            "D:\\smt-lib\\QF_UF\\20170829-Rodin\\",
            "D:\\smt-lib\\QF_UF\\eq_diamond\\",
            # "D:\\smt-lib\\QF_UF\\NEQ\\"
        ]

        for test_dir in test_dirs:
            for file_name in os.listdir(test_dir):
                file_name = test_dir + file_name
                if interface.is_sat(file_name):
                    continue
                print(file_name)
                verit_proof = interface.solve(file_name)
                c = proof_rec.bind_var(file_name)
                test_parse_step(verit_proof, c)