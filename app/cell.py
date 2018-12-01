# Author: Chaozhu Xiang, Bohua Zhan

import io

from kernel.report import ProofReport
from logic.basic import BasicTheory
from syntax import printer
from server import server, tactic


class Cell(object):
    def __init__(self, vars, assums, concl, origin, ctxt=None):
        self.proof = tactic.init_proof(vars, assums, concl)
        self.thy = BasicTheory()
        self.thy.check_proof(self.proof)

        self.ctxt = ctxt if ctxt is not None else dict()
        self.assums = assums
        self.concl = concl
        self.origin = origin
        self.rpt = ProofReport()

    def update(self, origin):
        self.origin = origin

    def parse_proof(self, proof_text):
        self.proof = server.Server(self.thy).parse_proof(io.StringIO(proof_text))

    def print_proof(self):
        def term_printer(t):
            return printer.print_term(self.thy, t, unicode=True)
        return self.proof.print(term_printer=term_printer, print_vars=True, unicode=True)

    def check_proof(self):
        self.thy.check_proof(self.proof)
