# Author: Chaozhu Xiang, Bohua Zhan

import io

from kernel.report import ProofReport
from logic.basic import BasicTheory
from syntax import printer
from server import server, tactic


class Cell(object):
    def __init__(self, vars, assums, concl, ctxt=None):
        self.proof = tactic.init_proof(vars, assums, concl)
        self.thy = BasicTheory()
        self.thy.check_proof(self.proof)

        self.ctxt = ctxt if ctxt is not None else dict()
        self.vars = vars
        self.assums = assums
        self.concl = concl
        self.rpt = None

    def parse_proof(self, proof_text):
        self.proof = server.Server(self.thy).parse_proof(io.StringIO(proof_text))

    def print_proof(self):
        def term_printer(t):
            return printer.print_term(self.thy, t, unicode=True, print_abs_type=True)
        return self.proof.print(term_printer=term_printer, print_vars=True, unicode=True)

    def check_proof(self):
        self.rpt = ProofReport()
        self.thy.check_proof(self.proof, rpt=self.rpt)

    def obtain_init_data(self):
        """Returns the initial string values for variables, assumptions,
        and conclusion.

        """
        def print_variable(v):
            return "var " + v.name + " :: " + str(v.T)

        def print_term(t):
            return printer.print_term(self.thy, t, unicode=True, print_abs_type=True)

        return {
            "variables": [print_variable(v) for v in self.vars],
            "assumes": [print_term(t) for t in self.assums],
            "conclusion": print_term(self.concl)
        }
