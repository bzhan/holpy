from kernel.report import ProofReport
from logic.basic import BasicTheory
from syntax import printer
from server import tactic


class Cell(object):
    def __init__(self, vars, assums, concl, origin, ctxt=None):
        self.proof = tactic.init_proof(vars, assums, concl)
        self.ctxt = ctxt if ctxt is not None else dict()
        self.assums = assums
        self.concl = concl
        self.origin = origin
        self.rpt = ProofReport()

    def update(self, origin):
        self.origin = origin

    def print_proof(self):
        thy = BasicTheory()
        def term_printer(t):
            return printer.print_term(thy, t, unicode=True)
        return self.proof.print(print_vars=True, term_printer=term_printer)
