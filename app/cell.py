from kernel.report import ProofReport
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
