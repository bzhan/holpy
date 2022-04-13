"""Proof reconstruction."""
from smt.veriT.proof_parser import decl_parser, proof_parser
from logic import context

def bind_var(file_name):
    """Convert the declaration in context to higher-order types and terms."""
    ctx = dict()
    with open(file_name, "r") as f:
        for s in f.readlines():
            if s.strip().startswith("(declare-fun"):
                tm = decl_parser.parse(s.strip())
                ctx.update(tm)
    return ctx

class ProofReconstruction:
    """Proof construction for a .smt2 file."""
    def __init__(self, file_name) -> None:
        self.file_name = file_name
        ctx = bind_var(self.file_name)
        cm_parser = proof_parser(ctx)
        
        