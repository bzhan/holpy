# Author: Bohua Zhan

from kernel.term import Var
from kernel.proof import Proof
import syntax.printer as printer
import syntax.parser as parser

class Server():
    """The outer interface of holpy."""

    def __init__(self, thy, ctxt = None):
        """Initialize the server with starting theory and context.

        ctxt - default value is {}.
        
        """
        self.thy = thy
        self.ctxt = ctxt if ctxt is not None else dict()

    def parse_proof(self, input):
        """Parse the given proof in text format."""
        
        # First: read input into proof object
        prf = Proof()
        for line in input:
            if line.startswith("var "):
                name, T = parser.var_decl_parser(self.thy).parse(line)
                assert name not in self.ctxt, "variable already declared"
                self.ctxt[name] = T
                prf.vars.append(Var(name, T))
            else:
                try:
                    prf.proof.append(parser.parse_proof_rule(self.thy, self.ctxt, line))
                except ValueError as e:
                    print(line)
                    raise e

        return prf

    def check_proof(self, input):
        prf = self.parse_proof(input)
        self.thy.check_proof(prf)
        return prf.print(term_printer = lambda t: printer.print_term(self.thy, t), print_vars=True)
