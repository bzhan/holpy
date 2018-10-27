# Author: Bohua Zhan

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

    def check_proof(self, input):
        """Check the given proof in text format."""
        
        # First: read input into proof object
        prf = Proof()
        for line in input:
            prf.proof.append(parser.parse_proof_rule(self.thy, self.ctxt, line))

        # Next: check the proof
        self.thy.check_proof(prf)

        # Return the checked proof
        return prf.str_with_printer(term_printer = lambda t: printer.print_term(self.thy, t))
