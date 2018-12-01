# Author: Bohua Zhan

class MacroSig():
    """Signature for the arguments of proof macro."""
    NONE, TERM, TYINST, INST, STRING, STRING_TERM = range(6)


class ProofMacro():
    """
    To define the macro to simplify the proof.
    A proof macro represents a derived proof method. It consists
    of the following data:
    
    __call__ -- obtain the result of applying the proof method. Input
    is the argument of the proof method, followed by the list of previous
    theorems.

    expand -- obtain the detail proof of the derivation. Input is the
    current depth (used to avoid name conflict), optionally the current
    theory, argument of the proof method, and the list of ids and statements
    of previous theorems.

    sig -- signature of the macro, of type MacroSig.

    level -- trustworthiness level of a macro. Smaller is greater
    trustworthiness.

    """
    def __init__(self):
        self.level = None
        self.sig = None
        self.has_theory = None

    def __str__(self):
        if hasattr(self, "__call__"):
            str_no_eval = ""
        else:
            str_no_eval = ", no eval"

        if hasattr(self, "expand"):
            str_no_expand = ""
        else:
            str_no_expand = ", no expand"

        return "level " + str(self.level) + str_no_eval + str_no_expand
