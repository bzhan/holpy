# Author: Bohua Zhan

class MacroSig():
    """Signature for the arguments of proof macro."""
    NONE, TERM, TYINST, INST, STRING = range(5)


class ProofMacro():
    """A proof macro represents a derived proof method. It consists
    of the following data:
    
    __call__ -- obtain the result of applying the proof method. Input
    is list of previous theorems, followed by arguments of the proof
    method.

    expand -- obtain the detail proof of the derivation. Input is
    current depth (used to avoid name conflict), list of ids
    of previous theorems, list of previous theorems, and arguments
    of the proof method.

    level -- trustworthiness level of a macro. Smaller is greater
    trustworthiness.

    """
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
