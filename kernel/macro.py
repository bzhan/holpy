# Author: Bohua Zhan

import abc

class ProofMacro(abc.ABC):
    """A proof macro represents a derived proof method. It consists
    of the following data:
    
    desc -- description of the macro.

    eval -- function to obtain the final result. Input is list of
    previous theorems, followed by arguments of the proof method.

    expand -- function to obtain the detail proof of the derivation.
    Input is current id (used to avoid name conflict), list of ids
    of previous theorems, list of previous theorems, and arguments
    of the proof method.

    level -- trustworthiness level of a macro. Smaller is greater
    trustworthiness.

    """
    def __init__(self, desc, eval, expand = None, level = 10):
        self.desc = desc
        self.eval = eval
        self.expand = expand
        self.level = level

    def __str__(self):
        if self.eval:
            str_no_eval = ""
        else:
            str_no_eval = ", no eval"

        if self.expand:
            str_no_expand = ""
        else:
            str_no_expand = ", no expand"

        return self.desc + " (level " + str(self.level) + str_no_eval + str_no_expand + ")"
