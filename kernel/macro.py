# Author: Bohua Zhan

"""Global store of macros. Keys are names of the macros,
values are the corresponding macro objects.

When each macro is defined, it is first put into this dictionary.
It is added to the theory only when a theory file contains an
extension adding it by name.

"""
global_macros = dict()

class MacroSig():
    """Signature for the arguments of proof macro."""
    NONE, TERM, TYINST, INST, STRING, STRING_TERM, STRING_INST = range(7)


class ProofMacro():
    """A proof macro represents a derived proof method.
    
    A single macro invocation can represent multiple primitive derivation
    steps or calls to other macros (including itself). It is used to both
    simplify the proof process and reduce the amount of memory it takes
    to store a proof.
    
    A macro consists of the following data:
    
    __call__ -- obtain the result of applying the proof method.

    expand -- obtain the detailed proof of the derivation.

    sig -- signature of the macro, of type MacroSig.

    level -- trustworthiness level of a macro. Smaller is greater
    trustworthiness.

    """
    def __init__(self):
        self.level = None
        self.sig = None
        self.has_theory = None

    def __call__(self):
        """Obtain the result of applying the proof method.
        
        Input is the argument of the proof method, followed by the list
        of previous theorems.

        """
        raise NotImplementedError()

    def expand(self):
        """Obtain the detailed proof of the derivation.
        
        Input is the current depth (used to avoid name conflict),
        optionally the current theory, argument of the proof method,
        and the list of ids and statements of previous theorems.

        """
        raise NotImplementedError()
