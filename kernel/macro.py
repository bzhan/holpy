# Author: Bohua Zhan

from typing import Dict

from kernel.type import HOLType
from kernel.term import Term

TyInst = Dict[str, HOLType]
Inst = Dict[str, Term]


"""Global store of macros. Keys are names of the macros,
values are the corresponding macro objects.

When each macro is defined, it is first put into this dictionary.
It is added to the theory only when a theory file contains an
extension adding it by name.

"""
global_macros = dict()

def has_macro(thy, name):
    if name in global_macros:
        macro = global_macros[name]
        return macro.limit is None or thy.has_theorem(macro.limit)
    else:
        return False

def get_macro(thy, name):
    assert has_macro(thy, name), "get_macro: %s is not available." % name
    return global_macros[name]


class ProofMacro():
    """A proof macro represents a derived proof method.
    
    A single macro invocation can represent multiple primitive derivation
    steps or calls to other macros (including itself). It is used to both
    simplify the proof process and reduce the amount of memory it takes
    to store a proof.
    
    A macro consists of the following data:
    
    eval -- obtain the result of applying the proof method.

    expand -- obtain the detailed proof of the derivation.

    sig -- signature of the macro.

    level -- trustworthiness level of a macro. Smaller is greater
    trustworthiness.

    """
    def __init__(self):
        self.level = None
        self.sig = None

    def eval(self, thy, args, prevs):
        """Obtain the result of applying the proof method.
        
        Input is the current theory, argument of the proof method, and
        the list of previous theorems.

        """
        raise NotImplementedError

    def expand(self, prefix, thy, args, prevs):
        """Obtain the detailed proof of the derivation.
        
        Input is the current id prefix, the current theory,
        argument of the proof method, and the list of ids and statements
        of previous theorems.

        """
        raise NotImplementedError
