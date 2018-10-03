# Author: Bohua Zhan

import abc
from kernel.thm import *

class ExtensionReport(abc.ABC):
    """A report of a theory extension. This contains:

    axioms -- list of axioms added. Each axiom is given by a pair,
    the first entry is the name of the constant or theorem. The second
    entry is type of the term or statement of the theorem.

    """
    def __init__(self):
        self.axioms = []

    def add_axiom(self, name, info):
        self.axioms.append((name, info))

    def get_axioms(self):
        return self.axioms

    @staticmethod
    def _str_axiom(axiom):
        (name, info) = axiom
        if isinstance(info, HOLType):
            return name + " :: " + str(info)
        elif isinstance(info, Thm):
            return name + ": " + str(info)
        else:
            raise AssertionError("_str_axiom")

    def __str__(self):
        return "Axiom added: " + str(len(self.axioms)) + "\n" + \
            "\n".join(ExtensionReport._str_axiom(axiom) for axiom in self.axioms)
