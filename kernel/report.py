# Author: Bohua Zhan

import abc
from kernel.thm import *

class ProofReport(abc.ABC):
    """A report of proof checking. This contains:

    steps -- number of primitive steps taken to check the proof.
    Each base derivation and each unexpanded macro counts as one step.

    """
    def __init__(self):
        self.count_steps = True
        self.step_count = 0

    def __str__(self):
        return "Steps: " + str(self.step_count)

    def __repr__(self):
        return str(self)

    def incr_step_count(self):
        if self.count_steps:
            self.step_count += 1

    def get_step_count(self):
        return self.step_count

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
