# Author: Bohua Zhan

import abc

from kernel.type import HOLType
from kernel.thm import Thm

class ProofReport(abc.ABC):
    """A report of proof checking. This contains:

    steps -- number of primitive steps taken to check the proof.
    Each base derivation and each unexpanded macro counts as one step.

    thm_steps -- number of invocation of existing theorems (counting
    multiplicity).

    base_steps -- number of invocations of base derivation.

    macro_steps -- number of invocations of macros.

    th_names -- name of set of theorems used.

    macros_eval -- name of set of macros evaluated.

    macros_expand -- name of set of macros expanded.

    """
    def __init__(self):
        self.steps = 0
        self.thm_steps = 0
        self.base_steps = 0
        self.macro_steps = 0
        self.th_names = set()
        self.macros_eval = set()
        self.macros_expand = set()

    def __str__(self):
        return "\n".join([
            "Steps: " + str(self.steps),
            "  Theorems: " + str(self.thm_steps),
            "  Base: " + str(self.base_steps),
            "  Macro: " + str(self.macro_steps),
            "Theorems applied: " + ",".join(self.th_names),
            "Macros evaluated: " + ",".join(self.macros_eval),
            "Macros expanded: " + ",".join(self.macros_expand)])

    def __repr__(self):
        return str(self)

    def apply_theorem(self, th_name):
        self.steps += 1
        self.thm_steps += 1
        self.th_names.add(th_name)

    def apply_base_deriv(self):
        self.steps += 1
        self.base_steps += 1

    def eval_macro(self, macro_name):
        self.steps += 1
        self.macro_steps += 1
        self.macros_eval.add(macro_name)

    def expand_macro(self, macro_name):
        self.macros_expand.add(macro_name)

    def steps_stat(self):
        """Return the triple of thm_steps, base_steps, macro_steps."""
        return (self.thm_steps, self.base_steps, self.macro_steps)

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
