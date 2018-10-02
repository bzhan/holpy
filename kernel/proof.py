# Author: Bohua Zhan

import abc
from kernel.thm import *

class ProofException(Exception):
    pass

class ProofItem(abc.ABC):
    """An item in a proof, consisting of the following data:

    - id: a string identifier, for reference from later sequents.
    - th: the sequent statement.
    - rule: the derivation rule used to derive the sequent.
    - args: the arguments to the rule.
    - prevs: the previous sequents used.
    """
    def __init__(self, id, th, rule, args, prevs):
        self.id = id
        self.th = th
        self.rule = rule
        self.args = args
        self.prevs = prevs

    def __str__(self):
        if self.args:
            str_args = " " + repr(self.args)
        else:
            str_args = ""

        if self.prevs:
            str_prevs = " from " + ", ".join(str(prev) for prev in self.prevs)
        else:
            str_prevs = ""

        return self.id + ": " + str(self.th) + " by " + self.rule + str_args + str_prevs

    def __repr__(self):
        return str(self)

class Proof(abc.ABC):
    """Proof objects represent proofs in the natural deduction format.

    Each proof consists of a list of items, where each item contains a
    sequent following from zero or more previous sequents by one of the
    deduction rules.

    """
    def __init__(self, *assums):
        """Initialization can take a list of n assumptions, and generates
        first n steps A1, ..., An using Thm.assume on the assumptions.

        """
        self.proof = []
        for (id, assum) in zip(range(len(assums)), assums):
            item = ProofItem("A" + str(id+1), Thm.assume(assum), "assume", assum, None)
            self.proof.append(item)

    def add_item(self, id, th, rule, args, prevs):
        """Add the given item to the end of the proof."""
        self.proof.append(ProofItem(id, th, rule, args, prevs))

    def get_items(self):
        """Returns the list of items."""
        return self.proof

    def get_thm(self):
        """Returns the theorem obtained by the proof."""
        if self.proof:
            return self.proof[-1].th
        else:
            raise ProofException()

    def __str__(self):
        return "\n".join(str(item) for item in self.proof)

    def __repr__(self):
        return str(self)
