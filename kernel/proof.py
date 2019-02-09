# Author: Bohua Zhan

from kernel.term import Term
from kernel.thm import Thm

class ProofItem():
    """An item in a proof, consisting of the following data:

    - id: an identifier for reference by later proof items.
    - rule: derivation rule used to derive the theorem.
    - args: arguments to the rule.
    - prevs: previous sequents used. Default to [].
    - th: optional theorem statement (as a sequent).

    """
    def __init__(self, id, rule, *, args=None, prevs=None, th=None):
        self.id = id
        self.rule = rule
        self.args = args
        self.prevs = prevs if prevs is not None else []
        self.th = th

    def print_str_args(self):
        def str_val(val):
            if isinstance(val, dict):
                items = sorted(val.items(), key = lambda pair: pair[0])
                return "{" + ", ".join(key + ": " + str_val(val) for key, val in items) + "}"
            else:
                return str(val)

        if isinstance(self.args, tuple):
            return ", ".join(str_val(val) for val in self.args)
        elif self.args:
            return str_val(self.args)
        else:
            return ""

    def __str__(self):
        """Print the given proof item."""
        str_args = " " + self.print_str_args() if self.args else ""
        str_prevs = " from " + ", ".join(str(prev) for prev in self.prevs) if self.prevs else ""
        str_th = str(self.th) + " by " if self.th else ""
        return str(self.id) + ": " + str_th + self.rule + str_args + str_prevs

    def __repr__(self):
        return str(self)

    def __eq__(self, other):
        return self.id == other.id and self.rule == other.rule and self.args == other.args \
            and self.prevs == other.prevs and self.th == other.th

class Proof():
    """Proof objects represent proofs in the natural deduction format.

    Each proof consists of a list of items, where each item contains a
    theorem, which is derived from zero or more previous theorems using
    one of the deduction rules.

    """
    def __init__(self, *assums):
        """Initialization can take a list of n assumptions, and generates
        first n steps A1, ..., An using Thm.assume on the assumptions.

        """
        self.items = []
        for id, assum in enumerate(assums):
            item = ProofItem("A" + str(id+1), "assume", args=assum)
            self.items.append(item)

    def add_item(self, id, rule, *, args=None, prevs=[], th=None):
        """Add the given item to the end of the proof."""
        self.items.append(ProofItem(id, rule, args=args, prevs=prevs, th=th))

    def __str__(self):
        """Print the given proof object."""
        return '\n'.join(str(item) for item in self.items)

    def __repr__(self):
        return str(self)
