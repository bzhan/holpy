# Author: Bohua Zhan

from kernel import settings
from kernel.term import Term
from kernel.thm import Thm

class ProofException(Exception):
    pass

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

    def _print_str_args(self):
        def str_val(val):
            if isinstance(val, dict):
                items = sorted(val.items(), key = lambda pair: pair[0])
                return "{" + ", ".join(key + ": " + str_val(val) for key, val in items) + "}"
            else:
                return str(val)

        if isinstance(self.args, str):
            return self.args
        elif isinstance(self.args, dict):
            return str_val(self.args)
        elif isinstance(self.args, tuple):
            return ", ".join(str_val(val) for val in self.args)
        else:
            return str_val(self.args) if self.args else ""

    def print(self, **kargs):
        """Print the given proof item."""
        try:
            settings.update_settings(**kargs)
            str_args = " " + self._print_str_args() if self.args else ""
            str_prevs = " from " + ", ".join(str(prev) for prev in self.prevs) if self.prevs else ""
            str_th = str(self.th) + " by " if self.th else ""
            return self.id + ": " + str_th + self.rule + str_args + str_prevs
        finally:
            settings.recover_settings()

    def export(self, **kargs):
        """Export the given proof item as a dictionary."""
        try:
            settings.update_settings(**kargs)
            str_args = self._print_str_args()
            str_th = str(self.th) if self.th else ""
            return {'id': self.id, 'th': str_th, 'rule': self.rule, 'args': str_args, 'prevs': self.prevs}
        finally:
            settings.recover_settings()

    def __str__(self):
        return self.print()

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
        self.vars = []
        self.items = []
        for id, assum in enumerate(assums):
            item = ProofItem("A" + str(id+1), "assume", args=assum)
            self.items.append(item)

    def add_item(self, id, rule, *, args=None, prevs=[], th=None):
        """Add the given item to the end of the proof."""
        self.items.append(ProofItem(id, rule, args=args, prevs=prevs, th=th))

    def get_num_item(self):
        """Returns the number of items."""
        return len(self.items)

    def get_thm(self):
        """Returns the theorem obtained by the proof."""
        if self.items and self.items[-1].th is not None:
            return self.items[-1].th
        else:
            raise ProofException()

    def print(self, **kargs):
        """Print the given proof object."""
        def print_var(t):
            return "var " + t.name + " :: " + str(t.T)

        try:
            settings.update_settings(**kargs)
            str_vars = "\n".join(print_var(t) for t in self.vars) + "\n"
            lines = [str(item) for item in self.items]
            return str_vars + "\n".join(lines)
        finally:
            settings.recover_settings()

    def export(self, **kargs):
        """Export the given proof object."""
        def export_var(t):
            return {'id': 'var', 'rule': t.name + ' :: ' + str(t.T)}

        try:
            settings.update_settings(**kargs)
            vars = [export_var(t) for t in self.vars]
            lines = [item.export() for item in self.items]
            return vars + lines
        finally:
            settings.recover_settings()

    def __str__(self):
        return self.print(print_vars=False)

    def __repr__(self):
        return str(self)

    def __eq__(self, other):
        return self.items == other.items
