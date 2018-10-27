# Author: Bohua Zhan

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
    def __init__(self, id, rule, *, args = None, prevs = None, th = None):
        self.id = id
        self.rule = rule
        self.args = args
        self.prevs = prevs if prevs is not None else []
        self.th = th

    def str_with_printer(self, *, term_printer):
        """Output function with custom printer for terms."""

        def repr_val(val):
            if isinstance(val, Term):
                return term_printer(val)
            else:
                return repr(val)

        if isinstance(self.args, str):
            str_args = " " + self.args
        elif isinstance(self.args, dict):
            str_args = " {" + ", ".join(key + ": " + repr_val(val) for key, val in self.args.items()) + "}"
        else:
            str_args = " " + repr_val(self.args) if self.args else ""

        str_prevs = " from " + ", ".join(str(prev) for prev in self.prevs) if self.prevs else ""
        str_th = self.th.str_with_printer(term_printer = term_printer) + " by " if self.th else ""

        return self.id + ": " + str_th + self.rule + str_args + str_prevs

    def __str__(self):
        return self.str_with_printer(term_printer = repr)

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
        self.proof = []
        for (id, assum) in zip(range(len(assums)), assums):
            item = ProofItem("A" + str(id+1), "assume", args = assum)
            self.proof.append(item)

    def add_item(self, id, rule, *, args = None, prevs = [], th = None):
        """Add the given item to the end of the proof."""
        self.proof.append(ProofItem(id, rule, args = args, prevs = prevs, th = th))

    def get_items(self):
        """Returns the list of items."""
        return self.proof

    def get_last_item(self):
        """Returns the last item."""
        return self.proof[-1]

    def get_num_item(self):
        """Returns the number of items."""
        return len(self.proof)

    def get_thm(self):
        """Returns the theorem obtained by the proof."""
        if self.proof and self.proof[-1].th is not None:
            return self.proof[-1].th
        else:
            raise ProofException()

    def str_with_printer(self, *, term_printer = repr):
        return "\n".join(item.str_with_printer(term_printer = term_printer) for item in self.proof)

    def __str__(self):
        return self.str_with_printer()

    def __repr__(self):
        return str(self)
