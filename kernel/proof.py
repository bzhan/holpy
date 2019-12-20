# Author: Bohua Zhan

from kernel.term import Term
from kernel.thm import Thm

class ItemID():
    """Represents id of an item."""
    def __init__(self, id=None):
        """Convert id into tuple form."""
        if id is None:
            self.id = tuple()
        elif isinstance(id, tuple) and all(isinstance(i, int) for i in id):
            self.id = id
        elif isinstance(id, int):
            self.id = (id,)
        elif isinstance(id, str):
            self.id = tuple(int(s) for s in id.split("."))
        elif isinstance(id, ItemID):
            self.id = id.id
        else:
            raise TypeError

    def __str__(self):
        """Print id in n1.n2.n3 form."""
        return ".".join(str(i) for i in self.id)

    def __eq__(self, other):
        return self.id == other.id

    def incr_id_after(self, start, n):
        """Perform the id adjustment necessary for adding n lines before
        start id. The exact logic is as follows:
        
        Suppose start has length k. Find all ids with length at least k,
        where the first k-1 numbers agree with start, and the k'th number
        is greater than or equal to start. Increment the k'th number by n
        and leave the rest unchanged.

        """
        k = len(start.id)
        if len(self.id) >= k and self.id[:k-1] == start.id[:k-1] and self.id[k-1] >= start.id[k-1]:
            return ItemID(self.id[:k-1] + (self.id[k-1] + n,) + self.id[k:])
        else:
            return self

    def incr_id(self, n):
        """Increment the last number in id by n."""
        return ItemID(self.id[:-1] + (self.id[-1] + n,))

    def decr_id(self, id_remove):
        """Decrement a single id, with the aim of closing the gap at
        id_remove. The logic used is similar to that incr_id_after.
        
        """
        k = len(id_remove.id)
        if len(self.id) >= k and self.id[:k-1] == id_remove.id[:k-1] and self.id[k-1] > id_remove.id[k-1]:
            return ItemID(self.id[:k-1] + (self.id[k-1] - 1,) + self.id[k:])
        else:
            return self

    def last(self):
        """Return the last entry of the id."""
        return self.id[-1]

    def can_depend_on(self, other):
        """Return whether the current id can depend on another id."""
        l = len(other.id)
        if l > len(self.id):
            return False
        if other.id[:l-1] != self.id[:l-1]:
            return False
        return other.id[l-1] < self.id[l-1]

class ProofException(Exception):
    pass


class ProofItem():
    """An item in a proof, consisting of the following data:

    - id: an identifier for reference by later proof items.
    - rule: derivation rule used to derive the theorem.
    - args: arguments to the rule.
    - prevs: previous sequents used. Default to [].
    - th: optional theorem statement (as a sequent).
    - subproof: optional expanded proof of the statement.

    """
    def __init__(self, id, rule, *, args=None, prevs=None, th=None):
        self.id = ItemID(id)
        self.rule = rule
        self.args = args
        self.prevs = [ItemID(prev) for prev in prevs] if prevs is not None else []
        self.th = th
        self.subproof = None

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
        str_id = str(self.id)
        str_args = " " + self.print_str_args() if self.args else ""
        str_prevs = " from " + ", ".join(str(prev) for prev in self.prevs) if self.prevs else ""
        str_th = str(self.th) + " by " if self.th else ""
        cur_line = str_id + ": " + str_th + self.rule + str_args + str_prevs
        if self.subproof:
            return cur_line + "\n" + "\n".join(str(item) for item in self.subproof.items)
        else:
            return cur_line

    def __repr__(self):
        return str(self)

    def __eq__(self, other):
        return self.id == other.id and self.rule == other.rule and self.args == other.args \
            and self.prevs == other.prevs and self.th == other.th

    def get_sorrys(self):
        if self.rule == 'sorry':
            assert self.subproof is None
            return [self.th]
        
        if self.subproof:
            return sum([item.get_sorrys() for item in self.subproof.items], [])
        else:
            return []
            
    def incr_proof_item(self, start, n):
        """Increment all ids in the given proof item. Recursively increment
        ids in subproofs.
        
        """
        self.id = self.id.incr_id_after(start, n)
        self.prevs = [id.incr_id_after(start, n) for id in self.prevs]
        if self.subproof:
            for subitem in self.subproof.items:
                subitem.incr_proof_item(start, n)

    def decr_proof_item(self, id_remove):
        """Decrement all ids in the given proof item."""
        self.id = self.id.decr_id(id_remove)
        self.prevs = [id.decr_id(id_remove) for id in self.prevs]
        if self.subproof:
            for subitem in self.subproof.items:
                subitem.decr_proof_item(id_remove)


class Proof():
    """Proof objects represent proofs in the natural deduction format.

    Each proof consists of a list of items, where each item contains a
    theorem, which is derived from zero or more previous theorems using
    one of the deduction rules.

    """
    def __init__(self, *assums):
        """Initialization can take a list of n assumptions, and generates
        first n steps 0, ..., n-1 using Thm.assume on the assumptions.

        """
        self.items = [ProofItem(i, "assume", args=assum) for i, assum in enumerate(assums)]

    def add_item(self, id, rule, *, args=None, prevs=[], th=None):
        """Add the given item to the end of the proof."""
        self.items.append(ProofItem(id, rule, args=args, prevs=prevs, th=th))

    def __str__(self):
        """Print the given proof object."""
        return '\n'.join(str(item) for item in self.items)

    def __repr__(self):
        return str(self)

    def find_item(self, id):
        """Find item at the given id."""
        try:
            item = self.items[id.id[0]]
            for i in id.id[1:]:
                item = item.subproof.items[i]
            return item
        except (AttributeError, IndexError):
            raise ProofException

    def get_parent_proof(self, id):
        """Traverse the proof to the subproof containing the given id."""
        try:
            prf = self
            for i in id.id[:-1]:
                prf = prf.items[i].subproof
            if prf is None:
                raise ProofException
            return prf
        except IndexError:
            raise ProofException

    def insert_item(self, item):
        """Insert the item using the id in the item. This item should
        be placed exactly after the last position of its subproof.
        
        """
        try:
            prf = self
            for i in item.id.id[:-1]:
                if prf.items[i].subproof is None:
                    prf.items[i].subproof = Proof()
                prf = prf.items[i].subproof
            if item.id.id[-1] != len(prf.items):
                raise ProofException
            prf.items.append(item)
        except IndexError:
            raise ProofException

    def get_sorrys(self):
        return sum([item.get_sorrys() for item in self.items], [])
