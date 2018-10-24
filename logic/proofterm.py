# Author: Bohua Zhan

from kernel.thm import Thm
from kernel.proof import Proof

class ProofTerm():
    """A proof term contains the derivation tree of a theorem.

    th -- statement of the theorem.
    rule -- proof method used to derive the theorem.
    args -- arguments to the proof method.
    prevs -- proof terms that the current one depends on.
    
    """
    def __init__(self, th, rule, args, prevs):
        self.th = th
        self.rule = rule
        self.args = args
        self.prevs = prevs

    @staticmethod
    def assume(A):
        return ProofTerm(Thm.assume(A), "assume", A, [])

    @staticmethod
    def reflexive(x):
        return ProofTerm(Thm.reflexive(x), "reflexive", x, [])

    @staticmethod
    def symmetric(pt):
        return ProofTerm(Thm.symmetric(pt.th), "symmetric", None, [pt])

    @staticmethod
    def transitive(pt1, pt2):
        return ProofTerm(Thm.transitive(pt1.th, pt2.th), "transitive", None, [pt1, pt2])

    @staticmethod
    def combination(pt1, pt2):
        return ProofTerm(Thm.combination(pt1.th, pt2.th), "combination", None, [pt1, pt2])

    @staticmethod
    def arg_combination(pt, f):
        """Given x = y and term f, return f x = f y."""
        return ProofTerm(Thm.combination(Thm.reflexive(f), pt.th), "arg_combination", f, [pt])

    @staticmethod
    def fun_combination(pt, f):
        """Given f = g and term x, return f x = g x."""
        return ProofTerm(Thm.combination(pt.th, Thm.reflexive(f)), "fun_combination", f, [pt])

    @staticmethod
    def substitution(pt, inst):
        return ProofTerm(Thm.substitution(pt.th, inst), "substitution", inst, [pt])

    @staticmethod
    def beta_conv(x):
        return ProofTerm(Thm.beta_conv(x), "beta_conv", x, [])

    @staticmethod
    def theorem(th_name, th):
        return ProofTerm(th, "theorem", th_name, [])

    def _export(self, seq_to_id, prf):
        """Helper function for _export.
        
        seq_to_id -- the dictionary from existing sequents to ids. This
        is updated by the function.

        prf -- the currently built proof. Updated by the function.

        """
        # Should not call _export when self is already in seq_to_id
        assert self.th not in seq_to_id, "_export: th already found."

        ids = []
        for prev in self.prevs:
            if prev.th in seq_to_id:
                ids.append(seq_to_id[prev.th])
            else:
                prev._export(seq_to_id, prf)
                ids.append(prf.get_last_item().id)
        
        id = "S" + str(prf.get_num_item()+1)
        seq_to_id[self.th] = id
        prf.add_item(id, self.th, self.rule, self.args, ids)
        return prf

    def export(self):
        """Convert to proof object."""
        return self._export(dict(), Proof())
