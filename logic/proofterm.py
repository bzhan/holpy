# Author: Bohua Zhan

from kernel.thm import Thm
from kernel.proof import Proof

class ProofTerm():
    """A proof term contains the derivation tree of a theorem.

    There are two kinds of proof terms: atoms and derivations.

    ProofTermAtom(id, th): existing theorem with the given id and statement.

    ProofTermDeriv(th, rule, args, prevs): one derivation step.
    
    """
    ATOM, DERIV = range(2)

    @staticmethod
    def atom(id, th):
        return ProofTermAtom(id, th)

    @staticmethod
    def assume(A):
        return ProofTermDeriv(Thm.assume(A), "assume", A, [])

    @staticmethod
    def reflexive(x):
        return ProofTermDeriv(Thm.reflexive(x), "reflexive", x, [])

    @staticmethod
    def symmetric(pt):
        return ProofTermDeriv(Thm.symmetric(pt.th), "symmetric", None, [pt])

    @staticmethod
    def transitive(pt1, pt2):
        return ProofTermDeriv(Thm.transitive(pt1.th, pt2.th), "transitive", None, [pt1, pt2])

    @staticmethod
    def combination(pt1, pt2):
        return ProofTermDeriv(Thm.combination(pt1.th, pt2.th), "combination", None, [pt1, pt2])

    @staticmethod
    def equal_elim(pt1, pt2):
        return ProofTermDeriv(Thm.equal_elim(pt1.th, pt2.th), "equal_elim", None, [pt1, pt2])

    @staticmethod
    def arg_combination(pt, f):
        """Given x = y and term f, return f x = f y."""
        return ProofTermDeriv(Thm.combination(Thm.reflexive(f), pt.th), "arg_combination", f, [pt])

    @staticmethod
    def fun_combination(pt, f):
        """Given f = g and term x, return f x = g x."""
        return ProofTermDeriv(Thm.combination(pt.th, Thm.reflexive(f)), "fun_combination", f, [pt])

    @staticmethod
    def substitution(pt, inst):
        return ProofTermDeriv(Thm.substitution(pt.th, inst), "substitution", inst, [pt])

    @staticmethod
    def beta_conv(x):
        return ProofTermDeriv(Thm.beta_conv(x), "beta_conv", x, [])

    @staticmethod
    def abstraction(pt, x):
        return ProofTermDeriv(Thm.abstraction(pt.th, x), "abstraction", x, [pt])

    @staticmethod
    def theorem(thy, th_name):
        return ProofTermDeriv(thy.get_theorem(th_name), "theorem", th_name, [])

    def _export(self, depth, seq_to_id, prf):
        """Helper function for _export.
        
        depth -- current depth of the proof. Used in generating ids.

        seq_to_id -- the dictionary from existing sequents to ids. This
        is updated by the function.

        prf -- the currently built proof. Updated by the function.

        """
        # Should not call _export when self is already in seq_to_id
        assert self.th not in seq_to_id, "_export: th already found."

        # Should be called only on derivations
        assert self.ty == ProofTerm.DERIV, "_export: DERIV"

        ids = []
        for prev in self.prevs:
            if prev.ty == ProofTerm.ATOM:
                ids.append(prev.id)
            elif prev.ty == ProofTerm.DERIV:
                if prev.th in seq_to_id:
                    ids.append(seq_to_id[prev.th])
                else:
                    prev._export(depth, seq_to_id, prf)
                    ids.append(prf.get_last_item().id)
            else:
                raise TypeError()
        
        id = (depth, "S" + str(prf.get_num_item()+1))
        seq_to_id[self.th] = id
        prf.add_item(id, self.rule, args = self.args, prevs = ids)
        return prf

    def export(self, depth = 0):
        """Convert to proof object."""
        return self._export(depth, dict(), Proof())

class ProofTermAtom(ProofTerm):
    """Atom proof terms."""
    def __init__(self, id, th):
        self.ty = ProofTerm.ATOM
        self.id = id
        self.th = th

class ProofTermDeriv(ProofTerm):
    """Derivations.
    
    th -- statement of the theorem.
    rule -- proof method used to derive the theorem.
    args -- arguments to the proof method.
    prevs -- proof terms that the current one depends on.

    """
    def __init__(self, th, rule, args, prevs):
        self.ty = ProofTerm.DERIV
        self.th = th
        self.rule = rule
        self.args = args
        self.prevs = prevs
