# Author: Bohua Zhan

from kernel.term import Term, Var
from kernel.thm import Thm, primitive_deriv
from kernel import theory
from kernel.proof import Proof, ItemID
from kernel.macro import ProofMacro, get_macro
from util import typecheck


class ProofTerm():
    """A proof term contains the derivation tree of a theorem.

    There are two kinds of proof terms: atoms and derivations.

    ProofTermAtom(id, th): existing theorem with the given id and statement.

    ProofTermDeriv(th, rule, args, prevs): one derivation step.
    
    """
    ATOM, DERIV = range(2)

    @property
    def hyps(self):
        return self.th.hyps

    @property
    def prop(self):
        return self.th.prop

    @property
    def assums(self):
        return self.th.assums

    @property
    def concl(self):
        return self.th.concl

    @property
    def lhs(self):
        return self.th.prop.lhs

    @property
    def rhs(self):
        return self.th.prop.rhs

    @staticmethod
    def atom(id, th):
        return ProofTermAtom(id, th)

    @staticmethod
    def variable(nm, T):
        return ProofTermDeriv("variable", (nm, T), [])

    @staticmethod
    def assume(A):
        return ProofTermDeriv("assume", A, [])

    @staticmethod
    def reflexive(x):
        return ProofTermDeriv("reflexive", x, [])

    @staticmethod
    def symmetric(pt):
        return ProofTermDeriv("symmetric", None, [pt])

    @staticmethod
    def transitive(pt1, pt2):
        if pt1.prop.is_reflexive():
            return pt2
        if pt2.prop.is_reflexive():
            return pt1
        return ProofTermDeriv("transitive", None, [pt1, pt2])

    @staticmethod
    def combination(pt1, pt2):
        return ProofTermDeriv("combination", None, [pt1, pt2])

    @staticmethod
    def equal_elim(pt1, pt2):
        return ProofTermDeriv("equal_elim", None, [pt1, pt2])

    @staticmethod
    def implies_intr(A, pt):
        return ProofTermDeriv("implies_intr", A, [pt])

    @staticmethod
    def implies_elim(pt1, *pts):
        if len(pts) == 0:
            return pt1
        else:
            pt2 = ProofTermDeriv("implies_elim", None, [pt1, pts[0]])
            return ProofTerm.implies_elim(pt2, *pts[1:])

    @staticmethod
    def subst_type(tyinst, pt):
        return ProofTermDeriv("subst_type", tyinst, [pt])

    @staticmethod
    def substitution(inst, pt):
        return ProofTermDeriv("substitution", inst, [pt])

    @staticmethod
    def beta_conv(x):
        return ProofTermDeriv("beta_conv", x, [])

    @staticmethod
    def abstraction(pt, x):
        return ProofTermDeriv("abstraction", x, [pt])

    @staticmethod
    def forall_intr(x, pt):
        return ProofTermDeriv("forall_intr", x, [pt])

    @staticmethod
    def forall_elim(s, pt):
        return ProofTermDeriv("forall_elim", s, [pt])

    @staticmethod
    def theorem(th_name):
        return ProofTermDeriv("theorem", th_name, [])

    @staticmethod
    def sorry(th):
        typecheck.checkinstance('sorry', th, Thm)
        return ProofTermDeriv("sorry", None, [], th=th)

    def get_gaps(self):
        """Return list of gaps of the proof term. Return value is
        a list of Thm objects.

        """
        res = set()
        def search(pt):
            if pt.ty == ProofTerm.ATOM:
                return
            if pt.rule == 'sorry':
                res.add(pt.th)
            else:
                for prev in pt.prevs:
                    search(prev)

        search(self)
        return list(res)

    def _export(self, prefix, seq_to_id, prf, subproof):
        """Helper function for _export.
        
        prefix -- current id prefix. Used in generating ids.

        seq_to_id -- the dictionary from existing sequents to ids. This
        is updated by the function.

        prf -- the currently built proof. Updated by the function.

        subproof -- whether to start a subproof or continue the prefix.

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
                    prev._export(prefix, seq_to_id, prf, subproof)
                    ids.append(prf.items[-1].id)
            else:
                raise TypeError
        
        if subproof:
            id = ItemID(prefix.id + (len(prf.items),))
        else:
            id = ItemID(prefix.id[:-1] + (prefix.id[-1] + len(prf.items),))

        seq_to_id[self.th] = id
        if self.rule == 'sorry':
            prf.add_item(id, self.rule, args=self.args, prevs=ids, th=self.th)
        else:
            prf.add_item(id, self.rule, args=self.args, prevs=ids)
        return prf

    def export(self, prefix=None, prf=None, subproof=True):
        """Convert to proof object."""
        if prefix is None:
            prefix = ItemID()
        if prf is None:
            prf = Proof()
        return self._export(prefix, dict(), prf, subproof)

    def on_prop(self, *cvs):
        """Apply the given conversion to the proposition."""
        pt = self
        for cv in cvs:
            pt = cv.apply_to_pt(pt)
        return pt

    def on_arg(self, *cvs):
        """Apply the given conversion to the argument of the proposition."""
        pt = self
        for cv in cvs:
            pt = cv.apply_to_pt(pt, pos="arg")
        return pt

    def on_lhs(self, *cvs):
        """Apply the given expression to the lhs of the proposition."""
        assert self.prop.is_equals(), "on_lhs: theorem is not an equality."
        pt = self
        for cv in cvs:
            pt = cv.apply_to_pt(pt, pos="lhs")
        return pt

    def on_rhs(self, *cvs):
        """Same as on_arg, except check the current theorem is an equality."""
        assert self.prop.is_equals(), "on_rhs: theorem is not an equality."
        pt = self
        for cv in cvs:
            pt = cv.apply_to_pt(pt, pos="rhs")
        return pt

    def on_assums(self, *cvs):
        """Apply the given conversion to the assumptions."""
        pt = self
        for cv in cvs:
            pt = cv.apply_to_pt(pt, pos="assums")
        return pt

def refl(t):
    return ProofTerm.reflexive(t)

class ProofTermAtom(ProofTerm):
    """Atom proof terms."""
    def __init__(self, id, th):
        typecheck.checkinstance('ProofTermAtom', th, Thm)
        self.ty = ProofTerm.ATOM
        self.id = ItemID(id)
        self.th = th

class ProofTermDeriv(ProofTerm):
    """Derivations.
    
    rule -- proof method used to derive the theorem.
    args -- arguments to the proof method.
    prevs -- proof terms that the current one depends on.

    """
    def __init__(self, rule, args, prevs=None, th=None):
        typecheck.checkinstance('ProofTermDeriv', rule, str)

        self.ty = ProofTerm.DERIV
        self.rule = rule
        if prevs is None:
            prevs = []
        prev_ths = [prev.th for prev in prevs]
        if rule == 'sorry':
            assert th is not None, "ProofTermDeriv: must provide th for sorry."
            self.th = th
        elif rule == 'variable':
            nm, T = args
            self.th = Thm.mk_VAR(Var(nm, T))
        elif rule == 'theorem':
            self.th = theory.thy.get_theorem(args, svar=True)
        elif rule in primitive_deriv:
            rule_fun, _ = primitive_deriv[rule]
            self.th = rule_fun(*prev_ths) if args is None else rule_fun(args, *prev_ths)
        else:
            macro = get_macro(rule)
            if th is None:
                self.th = macro.eval(args, prev_ths)
            else:
                self.th = th
        self.args = args
        self.prevs = prevs

class ProofTermMacro(ProofMacro):
    """Encapsulates a standard way for writing macros: by first
    constructing a proof term, then export the proof term.

    """
    def eval(self, args, prevs):
        pts = [ProofTerm.sorry(prev) for prev in prevs]
        return self.get_proof_term(args, pts).th

    def get_proof_term(self, args, prevs):
        raise NotImplementedError

    def expand(self, prefix, args, prevs):
        pts = tuple([ProofTerm.atom(id, prev) for id, prev in prevs])
        return self.get_proof_term(args, pts).export(prefix)
