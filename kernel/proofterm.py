# Author: Bohua Zhan

from kernel.term import Term, Var, Inst
from kernel.thm import Thm, primitive_deriv
from kernel.proof import Proof, ItemID
from util import typecheck


class ProofTerm():
    """A proof term contains the derivation tree of a theorem.

    There are two kinds of proof terms: atoms and derivations.

    ProofTermAtom(id, th): existing theorem with the given id and statement.

    ProofTermDeriv(th, rule, args, prevs): one derivation step.
    
    """
    ATOM, DERIV = range(2)

    def __str__(self):
        return "ProofTerm(%s)" % self.th

    @property
    def hyps(self):
        """Hypothesis of a proof term."""
        return self.th.hyps

    @property
    def prop(self):
        """Propositions of a proof term."""
        return self.th.prop

    @property
    def assums(self):
        """Assumptions of the proposition of a proof term."""
        return self.th.assums

    @property
    def concl(self):
        """Conclusion of the proposition of a proof term."""
        return self.th.concl

    @property
    def lhs(self):
        """Left side of the equality of a proof term."""
        return self.th.concl.lhs

    @property
    def rhs(self):
        """Right side of the equality of a proof term."""
        return self.th.concl.rhs

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

    def symmetric(self):
        return ProofTermDeriv("symmetric", None, [self])

    def transitive(self, *pts):
        pt = self
        for eq_pt in pts:
            if pt.prop.is_reflexive():
                pt = eq_pt
            elif eq_pt.prop.is_reflexive():
                pass
            else:
                pt = ProofTermDeriv("transitive", None, [pt, eq_pt])
        return pt

    def combination(self, pt2):
        return ProofTermDeriv("combination", None, [self, pt2])

    def equal_elim(self, pt2):
        return ProofTermDeriv("equal_elim", None, [self, pt2])

    def implies_intr(self, A):
        return ProofTermDeriv("implies_intr", A, [self])

    def implies_elim(self, *pts):
        pt = self
        for assum_pt in pts:
            pt = ProofTermDeriv("implies_elim", None, [pt, assum_pt])
        return pt

    def subst_type(self, tyinst=None, **kwargs):
        if tyinst is None:
            tyinst = TyInst(**kwargs)
        if tyinst:
            return ProofTermDeriv("subst_type", tyinst, [self])
        else:
            return self

    def substitution(self, inst=None, **kwargs):
        if inst is None:
            inst = Inst(**kwargs)
        if inst:
            return ProofTermDeriv("substitution", inst, [self])
        else:
            return self

    @staticmethod
    def beta_conv(x):
        return ProofTermDeriv("beta_conv", x, [])

    def abstraction(self, x):
        return ProofTermDeriv("abstraction", x, [self])

    def forall_intr(self, x):
        return ProofTermDeriv("forall_intr", x, [self])

    def forall_elim(self, s):
        return ProofTermDeriv("forall_elim", s, [self])

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
            from kernel import theory
            self.th = theory.get_theorem(args)
        elif rule in primitive_deriv:
            rule_fun, _ = primitive_deriv[rule]
            self.th = rule_fun(*prev_ths) if args is None else rule_fun(args, *prev_ths)
        else:
            from kernel.macro import get_macro
            macro = get_macro(rule)
            if th is None:
                self.th = macro.eval(args, prev_ths)
            else:
                self.th = th
        self.args = args
        self.prevs = prevs
