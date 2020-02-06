# Author: Bohua Zhan

from kernel.term import Term, Var, Inst
from kernel.thm import Thm, primitive_deriv
from kernel.proof import Proof, ItemID
from kernel import theory
from util import typecheck


class ProofTerm():
    """A proof term contains the derivation tree of a theorem."""
    def __init__(self, rule, args, prevs=None, th=None):
        typecheck.checkinstance('ProofTerm', rule, str)

        self.rule = rule
        if prevs is None:
            prevs = []
        prev_ths = [prev.th for prev in prevs]
        if rule == 'atom':
            assert th is not None, "ProofTerm: must provide th for atom."
            self.th = th
        elif rule == 'sorry':
            assert th is not None, "ProofTerm: must provide th for sorry."
            self.th = th
        elif rule == 'variable':
            nm, T = args
            self.th = Thm.mk_VAR(Var(nm, T))
        elif rule == 'theorem':
            self.th = theory.get_theorem(args)
        elif rule in primitive_deriv:
            rule_fun, _ = primitive_deriv[rule]
            self.th = rule_fun(*prev_ths) if args is None else rule_fun(args, *prev_ths)
        else:
            macro = theory.get_macro(rule)
            if th is None:
                self.th = macro.eval(args, prev_ths)
            else:
                self.th = th
        self.args = args
        self.prevs = prevs

    def __repr__(self):
        return str(self)

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
        return ProofTerm('atom', id, [], th)

    @staticmethod
    def variable(nm, T):
        return ProofTerm("variable", (nm, T), [])

    @staticmethod
    def assume(A):
        return ProofTerm("assume", A, [])

    @staticmethod
    def reflexive(x):
        return ProofTerm("reflexive", x, [])

    def symmetric(self):
        return ProofTerm("symmetric", None, [self])

    def transitive(self, *pts):
        pt = self
        for eq_pt in pts:
            if pt.prop.is_reflexive():
                pt = eq_pt
            elif eq_pt.prop.is_reflexive():
                pass
            else:
                pt = ProofTerm("transitive", None, [pt, eq_pt])
        return pt

    def combination(self, pt2):
        return ProofTerm("combination", None, [self, pt2])

    def equal_elim(self, pt2):
        return ProofTerm("equal_elim", None, [self, pt2])

    def implies_intr(self, A):
        return ProofTerm("implies_intr", A, [self])

    def implies_elim(self, *pts):
        pt = self
        for assum_pt in pts:
            pt = ProofTerm("implies_elim", None, [pt, assum_pt])
        return pt

    def subst_type(self, tyinst=None, **kwargs):
        if tyinst is None:
            tyinst = TyInst(**kwargs)
        if tyinst:
            return ProofTerm("subst_type", tyinst, [self])
        else:
            return self

    def substitution(self, inst=None, **kwargs):
        if inst is None:
            inst = Inst(**kwargs)
        if inst:
            return ProofTerm("substitution", inst, [self])
        else:
            return self

    @staticmethod
    def beta_conv(x):
        return ProofTerm("beta_conv", x, [])

    def abstraction(self, x):
        return ProofTerm("abstraction", x, [self])

    def forall_intr(self, x):
        return ProofTerm("forall_intr", x, [self])

    def forall_elim(self, s):
        return ProofTerm("forall_elim", s, [self])

    @staticmethod
    def theorem(th_name):
        return ProofTerm("theorem", th_name, [])

    @staticmethod
    def sorry(th):
        typecheck.checkinstance('sorry', th, Thm)
        return ProofTerm("sorry", None, [], th)

    def get_gaps(self):
        """Return list of gaps of the proof term. Return value is
        a list of Thm objects.

        """
        res = set()
        def search(pt):
            if pt.rule == 'sorry':
                res.add(pt.th)
            else:
                for prev in pt.prevs:
                    search(prev)

        search(self)
        return list(res)

    def export(self, prefix=None, prf=None, subproof=True):
        """Convert to proof object."""

        def rec(pt):
            # Should not call _export when self is already in seq_to_id
            assert pt.th not in seq_to_id, "export: th already found."

            # Should be called only on derivations
            assert pt.rule != 'atom', "export: atom"

            ids = []
            for prev in pt.prevs:
                if prev.rule == 'atom':
                    ids.append(prev.args)
                elif prev.th in seq_to_id:
                    ids.append(seq_to_id[prev.th])
                else:
                    rec(prev)
                    ids.append(prf.items[-1].id)
            
            if subproof:
                id = ItemID(prefix.id + (len(prf.items),))
            else:
                id = ItemID(prefix.id[:-1] + (prefix.id[-1] + len(prf.items),))

            seq_to_id[pt.th] = id
            prf.add_item(id, pt.rule, args=pt.args, prevs=ids, th=pt.th)

        # Current id prefix. Used in generating ids.
        if prefix is None:
            prefix = ItemID()

        # The currently built proof. Updated by the function.
        if prf is None:
            prf = Proof()

        # Mapping from existing sequents to ids.
        seq_to_id = dict()
        rec(self)
        return prf

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
