# Author: Bohua Zhan

from __future__ import annotations

from kernel.term import Term, Var, Inst
from kernel.type import TyInst
from kernel.thm import Thm, primitive_deriv
from kernel.proof import Proof, ItemID
from kernel.report import ProofReport
from kernel import theory
from util import typecheck


class TacticException(Exception):
    """Signals that a tactic is not applicable to the goal."""
    def __init__(self, err=""):
        self.err = err

    def __str__(self):
        return self.err


class ProofTerm():
    """A proof term contains the derivation tree of a theorem.
    
    Each proof term contains the following fields:
    
    - rule: name of the primitive derivation rule or macro.
    - args: arguments to the rule.
    - prevs: previous proof terms.
    - th: sequent proved by the proof term.
    - gaps: list of gaps (of type Thm) in the proof term.

    """
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
        if self.rule == 'sorry':
            self.gaps = [self.th]
        else:
            self.gaps = list(set(sum([prev.gaps for prev in self.prevs], [])))

        # Used for checking
        self.checked = False

    def __repr__(self):
        return str(self)

    def __str__(self):
        res = "ProofTerm(%s)" % self.th
        if self.gaps:
            res += '\nGaps: ' + '\n      '.join(str(gap) for gap in self.gaps)
        return res

    @property
    def hyps(self):
        """Hypothesis of a proof term."""
        return self.th.hyps

    @property
    def prop(self) -> Term:
        """Propositions of a proof term."""
        return self.th.prop

    @property
    def assums(self):
        """Assumptions of the proposition of a proof term."""
        return self.th.assums

    @property
    def concl(self) -> Term:
        """Conclusion of the proposition of a proof term."""
        return self.th.concl

    @property
    def lhs(self) -> Term:
        """Left side of the equality of a proof term."""
        return self.th.concl.lhs

    @property
    def rhs(self) -> Term:
        """Right side of the equality of a proof term."""
        return self.th.concl.rhs

    def is_equals(self) -> bool:
        return self.prop.is_equals()

    def is_reflexive(self) -> bool:
        return self.prop.is_reflexive()

    @staticmethod
    def atom(id, th):
        return ProofTerm('atom', id, [], th)

    @staticmethod
    def variable(nm, T):
        return ProofTerm("variable", (nm, T), [])

    @staticmethod
    def assume(A: Term) -> ProofTerm:
        return ProofTerm("assume", A, [])

    @staticmethod
    def reflexive(x: Term) -> ProofTerm:
        return ProofTerm("reflexive", x, [])

    def symmetric(self) -> ProofTerm:
        return ProofTerm("symmetric", None, [self])

    def transitive(self, *pts) -> ProofTerm:
        pt = self
        for eq_pt in pts:
            if pt.prop.is_reflexive():
                pt = eq_pt
            elif eq_pt.prop.is_reflexive():
                pass
            else:
                pt = ProofTerm("transitive", None, [pt, eq_pt])
        return pt

    def combination(self, pt2: ProofTerm) -> ProofTerm:
        return ProofTerm("combination", None, [self, pt2])

    def equal_intr(self, pt2: ProofTerm) -> ProofTerm:
        return ProofTerm("equal_intr", None, [self, pt2])

    def equal_elim(self, pt2: ProofTerm) -> ProofTerm:
        if self.is_reflexive():
            return pt2
        return ProofTerm("equal_elim", None, [self, pt2])

    def implies_intr(self, A: Term) -> ProofTerm:
        return ProofTerm("implies_intr", A, [self])

    def implies_elim(self, *pts) -> ProofTerm:
        pt = self
        for assum_pt in pts:
            pt = ProofTerm("implies_elim", None, [pt, assum_pt])
        return pt

    def subst_type(self, tyinst=None, **kwargs) -> ProofTerm:
        if tyinst is None:
            tyinst = TyInst(**kwargs)
        if tyinst:
            return ProofTerm("subst_type", tyinst, [self])
        else:
            return self

    def substitution(self, inst=None, **kwargs) -> ProofTerm:
        if inst is None:
            inst = Inst(**kwargs)
        if inst:
            return ProofTerm("substitution", inst, [self])
        else:
            return self

    @staticmethod
    def beta_conv(x: Term) -> ProofTerm:
        return ProofTerm("beta_conv", x, [])

    def abstraction(self, x: Term) -> ProofTerm:
        return ProofTerm("abstraction", x, [self])

    def forall_intr(self, x: Term) -> ProofTerm:
        return ProofTerm("forall_intr", x, [self])

    def forall_elim(self, s: Term) -> ProofTerm:
        return ProofTerm("forall_elim", s, [self])

    @staticmethod
    def theorem(th_name: str) -> ProofTerm:
        return ProofTerm("theorem", th_name, [])

    @staticmethod
    def sorry(th: Thm) -> ProofTerm:
        typecheck.checkinstance('sorry', th, Thm)
        return ProofTerm("sorry", None, [], th)

    def check(self, *, check_level=0, rpt=None):
        """Check the given proof term by expanding macros.
        
        Returns the proof report.
        
        """
        def rec(pt: ProofTerm):
            if pt.checked:
                return

            # First, check the prevs that self relies on.
            for prev in pt.prevs:
                rec(prev)

            if pt.rule == 'atom':
                raise AssertionError("check proofterm: atom")
            elif pt.rule == 'sorry':
                rpt.add_gap(pt.th)
            elif pt.rule == 'variable':
                pass
            elif pt.rule == 'theorem':
                rpt.apply_theorem(pt.args)
            elif pt.rule in primitive_deriv:
                rpt.apply_primitive_deriv()
            else:
                macro = theory.get_macro(pt.rule)
                if macro.level <= check_level:
                    rpt.eval_macro(pt.rule)
                else:
                    expand_pt = macro.get_proof_term(pt.args, pt.prevs)
                    rpt.expand_macro(pt.rule)
                    rec(expand_pt)

        rec(self)
        return

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
            eq_pt = cv.get_proof_term(pt.prop)
            pt = eq_pt.equal_elim(pt)
        return pt

    def on_arg(self, *cvs):
        """Apply the given conversion to the argument of the proposition."""
        pt = self
        for cv in cvs:
            eq_pt = cv.get_proof_term(pt.prop.arg)
            eq_pt = ProofTerm.reflexive(pt.prop.fun).combination(eq_pt)
            pt = eq_pt.equal_elim(pt)
        return pt

    def on_lhs(self, *cvs):
        """Apply the given expression to the lhs of the proposition."""
        assert self.prop.is_equals(), "on_lhs: theorem is not an equality."
        pt = self
        for cv in cvs:
            eq_pt = cv.get_proof_term(pt.prop.lhs)
            pt = eq_pt.symmetric().transitive(pt)
        return pt

    def on_rhs(self, *cvs):
        """Same as on_arg, except check the current theorem is an equality."""
        assert self.prop.is_equals(), "on_rhs: theorem is not an equality."
        pt = self
        for cv in cvs:
            eq_pt = cv.get_proof_term(pt.prop.rhs)
            pt = pt.transitive(eq_pt)
        return pt

    def tac(self, tac):
        """Apply the given tactic to the proof term. Return the new
        proof term.
        
        Each tactic is applied only to the subgoal. Use tac_all to apply a
        tactic to all subgoals.
        
        """
        if self.rule == 'sorry':
            return tac.get_proof_term(self.th)

        for i, prev in enumerate(self.prevs):
            if prev.gaps:
                new_prevs = self.prevs[:i] + [prev.tac(tac)] + self.prevs[i+1:]
                return ProofTerm(self.rule, self.args, prevs=new_prevs, th=self.th)

        raise TacticException('tac: no remaining subgoals')

    def tacs(self, *tacs):
        """Apply the given tactics in sequence."""
        pt = self
        for tac in tacs:
            pt = pt.tac(tac)
        return pt


def refl(t):
    return ProofTerm.reflexive(t)
