# Author: Bohua Zhan

from kernel.thm import Thm, primitive_deriv
from kernel.theory import Theory
from kernel.proof import Proof, id_force_tuple
from kernel.macro import ProofMacro, MacroSig

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

    @staticmethod
    def atom(id, th):
        return ProofTermAtom(id, th)

    @staticmethod
    def assume(A):
        return ProofTermDeriv("assume", None, A, [])

    @staticmethod
    def reflexive(x):
        return ProofTermDeriv("reflexive", None, x, [])

    @staticmethod
    def symmetric(pt):
        return ProofTermDeriv("symmetric", None, None, [pt])

    @staticmethod
    def transitive(pt1, pt2):
        return ProofTermDeriv("transitive", None, None, [pt1, pt2])

    @staticmethod
    def combination(pt1, pt2):
        return ProofTermDeriv("combination", None, None, [pt1, pt2])

    @staticmethod
    def equal_elim(pt1, pt2):
        return ProofTermDeriv("equal_elim", None, None, [pt1, pt2])

    @staticmethod
    def arg_combination(thy, f, pt):
        """Given x = y and term f, return f x = f y."""
        return ProofTermDeriv("arg_combination", thy, f, [pt])

    @staticmethod
    def fun_combination(thy, x, pt):
        """Given f = g and term x, return f x = g x."""
        return ProofTermDeriv("fun_combination", thy, x, [pt])

    @staticmethod
    def implies_intr(A, pt):
        return ProofTermDeriv("implies_intr", None, A, [pt])

    @staticmethod
    def implies_elim(pt1, *pts):
        if len(pts) == 0:
            return pt1
        else:
            pt2 = ProofTermDeriv("implies_elim", None, None, [pt1, pts[0]])
            return ProofTerm.implies_elim(pt2, *pts[1:])

    @staticmethod
    def subst_type(tyinst, pt):
        return ProofTermDeriv("subst_type", None, tyinst, [pt])

    @staticmethod
    def substitution(inst, pt):
        return ProofTermDeriv("substitution", None, inst, [pt])

    @staticmethod
    def beta_conv(x):
        return ProofTermDeriv("beta_conv", None, x, [])

    @staticmethod
    def abstraction(pt, x):
        return ProofTermDeriv("abstraction", None, x, [pt])

    @staticmethod
    def theorem(thy, th_name):
        return ProofTermDeriv("theorem", thy, th_name, [])

    def _export(self, prefix, seq_to_id, prf):
        """Helper function for _export.
        
        prefix -- current id prefix. Used in generating ids.

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
                    prev._export(prefix, seq_to_id, prf)
                    ids.append(prf.items[-1].id)
            else:
                raise TypeError()
        
        id = prefix + (len(prf.items),)
        seq_to_id[self.th] = id
        prf.add_item(id, self.rule, args=self.args, prevs=ids)
        return prf

    def export(self, prefix=None, prf=None):
        """Convert to proof object."""
        if prefix is None:
            prefix = tuple()
        if prf is None:
            prf = Proof()
        return self._export(prefix, dict(), prf)

    def on_prop(self, thy, *cvs):
        """Apply the given conversion to the proposition."""
        assert isinstance(thy, Theory), "on_prop: first argument must be Theory object."
        pt = self
        for cv in cvs:
            pt = cv.apply_to_pt(thy, pt)
        return pt

    def on_arg(self, thy, *cvs):
        """Apply the given conversion to the argument of the proposition."""
        assert isinstance(thy, Theory), "on_prop: first argument must be Theory object."
        pt = self
        for cv in cvs:
            pt = cv.apply_to_pt(thy, pt, pos="arg")
        return pt

    def on_rhs(self, thy, *cvs):
        """Same as on_arg, except check the current theorem is an equality."""
        assert isinstance(thy, Theory), "on_prop: first argument must be Theory object."
        assert self.prop.is_equals(), "on_rhs: theorem is not an equality."
        return self.on_arg(thy, *cvs)

    def on_assums(self, thy, *cvs):
        """Apply the given conversion to the assumptions."""
        assert isinstance(thy, Theory), "on_prop: first argument must be Theory object."
        pt = self
        for cv in cvs:
            pt = cv.apply_to_pt(thy, pt, pos="assums")
        return pt

def refl(t):
    return ProofTerm.reflexive(t)

class ProofTermAtom(ProofTerm):
    """Atom proof terms."""
    def __init__(self, id, th):
        self.ty = ProofTerm.ATOM
        self.id = id_force_tuple(id)
        self.th = th

class ProofTermDeriv(ProofTerm):
    """Derivations.
    
    rule -- proof method used to derive the theorem.
    thy -- current theory.
    args -- arguments to the proof method.
    prevs -- proof terms that the current one depends on.

    """
    def __init__(self, rule, thy, args, prevs):
        self.ty = ProofTerm.DERIV
        self.rule = rule
        prev_ths = [prev.th for prev in prevs]
        if rule == 'theorem':
            self.th = thy.get_theorem(args)
        elif rule in primitive_deriv:
            rule_fun, _ = primitive_deriv[rule]
            self.th = rule_fun(*prev_ths) if args is None else rule_fun(args, *prev_ths)
        else:
            macro = thy.get_proof_macro(rule)
            self.th = macro(thy, args, prev_ths)
        self.args = args
        self.prevs = prevs

class ProofTermMacro(ProofMacro):
    """Encapsulates a standard way for writing macros: by first
    constructing a proof term, then export the proof term.

    """
    def __call__(self, thy, args, prevs):
        pts = [ProofTerm.assume(prev) for prev in prevs]
        return self.get_proof_term(thy, args, pts).th

    def get_proof_term(self, thy, args, prevs):
        raise NotImplementedError()

    def expand(self, prefix, thy, args, prevs):
        pts = tuple([ProofTerm.atom(id, prev) for id, prev in prevs])
        return self.get_proof_term(thy, args, pts).export(prefix)
