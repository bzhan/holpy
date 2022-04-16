"""Proof reconstruction."""

from smt.veriT.proof_parser import decl_parser, proof_parser
from smt.veriT import command
from smt.veriT.verit_macro import NotOrMacro
from kernel.proofterm import ProofTerm
from kernel.thm import Thm
from kernel import term
from kernel import theory
from logic import logic

def bind_var(file_name):
    """Convert the declaration in context to higher-order types and terms."""
    ctx = dict()
    with open(file_name, "r") as f:
        for s in f.readlines():
            if s.strip().startswith("(declare-fun"):
                tm = decl_parser.parse(s.strip())
                ctx.update(tm)
    return ctx

def clause_to_disj(cls):
    return term.Or(*cls)

class ProofReconstruction:
    """Verit proof reconstruction.
    
    - steps: a list of parsed proof rules.
    """
    def __init__(self, steps) -> None:
        self.steps = steps

        # map from step id to proof term
        self.pts = dict()

    def to_pts(self, ids):
        """ids is a tuple of step name, return their corresponding pts."""
        return tuple([self.pts[i] for i in ids])

    def validate_step(self, macro_name, args, prevs=None, is_eval=True):
        if is_eval:
            return ProofTerm(macro_name, args, prevs)
        else:
            macro = theory.get_macro(macro_name)
            pt = macro.get_proof_term(args, prevs)
            return pt

    def validate(self, is_eval=True):
        for step in self.steps:
            if isinstance(step, command.Assume):
                self.pts[step.id] = ProofTerm.assume(step.assm)
                continue
            elif isinstance(step, command.Anchor):
                raise NotImplementedError
            assert isinstance(step, command.Step), type(step)
            rule_name = step.rule_name
            premises = self.to_pts(step.pm) # Collect the proof terms in premises
            if rule_name == "not_or":
                self.pts[step.id] = self.validate_step("verit_not_or", step.cl, premises, is_eval=is_eval)
            elif rule_name == "not_and":
                self.pts[step.id] = self.validate_step("verit_not_and", step.cl, premises, is_eval=is_eval)
            elif rule_name == "not_not":
                self.pts[step.id] = self.validate_step("verit_not_not", step.cl, is_eval=is_eval)
            elif rule_name in ("resolution", "th_resolution"): 
                # the difference between resolution and th-resolution rule 
                # is invisible on reconstruction
                self.pts[step.id] = self.validate_step("verit_th_resolution", step.cl, premises, is_eval=is_eval)
            elif rule_name == "implies":
                self.pts[step.id] = self.validate_step("verit_implies", step.cl, premises, is_eval=is_eval)
            elif rule_name == "and_pos":
                self.pts[step.id] = self.validate_step("verit_and_pos", step.cl, is_eval=is_eval)
            elif rule_name == "or_pos":
                self.pts[step.id] = self.validate_step("verit_or_pos", step.cl, is_eval=is_eval)
            elif rule_name == "or_neg":
                self.pts[step.id] = self.validate_step("verit_or_neg", step.cl, is_eval=is_eval)
            elif rule_name == "not_equiv1":
                self.pts[step.id] = self.validate_step("verit_not_equiv1", step.cl, premises, is_eval=is_eval)
            elif rule_name == "not_equiv2":
                self.pts[step.id] = self.validate_step("verit_not_equiv2", step.cl, premises, is_eval=is_eval)
            elif rule_name == "equiv1":
                self.pts[step.id] = self.validate_step("verit_equiv1", step.cl, premises, is_eval=is_eval)
            elif rule_name == "equiv2":
                self.pts[step.id] = self.validate_step("verit_equiv2", step.cl, premises, is_eval=is_eval)
            elif rule_name == "eq_reflexive":
                self.pts[step.id] = self.validate_step("verit_eq_reflexive", step.cl, is_eval=is_eval)
            elif rule_name == "eq_transitive":
                self.pts[step.id] = self.validate_step("verit_eq_transitive", step.cl, is_eval=is_eval)
            elif rule_name == "eq_congruent":
                self.pts[step.id] = self.validate_step("verit_eq_congurent", step.cl, is_eval=is_eval)
            elif rule_name == "equiv_pos1":
                self.pts[step.id] = self.validate_step("verit_equiv_pos1", step.cl, is_eval=is_eval)
            elif rule_name == "equiv_pos2":
                self.pts[step.id] = self.validate_step("verit_equiv_pos2", step.cl, is_eval=is_eval)
            # elif rule_name == "and_neg":
            #     self.pts[step.id] = self.validate_step("verit_and_neg", step.cl, is_eval=is_eval)
            else:
                print(rule_name)
                self.pts[step.id] = ProofTerm.sorry(Thm([hyp for step_id in\
                    step.pm for hyp in self.pts[step_id].hyps], clause_to_disj(step.cl)))
        
            if len(step.cl) > 0:
                assert self.pts[step.id].prop == term.Or(*step.cl)
            else:
                assert self.pts[step.id].prop == term.false

        return self.pts[self.steps[-1].id]