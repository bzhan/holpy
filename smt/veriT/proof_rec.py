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

        # map from step id to steps
        self.step_map = {step.id : step for step in self.steps}

        # # a list of contexts
        self.ctx = dict()

    def to_pts(self, ids):
        """ids is a tuple of step name, return their corresponding pts."""
        return tuple([self.pts[i] for i in ids])

    def validate_step(self, macro_name, args, prevs=None, is_eval=True, is_refl=False):
        if is_refl:
            args = args + (self.ctx,)
        if is_eval:
            return ProofTerm(macro_name, args, prevs)
        else:
            macro = theory.get_macro(macro_name)
            pt = macro.get_proof_term(args, prevs)
            return pt

    def add_subproof_context(self, step):
        self.ctx = step.ctx

    def validate(self, is_eval=True):
        for step in self.steps:
            if isinstance(step, command.Assume):
                self.pts[step.id] = ProofTerm.assume(step.assm)
                continue
            elif isinstance(step, command.Anchor):
                self.add_subproof_context(step)
                continue
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
                try:
                    self.pts[step.id] = self.validate_step("verit_th_resolution", step.cl, premises, is_eval=is_eval)
                except:
                    self.pts[step.id] = ProofTerm.sorry(Thm([hyp for step_id in\
                    step.pm for hyp in self.pts[step_id].hyps], clause_to_disj(step.cl)))
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
            elif rule_name == "distinct_elim":
                self.pts[step.id] = self.validate_step("verit_distinct_elim", step.cl, is_eval=is_eval)
            elif rule_name == "and":
                self.pts[step.id] = self.validate_step("verit_and", step.cl, premises, is_eval=is_eval)  
            elif rule_name == "bfun_elim":
                self.pts[step.id] = self.validate_step("verit_bfun_elim", step.cl, premises, is_eval=is_eval)  
            elif rule_name == "ite_intro":
                self.pts[step.id] = self.validate_step("verit_ite_intro", step.cl, is_eval=is_eval)
            elif rule_name == "ite1":
                self.pts[step.id] = self.validate_step("verit_ite1", step.cl, premises, is_eval=is_eval)
            elif rule_name == "ite2":
                self.pts[step.id] = self.validate_step("verit_ite2", step.cl, premises, is_eval=is_eval)
            elif rule_name == "and_neg":
                self.pts[step.id] = self.validate_step("verit_and_neg", step.cl, is_eval=is_eval)
            elif rule_name == "contraction":
                self.pts[step.id] = self.validate_step("verit_contraction", step.cl, premises, is_eval=is_eval)
            elif rule_name == "or":
                self.pts[step.id] = self.validate_step("verit_or", step.cl, premises, is_eval=is_eval)
            elif rule_name == "false":
                self.pts[step.id] = self.validate_step("verit_false", step.cl, is_eval=is_eval)
            elif rule_name == "not_simplify":
                self.pts[step.id] = self.validate_step("verit_not_simplify", step.cl, is_eval=is_eval)
            elif rule_name == "eq_simplify":
                self.pts[step.id] = self.validate_step("verit_eq_simplify", step.cl, is_eval=is_eval)
            elif rule_name == "trans":
                self.pts[step.id] = self.validate_step("verit_trans", step.cl, premises, is_eval=is_eval)
            # elif rule_name == "let":
            #     self.pts[step.id] = self.validate_step("verit_let", step.cl, premises, is_eval=is_eval)
            elif rule_name == "cong":
                try:
                    self.pts[step.id] = self.validate_step("verit_cong", step.cl, premises, is_eval=is_eval)
                except:
                    self.pts[step.id] = ProofTerm.sorry(Thm([hyp for step_id in\
                    step.pm for hyp in self.pts[step_id].hyps], clause_to_disj(step.cl)))
            elif rule_name == "refl":
                self.pts[step.id] = self.validate_step("verit_refl", step.cl, is_eval=is_eval, is_refl=True)
            elif rule_name == "eq_congruent_pred":
                self.pts[step.id] = self.validate_step("verit_eq_congurent_pred", step.cl, is_eval=is_eval)
            elif rule_name == "ac_simp":
                try:
                    self.pts[step.id] = self.validate_step("verit_ac_simp", step.cl, is_eval=is_eval)
                except:
                    self.pts[step.id] = ProofTerm.sorry(Thm([hyp for step_id in\
                    step.pm for hyp in self.pts[step_id].hyps], clause_to_disj(step.cl)))
            else:
                print(rule_name)
                self.pts[step.id] = ProofTerm.sorry(Thm([hyp for step_id in\
                    step.pm for hyp in self.pts[step_id].hyps], clause_to_disj(step.cl)))

        return self.pts[self.steps[-1].id]