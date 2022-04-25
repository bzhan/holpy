"""Proof reconstruction."""

from smt.veriT.proof_parser import decl_parser, proof_parser
from smt.veriT import command
from smt.veriT.verit_macro import NotOrMacro
from smt.veriT import la_generic
from kernel.proofterm import ProofTerm
from kernel.thm import Thm
from kernel import term
from kernel.term import Or
from kernel import theory
from logic import logic
from alive_progress import alive_bar

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
        # List of steps
        self.steps = steps

        # Dictionary from step id to steps
        self.steps_dict = dict()
        for step in self.steps:
            self.steps_dict[step.id] = step

        # map from step id to proof term
        self.pts = dict()

        # map from step id to steps
        self.step_map = {step.id : step for step in self.steps}

        # # a list of contexts
        self.ctx = dict()

        # current subproof id
        self.subprf_id = None

    def to_pts(self, ids):
        """ids is a tuple of step name, return their corresponding pts."""
        return tuple(self.pts[i] for i in ids)

    def get_clause_sizes(self, ids):
        """Return the list of clause sizes, used in resolution."""
        return tuple(self.steps_dict[i].get_clause_size() for i in ids)

    def add_subproof_context(self, step):
        self.ctx = step.ctx
        self.subprf_id = step.id

    def find_local_assms(self, step_id):
        """Find all assumptions declared in step_id's subproof."""
        assms = []
        for step in self.steps:
            if step.id.startswith(step_id):
                sub_ids = step.id.split(".")
                if sub_ids[:-1] == step_id.split(".") and isinstance(step, command.Assume):
                    assms.append(self.pts[step.id])

        return tuple(assms)

    def find_last_subproof(self, step_id):
        size = len(step_id.split("."))
        for i in range(len(self.steps)-1):
            if self.steps[i+1].id == step_id:
                if not isinstance(self.steps[i+1], command.Anchor) and not isinstance(self.steps[i], command.Anchor):
                    return self.pts[self.steps[i].id]

    def validate_step(self, step, is_eval=True, omit_proofterm=None):
        if isinstance(step, command.Anchor):
            return
        if isinstance(step, command.Assume):
            self.pts[step.id] = ProofTerm.assume(step.assm)
        else:
            assert isinstance(step, command.Step)
            rule_name = step.rule_name
            # print(rule_name)
            macro_name = "verit_" + rule_name
            prevs = self.to_pts(step.pm)
            args = step.cl
            if rule_name == "refl":
                args += (step.cur_ctx,)
            if rule_name == "let":
                last_prf = self.find_last_subproof(step.id)
                prevs += (last_prf,)
            if rule_name in ("bind", "sko_ex", "sko_forall", "onepoint"):
                args += (step.cur_ctx,)
                last_prf = self.find_last_subproof(step.id)
                prevs += (last_prf,)
            if rule_name in ("la_generic", "forall_inst"):
                args += step.args
            if rule_name == "subproof":
                sub_assms = self.find_local_assms(step.id)
                last_prf = self.find_last_subproof(step.id)
                prevs += sub_assms
                prevs += (last_prf,)
            if rule_name in ("resolution", "th_resolution"):
                args = (step.cl, self.get_clause_sizes(step.pm))
                macro_name = "verit_th_resolution"
            if is_eval:
                self.pts[step.id] = ProofTerm(macro_name, args, prevs)
            elif omit_proofterm and macro_name in omit_proofterm:
                self.pts[step.id] = ProofTerm(macro_name, args, prevs)
            else:
                macro = theory.get_macro(macro_name)
                try:
                    pt = macro.get_proof_term(args, prevs)
                    if rule_name in ('resolution', 'th_resolution'):
                        cl = args[0]
                    elif rule_name in ('refl',):
                        cl = args[:-1]
                    else:
                        cl = args
                    if not isinstance(pt, ProofTerm):
                        print(macro_name)
                        print("Returned: ", pt)
                        raise AssertionError("Unexpected type of returned result")
                    if pt.prop != Or(*cl):
                        print(macro_name)
                        print("Computed: ", pt.prop)
                        print("In proof: ", Or(*cl))
                        raise AssertionError("Unexpected returned theorem")
                    else:
                        self.pts[step.id] = pt
                except NotImplementedError as e:
                    print(step.id, rule_name)
                    self.pts[step.id] = ProofTerm.sorry(
                        Thm(clause_to_disj(step.cl), *(self.pts[step_id].hyps for step_id in step.pm)))

    def validate(self, is_eval=True, step_limit=None, omit_proofterm=None):
        with alive_bar(len(self.steps), spinner=None, bar=None) as bar:
            for i, step in enumerate(self.steps):
                self.validate_step(step, is_eval=is_eval, omit_proofterm=omit_proofterm)
                bar()
                if step_limit and i > step_limit:
                    break
        return self.pts[step.id]
