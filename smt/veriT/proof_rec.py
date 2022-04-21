"""Proof reconstruction."""

from smt.veriT.proof_parser import decl_parser, proof_parser
from smt.veriT import command
from smt.veriT.verit_macro import NotOrMacro
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

    def validate(self, is_eval=True, has_bar=False):
        with alive_bar(len(self.steps), spinner=None, bar=None) as bar:
            for step in self.steps:
                if isinstance(step, command.Assume):
                    self.pts[step.id] = ProofTerm.assume(step.assm)
                    
                elif isinstance(step, command.Anchor):
                    self.add_subproof_context(step)
                else:
                    assert isinstance(step, command.Step)
                    rule_name = step.rule_name
                    macro_name = "verit_" + rule_name
                    prevs = self.to_pts(step.pm)
                    args = step.cl
                    if rule_name == "refl":
                        args += (step.cur_ctx,)
                    if rule_name in ("let", "bind"):
                        args += (self.ctx,)
                    if rule_name in ("la_generic", "forall_inst"):
                        args += step.args
                    if rule_name in ("resolution", "th_resolution"):
                        args = (step.cl, self.get_clause_sizes(step.pm))
                        macro_name = "verit_th_resolution"
                    if is_eval:
                        if rule_name == "bind":
                            self.pts[step.id] = ProofTerm.sorry(Thm([hyp for step_id in\
                                step.pm for hyp in self.pts[step_id].hyps], clause_to_disj(step.cl)))
                        else:
                            try:
                                self.pts[step.id] = ProofTerm(macro_name, args, prevs)
                            except AssertionError:
                                print(step.id, rule_name)
                                self.pts[step.id] = ProofTerm.sorry(Thm([hyp for step_id in\
                                    step.pm for hyp in self.pts[step_id].hyps], clause_to_disj(step.cl)))
                    else:
                        macro = theory.get_macro(macro_name)
                        try:
                            pt = macro.get_proof_term(args, prevs)
                            if macro_name == 'verit_th_resolution':
                                cl = args[0]
                            else:
                                cl = args
                            if pt.prop != Or(*cl):
                                print(macro_name)
                                print("Computed: ", pt.prop)
                                print("In proof: ", Or(*cl))
                                raise AssertionError("Unexpected returned theorem")
                        except NotImplementedError:
                            print(macro_name)
                            pt = ProofTerm(macro_name, args, prevs)
                        return pt
                bar()
        return self.pts[self.steps[-1].id]